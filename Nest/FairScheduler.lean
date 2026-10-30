import Nest.NetworkLiveness

/-!
# FairScheduler: round-robin drain scheduler feeding output-liveness arguments.

**Design.** Fix the role order `round_robin_roles Ni` once. Cycle forever; at role `r`'s
turn: (1) drain — fire `r`-dequeues until quiescent (each firing drops the
queue length by exactly one, so the drain is finite); (2) send — fire one
`r`-send (`τ_comm r q …`) if possible. Tie-breaking within drain/send is
arbitrary (first-match rules make it computable — no choice axioms needed).

**Fairness: every INFINITE run produced is fair**
(`IsFair`, `Nest.NetworkLiveness`), but the design does NOT guarantee infinite
production — tie-breaking may steer into killing branches, so guaranteeing
an infinite run needs non-killing selection. See `rr_deq_clause` /
`rr_comm_clause` (fairness obligations).

**Properties.**
- Granularity: roles; order: fixed round-robin.
- Machinery: drain-fuel + scan/type preservation, all elementary.
- Choice: computable first-match rules suffice — no choice axioms needed.
- Fairness argument: serve-at-own-turn + capability-preserved-until-turn
  (`IsFair`, `Nest.NetworkLiveness`).
- Production: may stall at stuck / steer into killing branches — e.g. an
  internal-choice send picking a dead-end branch — so infinite production is
  NOT guaranteed; guaranteeing it needs non-killing selection.
- Output dichotomy: every RR-drain run is fair-infinite or finite-maximal
  (each turn is finite; either infinitely many firings occur — then the
  infinite run is fair by the above — or firing stops, in which case drain
  quiescence + skipped sends mean no internal step exists, i.e. stuck).
  Both disjuncts have a verdict in the `IsOutputLiveNetwork` architecture
  (infinite via fairness, maximal via stuckness + orphans) — but `hSched`
  needs specifically the infinite one, which is where killing branches bite.

This file provides the scheduler used by the drain-failure ⇒ non-liveness
argument (`DrainNonLiveness`): fair-path production (`toFairPath`) and the
finite-maximal stuck alternative (`turn_run_stuck`).
-/

/-- Cycling order: the network's roles, fixed once (role sets are static
    under `replace`). -/
def round_robin_roles (N : Network) : List Role := (N.map Prod.fst).eraseDups

/-- Quiescence of role `r`: no dequeue step fires at `r`'s entry. -/
def rr_quiescent (N : Network) (r : Role) : Prop :=
  ∀ (T : SessionType) (Q : Queue) (p : Role) (lab : Lab) (S : DataSort)
    (T' : SessionType) (Q' : Queue),
    (r, (T, Q)) ∈ N → ¬ sq_trans (T, Q) (sq_action.dequeue p lab S) (T', Q')

/-- Drain star: finitely many `r`-dequeue network steps
    (`net_trans_star` alone does not record labels, so this is its own inductive). -/
inductive rr_drain_star : Network → Network → Role → Prop where
  | refl (N r) : rr_drain_star N N r
  | step (N1 N2 N3 r p lab S)
      (h : net_trans N1 (net_label.τ_dequeue r p lab S) N2)
      (hTail : rr_drain_star N2 N3 r) : rr_drain_star N1 N3 r

/-- A successful dequeue scan persists under end-appends (other roles only
    append to `r`'s queue between `r`-turns; the pre-match region is
    untouched, so the first match is unchanged — in fact the result appends).
    By induction on the traversed prefix, via `Queue.dequeue.go`. -/
private lemma rr_scan_append {seen left R : Queue} {msg : QueueMessage} {Q' : Queue}
    (h : Queue.dequeue.go seen left msg = some Q') :
    Queue.dequeue.go seen (left ++ R) msg = some (Q' ++ R) := by
  induction left generalizing seen Q' with
  | nil => simp [Queue.dequeue.go] at h
  | cons m rest ih =>
    by_cases hm : m = msg
    · subst hm
      simp [List.cons_append, Queue.dequeue.go] at h ⊢
      subst h
      simp [List.append_assoc]
    · have hm_ne : m ≠ msg := hm
      by_cases hs : m.1 = msg.1
      · simp only [List.cons_append, Queue.dequeue.go] at h ⊢
        rw [if_neg hm_ne, if_pos hs] at h
        cases h
      · simp only [List.cons_append, Queue.dequeue.go] at h ⊢
        rw [if_neg hm_ne, if_neg hs] at h ⊢
        exact ih h

/-- Other roles' dequeues leave `r`'s entry untouched (only the dequeuer's
    entry is replaced). Via `mem_replace_other` / `network_mem_unique`. -/
private lemma rr_entry_untouched_deq {N N' : Network} {r s : Role} {p : Role}
    {lab : Lab} {S : DataSort} (hne : s ≠ r)
    (hTr : net_trans N (net_label.τ_dequeue s p lab S) N') :
    ∀ stq, (r, stq) ∈ N → (r, stq) ∈ N' := by
  intro stq hmem0
  cases hTr with
  | dequeue _ _ =>
    unfold Network.replace
    simp only [List.mem_cons, List.mem_filter]
    refine Or.inr ⟨hmem0, ?_⟩
    exact bne_iff_ne.mpr hne.symm

/-- Third-party comms leave `r`'s entry untouched. -/
private lemma rr_entry_untouched_comm {N N' : Network} {r s q : Role}
    {lab : Lab} {S : DataSort} (hnes : s ≠ r) (hneqr : q ≠ r)
    (hTr : net_trans N (net_label.τ_comm s q lab S) N') :
    ∀ stq, (r, stq) ∈ N → (r, stq) ∈ N' := by
  intro stq hmem0
  cases hTr with
  | comm _ _ _ _ =>
    unfold Network.replace
    simp only [List.mem_cons, List.mem_filter]
    refine Or.inr ⟨Or.inr ⟨hmem0, ?_⟩, ?_⟩
    · exact bne_iff_ne.mpr hnes.symm
    · exact bne_iff_ne.mpr hneqr.symm

/-- Receives append only: `r`'s type is unchanged when `r` receives
    (only its queue grows, at the end — feeding `rr_scan_append`).
    Needs well-formedness (role uniqueness identifies the receiver entry). -/
private lemma rr_type_untouched_recv {N N' : Network} {r s : Role}
    {lab : Lab} {S : DataSort} (hWF : N.WellFormed)
    (hTr : net_trans N (net_label.τ_comm s r lab S) N') :
    ∀ (T : SessionType) (Q : Queue), (r, (T, Q)) ∈ N →
      (r, (T, Q ++ [QueueMessage.msg s lab S])) ∈ N' := by
  intro T Q hmem0
  cases hTr with
  | @comm s0 q0 lab0 S0 _ _ _ _ _hne h_send h_recv hmem_p hmem_q =>
    have hTEq : _ = (T, Q) := network_mem_unique hWF hmem_q hmem0
    subst hTEq
    cases h_recv with
    | recv =>
      unfold Network.replace
      exact List.mem_cons.mpr (Or.inl rfl)

/-- A type offers inputs for at most one role (choice roles are unique
    through unfolds). Induction with a variable label + equation hypotheses
    (the `st_trans_inp_imp_mon_tr_yes_base_aux` pattern). -/
private lemma rr_inp_role_unique {T T1 : SessionType} {α : st_label}
    (h1 : st_trans T α T1) : ∀ {p : Role} {lab : Lab} {S : DataSort},
      α = st_label.inp p lab S →
      ∀ {p' : Role} {lab' : Lab} {S' : DataSort} {T2 : SessionType},
      st_trans T (st_label.inp p' lab' S') T2 → p = p' := by
  induction h1 with
  | intC hmem =>
    intro p lab S e1 p' lab' S' T2 h2
    cases e1
  | extC =>
    intro p lab S e1 p' lab' S' T2 h2
    cases h2 with
    | extC =>
      cases e1
      rfl
  | tRec hsub ih =>
    intro p lab S e1 p' lab' S' T2 h2
    cases h2 with
    | tRec hsub2 => exact ih e1 hsub2

/-- Two successful scans for same-sender different messages are impossible:
    whichever matches first blocks the other. Joint induction on the queue. -/
private lemma rr_scan_blocks_other {acc left : Queue} {msg msg' : QueueMessage}
    {Q1 Q2 : Queue}
    (hne : msg' ≠ msg) (hsame : msg'.1 = msg.1)
    (h1 : Queue.dequeue.go acc left msg = some Q1)
    (h2 : Queue.dequeue.go acc left msg' = some Q2) : False := by
  induction left generalizing acc Q1 Q2 with
  | nil => simp [Queue.dequeue.go] at h1
  | cons m rest ih =>
    simp only [Queue.dequeue.go] at h1 h2
    by_cases hm : m = msg
    · subst hm
      have hm' : m ≠ msg' := fun h => hne h.symm
      have hs : m.1 = msg'.1 := hsame.symm
      rw [if_neg hm', if_pos hs] at h2
      cases h2
    · by_cases hm' : m = msg'
      · subst hm'
        have hs : m.1 = msg.1 := hsame
        rw [if_neg hm, if_pos hs] at h1
        cases h1
      · by_cases hs : m.1 = msg.1
        · have hs' : m.1 = msg'.1 := hs.trans hsame.symm
          rw [if_neg hm, if_pos hs] at h1
          cases h1
        · have hs' : m.1 ≠ msg'.1 := by
            intro hcon
            apply hs
            exact hcon.trans hsame
          rw [if_neg hm, if_neg hs] at h1
          rw [if_neg hm', if_neg hs'] at h2
          exact ih h1 h2

-- Fairness obligations (precise statements over `RoundRobinRun` below; proofs
-- need drain-exhaustiveness + scan/type preservation):

-- Production gap (documented limitation, not proved): nothing above prevents
-- tie-breaking from steering into a killing branch (a send/dequeue choice
-- after which the network is stuck although infinite paths existed) —
-- e.g. an internal-choice send picking a dead-end branch. Guaranteeing an
-- infinite run needs non-killing selection. Hence this design proves fairness
-- of infinite runs but does not discharge `hSched` on its own.

/-- Role served by block `j` (cycling through `round_robin_roles Ni`). -/
def round_robin_role_at (Ni : Network) (j : ℕ) : Role :=
  (round_robin_roles Ni).getD (j % (round_robin_roles Ni).length) ""

/-- Micro-step run: an infinite genuine-step sequence grouped into turn
    blocks. Block `j` serves `round_robin_role_at Ni j`: labels before `dend j` are its
    dequeues, `dend j` holds a quiescent state, and the block ends with at
    most one send (or nothing, with no send possible). -/
structure RoundRobinRun (Ni : Network) where
  seq : ℕ → Network
  lbl : ℕ → net_label
  tr : ∀ i, net_trans (seq i) (lbl i) (seq (i + 1))
  f0 : seq 0 = Ni
  wf : ∀ i, (seq i).WellFormed
  bound : ℕ → ℕ
  b0 : bound 0 = 0
  bmono : Monotone bound
  dend : ℕ → ℕ
  send : ℕ → Bool
  bounds_ok : ∀ j, bound j ≤ dend j ∧ dend j ≤ bound (j + 1)
  drain_lbl : ∀ j k, bound j ≤ k → k < dend j →
    ∃ p lab S, lbl k = net_label.τ_dequeue (round_robin_role_at Ni j) p lab S
  send_pos : ∀ j, send j = true → bound (j + 1) = dend j + 1
  send_is : ∀ j, send j = true → ∃ q lab S,
    lbl (dend j) = net_label.τ_comm (round_robin_role_at Ni j) q lab S
  nosend_pos : ∀ j, send j = false → bound (j + 1) = dend j
  nosend_none : ∀ j, send j = false → ∀ q lab S N2,
    ¬ net_trans (seq (dend j)) (net_label.τ_comm (round_robin_role_at Ni j) q lab S) N2
  quies : ∀ j, rr_quiescent (seq (dend j)) (round_robin_role_at Ni j)

/-- Membership in a replaced network: old entry or the new role. -/
private lemma rr_replace_mem {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    {r' : Role} {stq' : SessionTypeWithQueue}
    (h : (r', stq') ∈ Network.replace N r stq) : (r', stq') ∈ N ∨ r' = r := by
  unfold Network.replace at h
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact Or.inr (by simpa using congrArg Prod.fst h)
  · exact Or.inl (List.mem_of_mem_filter h)

/-- Single steps never introduce new roles (new entries reuse actors). -/
private lemma rr_roles_step {N1 N2 : Network} {δ : net_label}
    (hTr : net_trans N1 δ N2) :
    ∀ (r : Role) (stq : SessionTypeWithQueue),
      (r, stq) ∈ N2 → r ∈ N1.map Prod.fst := by
  intro r stq hmem
  cases hTr with
  | io_send _ hmemN =>
    rcases rr_replace_mem hmem with h | rfl
    · exact List.mem_map.mpr ⟨(r, stq), h, rfl⟩
    · exact List.mem_map.mpr ⟨_, hmemN, rfl⟩
  | io_recv _ hmemN =>
    rcases rr_replace_mem hmem with h | rfl
    · exact List.mem_map.mpr ⟨(r, stq), h, rfl⟩
    · exact List.mem_map.mpr ⟨_, hmemN, rfl⟩
  | dequeue _ hmemN =>
    rcases rr_replace_mem hmem with h | rfl
    · exact List.mem_map.mpr ⟨(r, stq), h, rfl⟩
    · exact List.mem_map.mpr ⟨_, hmemN, rfl⟩
  | comm _hne _ _ hmem_p hmem_q =>
    rcases rr_replace_mem hmem with h | rfl
    · rcases rr_replace_mem h with h | rfl
      · exact List.mem_map.mpr ⟨(r, stq), h, rfl⟩
      · exact List.mem_map.mpr ⟨_, hmem_p, rfl⟩
    · exact List.mem_map.mpr ⟨_, hmem_q, rfl⟩

/-- Reachability preserves role keys (steps only swap values). -/
lemma rr_roles_mono {Ni N : Network} (hStar : net_trans_star Ni N) :
    ∀ (r : Role) (stq : SessionTypeWithQueue),
      (r, stq) ∈ N → r ∈ Ni.map Prod.fst := by
  induction hStar with
  | refl => intro r stq h; exact List.mem_map.mpr ⟨(r, stq), h, rfl⟩
  | step _ hTr hStar' ih =>
    intro r stq hmem
    have h2 := ih _ _ hmem
    obtain ⟨⟨r', stq'⟩, h2', hfst⟩ := List.mem_map.mp h2
    have heq : r' = r := by simpa using hfst
    subst heq
    exact rr_roles_step hTr _ _ h2'

/-- Block cover below a bound: every index under a bound lies in a block. -/
private lemma rr_cover_below {Ni : Network} (run : RoundRobinRun Ni) (i J : ℕ)
    (h : i < run.bound J) :
    ∃ j, j < J ∧ run.bound j ≤ i ∧ i < run.bound (j + 1) := by
  have hex : ∃ m, i < run.bound m := ⟨J, h⟩
  have hMspec : i < run.bound (Nat.find hex) := Nat.find_spec hex
  have hMmin : ∀ m, i < run.bound m → Nat.find hex ≤ m :=
    fun m hm => Nat.find_min' hex hm
  have hMJ : Nat.find hex ≤ J := hMmin J h
  have hMpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exfalso; rw [h0, run.b0] at hMspec; omega
    · exact hpos
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have := hMmin _ hcon
    omega
  · have hEq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hEq]; exact hMspec

/-- Send flag from a non-drain position inside a block. -/
private lemma rr_send_of_cover {Ni : Network} (run : RoundRobinRun Ni) (j k : ℕ)
    (h1 : run.dend j ≤ k) (h2 : k < run.bound (j + 1)) : run.send j = true := by
  cases hsb : run.send j
  · exfalso
    have h3 : run.bound (j + 1) = run.dend j := run.nosend_pos j hsb
    omega
  · rfl

/-- Every in-block micro-step is internal. -/
private lemma rr_step_internal {Ni : Network} (run : RoundRobinRun Ni) (j k : ℕ)
    (h1 : run.bound j ≤ k) (h2 : k < run.bound (j + 1)) :
    is_internal_net_label (run.lbl k) := by
  by_cases hk : k < run.dend j
  · obtain ⟨p, lab, S, h⟩ := run.drain_lbl j k h1 hk
    rw [h]
    exact True.intro
  · push Not at hk
    have hsend := rr_send_of_cover run j k hk h2
    have hkb : run.bound (j + 1) = run.dend j + 1 := run.send_pos j hsend
    have hkeq : k = run.dend j := by omega
    obtain ⟨q, lab, S, h⟩ := run.send_is j hsend
    rw [hkeq, h]
    exact True.intro

/-- Every in-block micro-step is a dequeue or a comm with the block role. -/
private lemma rr_lbl_form {Ni : Network} (run : RoundRobinRun Ni) (j k : ℕ)
    (h1 : run.bound j ≤ k) (h2 : k < run.bound (j + 1)) :
    (∃ r p lab S, run.lbl k = net_label.τ_dequeue r p lab S) ∨
    (∃ r q lab S, run.lbl k = net_label.τ_comm r q lab S) := by
  by_cases hk : k < run.dend j
  · obtain ⟨p, lab, S, h⟩ := run.drain_lbl j k h1 hk
    exact Or.inl ⟨_, _, _, _, h⟩
  · push Not at hk
    have hsend := rr_send_of_cover run j k hk h2
    have hkb : run.bound (j + 1) = run.dend j + 1 := run.send_pos j hsend
    have hkeq : k = run.dend j := by omega
    obtain ⟨q, lab, S, h⟩ := run.send_is j hsend
    exact Or.inr ⟨_, _, _, _, by rw [hkeq]; exact h⟩

/-- Reachability of block-covered indices. -/
private lemma rr_reachable_at {Ni : Network} (run : RoundRobinRun Ni) :
    ∀ (i J : ℕ), i ≤ run.bound J → net_trans_star Ni (run.seq i) := by
  intro i
  induction i with
  | zero => intro J _; rw [run.f0]; exact net_trans_star.refl _
  | succ i ih =>
    intro J h
    have hlt : i < run.bound J := by omega
    obtain ⟨j, _, hbj, hbj1⟩ := rr_cover_below run i J hlt
    have hInt := rr_step_internal run j i hbj hbj1
    have ih' := ih J (by omega)
    exact net_trans_star.trans ih' (net_trans_star.step hInt (run.tr i) (net_trans_star.refl _))

/-- Every role appears in every full cycle window. -/
lemma rr_cycle_cover (Ni : Network) (hne : round_robin_roles Ni ≠ []) (J : ℕ)
    (x : Role) (hx : x ∈ round_robin_roles Ni) :
    ∃ t, t < (round_robin_roles Ni).length ∧ round_robin_role_at Ni (J + t) = x := by
  obtain ⟨t0, ht0, hxt⟩ := List.mem_iff_getElem.mp hx
  have hpos : 0 < (round_robin_roles Ni).length := List.length_pos_iff_ne_nil.mpr hne
  have hJm : J % (round_robin_roles Ni).length < (round_robin_roles Ni).length := Nat.mod_lt _ hpos
  have hex : ∃ t, t < (round_robin_roles Ni).length ∧
      (J + t) % (round_robin_roles Ni).length = t0 := by
    by_cases hle : t0 < J % (round_robin_roles Ni).length
    · refine ⟨t0 + (round_robin_roles Ni).length - J % (round_robin_roles Ni).length, by omega, ?_⟩
      have hXlt : t0 + (round_robin_roles Ni).length - J % (round_robin_roles Ni).length
          < (round_robin_roles Ni).length := by omega
      rw [Nat.add_mod, Nat.mod_eq_of_lt hXlt]
      have hSum : J % (round_robin_roles Ni).length +
          (t0 + (round_robin_roles Ni).length - J % (round_robin_roles Ni).length)
          = t0 + (round_robin_roles Ni).length :=
        Nat.add_sub_cancel' (by omega)
      rw [hSum]
      have hEq : t0 + (round_robin_roles Ni).length
          = t0 + (round_robin_roles Ni).length * 1 := by rw [Nat.mul_one]
      rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht0]
    · push Not at hle
      refine ⟨t0 - J % (round_robin_roles Ni).length, by omega, ?_⟩
      have hXlt : t0 - J % (round_robin_roles Ni).length < (round_robin_roles Ni).length := by omega
      rw [Nat.add_mod, Nat.mod_eq_of_lt hXlt]
      have hSum : J % (round_robin_roles Ni).length + (t0 - J % (round_robin_roles Ni).length)
          = t0 :=
        Nat.add_sub_cancel' (by omega)
      rw [hSum, Nat.mod_eq_of_lt ht0]
  obtain ⟨t, htn, hmod⟩ := hex
  refine ⟨t, htn, ?_⟩
  subst t0
  unfold round_robin_role_at
  rw [List.getD_eq_getElem _ _ (Nat.mod_lt _ hpos)]
  exact hxt

/-- Monotone bounded `ℕ`-sequences stabilize. -/
private lemma rr_bounded_const {f : ℕ → ℕ} (hmono : Monotone f)
    (hbdd : ∃ K, ∀ j, f j ≤ K) : ∃ J, ∀ j, J ≤ j → f j = f J := by
  obtain ⟨K, hK⟩ := hbdd
  by_contra hcon
  push Not at hcon
  have hlt : ∀ J, ∃ j, J ≤ j ∧ f J < f j := by
    intro J
    obtain ⟨j, hJj, hne⟩ := hcon J
    exact ⟨j, hJj, by have hle := hmono hJj; omega⟩
  have key : ∀ k, ∃ j, k ≤ f j := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨j, hj⟩ := ih
      obtain ⟨j', hJj', hlt'⟩ := hlt j
      exact ⟨j', by omega⟩
  obtain ⟨j, hj⟩ := key (K + 1)
  have := hK j
  omega


/-- Fairness clause 2 (dequeues): a dequeue enabled at step `i` fires later
    with its exact label. Least-r-action structure: the invariant (entry +
    scan) rides non-`r` steps only; the least later `r`-action must be the
    target itself (scan-ordering + input-role uniqueness; a send would
    contradict step exclusivity); with no later `r`-action, any future
    `r`-turn's drain must fire it. -/
private lemma rr_deq_clause {Ni : Network} {hne : round_robin_roles Ni ≠ []}
    (run : RoundRobinRun Ni)
    (hUnbdd : ∀ K, ∃ j, K < run.bound j) :
    ∀ (i : ℕ) (r p : Role) (lab : Lab) (S : DataSort) (N' : Network),
      net_trans (run.seq i) (net_label.τ_dequeue r p lab S) N' →
      ∃ k, i ≤ k ∧ run.lbl k = net_label.τ_dequeue r p lab S := by
  classical
  intro i r p lab S N' hTr
  cases hTr with
  | @dequeue _ _ _ _ _ _ hSQ hmem =>
    cases hSQ with
    | @dequeue T T' Q Q' _ _ _ hST hQ =>
      obtain ⟨J, hJ⟩ := hUnbdd i
      have hReach : net_trans_star Ni (run.seq i) :=
        rr_reachable_at run i J (Nat.le_of_lt hJ)
      have hrRoles : r ∈ round_robin_roles Ni :=
        List.mem_eraseDups.mpr (rr_roles_mono hReach _ _ hmem)
      -- Invariant over non-`r` ranges: entry `(T, Qk)` with succeeding scan.
      have hInv : ∀ (d k : ℕ), k = i + d →
          (∀ m, i ≤ m → m < k →
            ¬ (((∃ p' lab' S', run.lbl m = net_label.τ_dequeue r p' lab' S') ∨
              (∃ q' lab' S', run.lbl m = net_label.τ_comm r q' lab' S')))) →
          ∃ Qk Qk', (r, (T, Qk)) ∈ run.seq k ∧
            Qk.dequeue (QueueMessage.msg p lab S) = some Qk' := by
        intro d
        induction d with
        | zero =>
          intro k hk _
          have hki : k = i := by omega
          rw [hki]
          exact ⟨Q, Q', hmem, hQ⟩
        | succ d ih =>
          intro k hk hno
          have hprev_lt : i + d < k := by omega
          have hge : i ≤ i + d := by omega
          obtain ⟨Qp, Qp', hmemP, hscanP⟩ := ih (i + d) rfl
            (fun m hm1 hm2 => hno m hm1 (by omega))
          have hnot := hno (i + d) hge hprev_lt
          obtain ⟨J', hJ'⟩ := hUnbdd (i + d)
          obtain ⟨j', _, hbj', hbj'1⟩ := rr_cover_below run (i + d) J' hJ'
          have hne_r : round_robin_role_at Ni j' ≠ r := by
            by_cases hpos : i + d < run.dend j'
            · obtain ⟨p', lab', S', hfire⟩ :=
                run.drain_lbl j' (i + d) hbj' hpos
              intro hcon
              apply hnot
              rw [hcon] at hfire
              exact Or.inl ⟨p', lab', S', hfire⟩
            · push Not at hpos
              have hsend : run.send j' = true := by
                rcases hsb : run.send j' with _ | _
                · exfalso
                  have h3 := run.nosend_pos j' hsb
                  omega
                · rfl
              have hkb2 : run.bound (j' + 1) = run.dend j' + 1 :=
                run.send_pos j' hsend
              have hkeq : i + d = run.dend j' := by omega
              obtain ⟨q', lab', S', hfire⟩ := run.send_is j' hsend
              rw [← hkeq] at hfire
              intro hcon
              apply hnot
              rw [hcon] at hfire
              exact Or.inr ⟨q', lab', S', hfire⟩
          have hstep := run.tr (i + d)
          by_cases hpos : i + d < run.dend j'
          · obtain ⟨p', lab', S', hfire⟩ :=
              run.drain_lbl j' (i + d) hbj' hpos
            rw [hfire] at hstep
            have hmemR := rr_entry_untouched_deq hne_r hstep (T, Qp) hmemP
            have hkk : k = (i + d) + 1 := by omega
            rw [hkk]
            exact ⟨Qp, Qp', hmemR, hscanP⟩
          · push Not at hpos
            have hsend : run.send j' = true := by
              rcases hsb : run.send j' with _ | _
              · exfalso
                have h3 := run.nosend_pos j' hsb
                omega
              · rfl
            have hkb2 : run.bound (j' + 1) = run.dend j' + 1 :=
              run.send_pos j' hsend
            have hkeq : i + d = run.dend j' := by omega
            obtain ⟨q', lab', S', hfire⟩ := run.send_is j' hsend
            rw [← hkeq] at hfire
            rw [hfire] at hstep
            by_cases heqq : q' = r
            · rw [heqq] at hfire hstep
              have hmemR := rr_type_untouched_recv (run.wf (i + d)) hstep
                T Qp hmemP
              have hscanR : (Qp ++ [QueueMessage.msg (round_robin_role_at Ni j') lab' S']).dequeue
                  (QueueMessage.msg p lab S) = some _ :=
                rr_scan_append hscanP
              have hkk : k = (i + d) + 1 := by omega
              rw [hkk]
              exact ⟨_, _, hmemR, hscanR⟩
            · have hmemR := rr_entry_untouched_comm hne_r heqq hstep
                (T, Qp) hmemP
              have hkk : k = (i + d) + 1 := by omega
              rw [hkk]
              exact ⟨Qp, Qp', hmemR, hscanP⟩
      by_cases hEx : ∃ k, i ≤ k ∧
          ((∃ p' lab' S', run.lbl k = net_label.τ_dequeue r p' lab' S') ∨
            (∃ q' lab' S', run.lbl k = net_label.τ_comm r q' lab' S'))
      · -- Least later `r`-action: dequeue (must be the target) or send
        -- (exclusivity contradiction).
        set ks := Nat.find hEx with hks
        have hspec : i ≤ ks ∧
            ((∃ p' lab' S', run.lbl ks = net_label.τ_dequeue r p' lab' S') ∨
              (∃ q' lab' S', run.lbl ks = net_label.τ_comm r q' lab' S')) :=
          Nat.find_spec hEx
        have hmin : ∀ k, i ≤ k →
            ((∃ p' lab' S', run.lbl k = net_label.τ_dequeue r p' lab' S') ∨
              (∃ q' lab' S', run.lbl k = net_label.τ_comm r q' lab' S')) →
            ks ≤ k :=
          fun k hik hPk => Nat.find_min' hEx ⟨hik, hPk⟩
        obtain ⟨Qk, Qk', hmemK, hscanK⟩ := hInv (ks - i) ks
          (by omega) (fun m hm1 hm2 => by
            intro hcon
            have := hmin m hm1 hcon
            omega)
        rcases hspec.2 with ⟨p', lab', S', hfire⟩ | ⟨q', lab', S', hfire⟩
        · have hstep := run.tr ks
          rw [hfire] at hstep
          generalize hN' : run.seq (ks + 1) = N2' at hstep
          cases hstep with
          | @dequeue _ _ _ _ _ _ hSQ' hmem2 =>
            cases hSQ' with
            | @dequeue T2 _ Q2 Q2' _ _ _ hST' hQ' =>
              have hUq : (T2, Q2) = (T, Qk) :=
                network_mem_unique (run.wf ks) hmem2 hmemK
              obtain ⟨hTT, hQQ⟩ := Prod.mk.inj hUq
              rw [hTT] at hST'
              have hpp : p' = p := rr_inp_role_unique hST' rfl hST
              rw [hpp] at hfire hQ'
              by_cases heq : lab' = lab ∧ S' = S
              · obtain ⟨heq1, heq2⟩ := heq
                rw [heq1, heq2] at hfire
                exact ⟨ks, hspec.1, hfire⟩
              · have hne : QueueMessage.msg p lab' S' ≠ QueueMessage.msg p lab S := by
                    intro hcon
                    injection hcon with _ h2 h3
                    exact heq ⟨h2, h3⟩
                have hsame : (QueueMessage.msg p lab' S').1
                    = (QueueMessage.msg p lab S).1 := rfl
                rw [hQQ] at hQ'
                have hscanK' : Queue.dequeue.go [] Qk (QueueMessage.msg p lab S)
                    = some _ := hscanK
                have hQ'' : Queue.dequeue.go [] Qk (QueueMessage.msg p lab' S')
                    = some _ := hQ'
                exact False.elim (rr_scan_blocks_other hne hsame hscanK' hQ'')
        · have hstep := run.tr ks
          rw [hfire] at hstep
          generalize hN' : run.seq (ks + 1) = N2' at hstep
          cases hstep with
  | @comm _ _ _ _ _ _ _ _ hnePQ h_send h_recv hmem_p hmem_q =>
            cases h_send with
            | @send _ _ _ _ _ _ hSTo =>
              have hUq : (_ : SessionTypeWithQueue) = (T, Qk) :=
                network_mem_unique (run.wf ks) hmem_p hmemK
              obtain ⟨hTT, hQQ⟩ := Prod.mk.inj hUq
              rw [hTT] at hSTo
              exact False.elim (sttr_out_not_inp hSTo hST)
      · -- No later `r`-action: any future `r`-turn's drain must fire it.
        obtain ⟨J0, hJ0⟩ := hUnbdd i
        obtain ⟨t, htt, hrole⟩ := rr_cycle_cover Ni hne J0 r hrRoles
        have hbJ : run.bound J0 ≤ run.bound (J0 + t) :=
          run.bmono (Nat.le_add_right _ _)
        have hki : i < run.bound (J0 + t) := by omega
        obtain ⟨Qstar, Qstar', hmemS, hscanS⟩ := hInv (run.bound (J0 + t) - i)
          (run.bound (J0 + t)) (by omega)
          (fun m hm1 hm2 hcon => hEx ⟨m, hm1, hcon⟩)
        by_cases hemptyRange : run.bound (J0 + t) < run.dend (J0 + t)
        · -- Nonempty drain: its first firing is an `r`-action — contradiction.
          obtain ⟨p', lab', S', hfire⟩ := run.drain_lbl (J0 + t)
            (run.bound (J0 + t)) (Nat.le_refl _) hemptyRange
          rw [hrole] at hfire
          exact False.elim (hEx ⟨_, hki.le, Or.inl ⟨p', lab', S', hfire⟩⟩)
        · push Not at hemptyRange
          -- Empty drain: quiescence contradicts the fireable target.
          have hEq : run.dend (J0 + t) = run.bound (J0 + t) := by
            have h1 := (run.bounds_ok (J0 + t)).1
            omega
          have hQ := run.quies (J0 + t)
          rw [hEq] at hQ
          simp only [rr_quiescent] at hQ
          rw [← hrole] at hmemS
          exact False.elim
            (hQ T Qstar p lab S T' Qstar' hmemS (sq_trans.dequeue hST hscanS))

/-- New head entry of a replacement. -/
private lemma rr_replace_head {N : Network} {r : Role} {stq : SessionTypeWithQueue} :
    (r, stq) ∈ Network.replace N r stq := by
  unfold Network.replace
  exact List.mem_cons.mpr (Or.inl rfl)

/-- Old entries survive replacement at other roles. -/
private lemma rr_replace_forward {N : Network} {r s : Role}
    {stq stq' : SessionTypeWithQueue}
    (h : (r, stq) ∈ N) (hne : s ≠ r) : (r, stq) ∈ Network.replace N s stq' := by
  unfold Network.replace
  simp only [List.mem_cons, List.mem_filter]
  refine Or.inr ⟨h, ?_⟩
  exact bne_iff_ne.mpr hne.symm

/-- Role keys persist forward along stars: an entry's role keeps (some)
    entry. Proved by induction generalizing the start (single step analysis
    per constructor, then the induction hypothesis). -/
private lemma rr_key_mem_entry {N1 N2 : Network} (hStar : net_trans_star N1 N2) :
    ∀ (r : Role) (stq : SessionTypeWithQueue), (r, stq) ∈ N1 →
    ∃ stq', (r, stq') ∈ N2 := by
  induction hStar with
  | refl => intro r stq hmem; exact ⟨stq, hmem⟩
  | step _ hTr _ ih =>
    intro r stq hmem
    cases hTr with
    | @io_send s _ _ stq' _ _ _ _ =>
      by_cases heq : s = r
      · subst s
        exact ih _ _ rr_replace_head
      · exact ih _ _ (rr_replace_forward hmem heq)
    | @io_recv s _ _ stq' _ _ _ _ =>
      by_cases heq : s = r
      · subst s
        exact ih _ _ rr_replace_head
      · exact ih _ _ (rr_replace_forward hmem heq)
    | @dequeue s _ _ stq' _ _ _ _ =>
      by_cases heq : s = r
      · subst heq
        exact ih _ _ rr_replace_head
      · exact ih _ _ (rr_replace_forward hmem heq)
    | @comm s q _ _ _ astqp' _ astqq' _hne _ _ _ _ =>
      by_cases heqs : s = r
      · subst s
        by_cases heqq : q = r
        · subst q
          exact ih _ _ rr_replace_head
        · exact ih _ _ (rr_replace_forward
            (rr_replace_head (N := _) (r := _) (stq := _)) heqq)
      · by_cases heqq : q = r
        · subst q
          exact ih _ _ rr_replace_head
        · exact ih _ stq (rr_replace_forward
            (rr_replace_forward hmem heqs) (fun h => heqq h))

/-- Role keys persist forward along stars, membership form. -/
private lemma rr_key_mem {Ni N : Network} (hStar : net_trans_star Ni N) (r : Role)
    (h : r ∈ Ni.map Prod.fst) : ∃ stq, (r, stq) ∈ N := by
  obtain ⟨⟨r', stq⟩, hmem, hfst⟩ := List.mem_map.mp h
  have heq : r' = r := by simpa using hfst
  subst heq
  exact rr_key_mem_entry hStar _ _ hmem

/-- Fairness clause 1 (comms): a role able to send fires some send later.
    Any `p`-send is already a witness; otherwise the type is frozen (`p`-sends
    excluded by case, `p`-dequeues by exclusivity), so the turn's send must
    fire (`sq_trans.recv` is always enabled). Needs no leastness, no cycling
    beyond turn existence, no scan tracking. -/
private lemma rr_comm_clause {Ni : Network} {hne : round_robin_roles Ni ≠ []}
    (run : RoundRobinRun Ni)
    (hUnbdd : ∀ K, ∃ j, K < run.bound j) :
    ∀ (i : ℕ) (p q : Role) (lab : Lab) (S : DataSort) (N' : Network),
      net_trans (run.seq i) (net_label.τ_comm p q lab S) N' →
      ∃ k, i ≤ k ∧ ∃ (q' : Role) (lab' : Lab) (S' : DataSort),
        run.lbl k = net_label.τ_comm p q' lab' S' := by
  intro i p q lab S N' hTr
  cases hTr with
  | @comm _ _ _ _ _ _ _ _ hnePQ h_send h_recv hmem_p hmem_q =>
    cases h_send with
    | @send T _ Q _ _ _ hST =>
      obtain ⟨J, hJ⟩ := hUnbdd i
      have hReach : net_trans_star Ni (run.seq i) :=
        rr_reachable_at run i J (Nat.le_of_lt hJ)
      have hpRoles : p ∈ round_robin_roles Ni :=
        List.mem_eraseDups.mpr (rr_roles_mono hReach _ _ hmem_p)
      -- A `p`-turn reaching past `i`.
      obtain ⟨J0, hJ0⟩ := hUnbdd i
      obtain ⟨t, _htt, hrole⟩ := rr_cycle_cover Ni hne J0 p hpRoles
      have hbJ : i < run.bound (J0 + t) := by
        have h1 : run.bound J0 ≤ run.bound (J0 + t) :=
          run.bmono (Nat.le_add_right _ _)
        omega
      have hdJ : i ≤ run.dend (J0 + t) := by
        have h1 := (run.bounds_ok (J0 + t)).1
        omega
      -- Either a `p`-send fires in range (witness), or the type stays `T`.
      rcases Classical.em (∃ m, i ≤ m ∧ m ≤ run.dend (J0 + t) ∧
          (∃ q' lab' S', run.lbl m = net_label.τ_comm p q' lab' S')) with
        ⟨m, hm1, hm2, q', lab', S', hfire⟩ | hNoSend
      · exact ⟨m, hm1, q', lab', S', hfire⟩
      · push Not at hNoSend
        -- Invariant: type `T` preserved over `[i, dend (J0+t)]`.
        have hInv : ∀ (d k : ℕ), k = i + d → k ≤ run.dend (J0 + t) →
            ∃ Qk, (p, (T, Qk)) ∈ run.seq k := by
          intro d
          induction d with
          | zero =>
            intro k hk _
            have hki : k = i := by omega
            rw [hki]
            exact ⟨Q, hmem_p⟩
          | succ d ih =>
            intro k hk hkb
            have hprev_lt : i + d < k := by omega
            have hge : i ≤ i + d := by omega
            obtain ⟨Qp, hmemP⟩ := ih (i + d) rfl (by omega)
            have hnosend : ¬ ∃ q' lab' S',
                run.lbl (i + d) = net_label.τ_comm p q' lab' S' := by
              intro hcon
              obtain ⟨qq, ll, ss, hfire⟩ := hcon
              exact hNoSend (i + d) hge (by omega) qq ll ss hfire
            obtain ⟨J', hJ'⟩ := hUnbdd (i + d)
            obtain ⟨j', _, hbj', hbj'1⟩ := rr_cover_below run (i + d) J' hJ'
            have hstep := run.tr (i + d)
            by_cases hpos : i + d < run.dend j'
            · -- Drain step: `p`-actor impossible (exclusivity), else preserve.
              obtain ⟨p', lab', S', hfire⟩ :=
                run.drain_lbl j' (i + d) hbj' hpos
              rw [hfire] at hstep
              by_cases heq : round_robin_role_at Ni j' = p
              · rw [heq] at hfire hstep
                generalize hN' : run.seq (i + d + 1) = N2' at hstep
                cases hstep with
                | @dequeue _ _ _ _ _ _ hSQ' hmem2 =>
                  cases hSQ' with
                  | @dequeue T2 _ Q2 _ _ _ _ hST' hQ' =>
                    have hUq : (T2, Q2) = (T, Qp) :=
                      network_mem_unique (run.wf (i + d)) hmem2 hmemP
                    obtain ⟨hTT, hQQ⟩ := Prod.mk.inj hUq
                    rw [hTT] at hST'
                    exact False.elim (sttr_out_not_inp hST hST')
              · have hmemR := rr_entry_untouched_deq heq hstep (T, Qp) hmemP
                have hkk : k = (i + d) + 1 := by omega
                rw [hkk]
                exact ⟨Qp, hmemR⟩
            · push Not at hpos
              have hsend : run.send j' = true := by
                rcases hsb : run.send j' with _ | _
                · exfalso
                  have h3 := run.nosend_pos j' hsb
                  omega
                · rfl
              have hkb2 : run.bound (j' + 1) = run.dend j' + 1 :=
                run.send_pos j' hsend
              have hkeq : i + d = run.dend j' := by omega
              obtain ⟨q', lab', S', hfire⟩ := run.send_is j' hsend
              rw [← hkeq] at hfire
              rw [hfire] at hstep
              by_cases heq : round_robin_role_at Ni j' = p
              · -- A `p`-send here contradicts the case hypothesis.
                rw [heq] at hfire
                exact False.elim (hNoSend (i + d) hge (by omega) q' lab' S' hfire)
              · by_cases heqq : q' = p
                · rw [heqq] at hfire hstep
                  have hmemR := rr_type_untouched_recv (run.wf (i + d)) hstep
                    T Qp hmemP
                  have hkk : k = (i + d) + 1 := by omega
                  rw [hkk]
                  exact ⟨_, hmemR⟩
                · have hmemR := rr_entry_untouched_comm heq heqq hstep
                    (T, Qp) hmemP
                  have hkk : k = (i + d) + 1 := by omega
                  rw [hkk]
                  exact ⟨Qp, hmemR⟩
        -- At the turn: entry `(T, Qstar)`; the send must fire.
        obtain ⟨Qstar, hmemS⟩ := hInv (run.dend (J0 + t) - i)
          (run.dend (J0 + t)) (by omega) (Nat.le_refl _)
        rcases hsb : run.send (J0 + t) with _ | _
        · -- Send skipped: send-then-receive capability contradicts
          -- `nosend_none` (receiver entry by key persistence).
          have hNS := run.nosend_none (J0 + t) hsb
          rw [hrole] at hNS
          have hqNi : q ∈ Ni.map Prod.fst := rr_roles_mono hReach _ _ hmem_q
          have hReachD : net_trans_star Ni (run.seq (run.dend (J0 + t))) :=
            rr_reachable_at run (run.dend (J0 + t)) (J0 + t + 1) (by
              have h1 := (run.bounds_ok (J0 + t)).2
              omega)
          obtain ⟨⟨Tq, Qq⟩, hmemQ⟩ := rr_key_mem hReachD q hqNi
          have hsendfire : sq_trans (T, Qstar) (sq_action.send q lab S) _ :=
            sq_trans.send hST
          have hrecvfire : sq_trans (Tq, Qq) (sq_action.recv p lab S) _ :=
            sq_trans.recv
          have hComm : net_trans (run.seq (run.dend (J0 + t)))
              (net_label.τ_comm p q lab S) _ :=
            net_trans.comm hnePQ hsendfire hrecvfire hmemS hmemQ
          exact False.elim (hNS q lab S _ hComm)
        · -- Send taken: its label (role rewritten) is the witness.
          obtain ⟨q', lab', S', hfire⟩ := run.send_is (J0 + t) hsb
          rw [hrole] at hfire
          exact ⟨run.dend (J0 + t), hdJ, q', lab', S', hfire⟩


/-- Labeled drain trace: `r`-dequeues with recorded labels (the
    label-explicit twin of `rr_drain_star`, needed wherever a scheduler
    must replay or audit the drained steps). -/
inductive rr_drain_trace : Network → Network → Role → List net_label → Prop where
  | refl (N r) : rr_drain_trace N N r []
  | step {N1 N2 N3 r p lab S ls}
      (h : net_trans N1 (net_label.τ_dequeue r p lab S) N2)
      (hTail : rr_drain_trace N2 N3 r ls) :
      rr_drain_trace N1 N3 r (net_label.τ_dequeue r p lab S :: ls)

/-- Turn policy over an invariant: at a drained quiescent state
    satisfying `Inv`, either fire a send (with evidence AND
    preservation) or prove none exists. Preservation rides in the
    evidence branch, so turns never silently break the invariant. -/
def turn_policy (Inv : Network → Prop) : Prop :=
  ∀ (r : Role) (Nmid : Network), Inv Nmid → Nmid.WellFormed →
    rr_quiescent Nmid r →
    (∃ (q : Role) (lab : Lab) (S : DataSort) (N' : Network),
      net_trans Nmid (net_label.τ_comm r q lab S) N' ∧ Inv N') ∨
    (∀ (q : Role) (lab : Lab) (S : DataSort) (N' : Network),
      ¬ net_trans Nmid (net_label.τ_comm r q lab S) N')

/-- Fair path from an unbounded micro-run, with labels exposed: the
    same construction as the dichotomy's fair arm, but the path is
    returned together with its definitional label equation (an
    existential-obtained path would hide the labels behind an opaque
    variable, unusable for never-fires arguments). -/
theorem RoundRobinRun.toFairPath {Ni : Network} {hne : round_robin_roles Ni ≠ []}
    (run : RoundRobinRun Ni) (hUnbdd : ∀ K, ∃ j, K < run.bound j) :
    ∃ path : InfiniteNetworkPath, path.seq 0 = Ni ∧ IsFair path ∧
      ∀ k, path.δ k = run.lbl k := by
  refine ⟨⟨run.seq, run.lbl, ?_, run.tr⟩, run.f0, ?_, fun k => rfl⟩
  · intro i
    obtain ⟨J, hJ⟩ := hUnbdd i
    obtain ⟨j, _, hbj, hbj1⟩ := rr_cover_below run i J hJ
    rcases rr_lbl_form run j i hbj hbj1 with ⟨r, p, lab, S, h⟩ | ⟨r, q, lab, S, h⟩
    · exact ⟨r, p, lab, S, Or.inl h⟩
    · exact ⟨r, q, lab, S, Or.inr h⟩
  · intro i
    constructor
    · intro p hEn
      obtain ⟨q, lab, S, N', hTr⟩ := hEn
      obtain ⟨k, hik, q', lab', S', hkl⟩ :=
        rr_comm_clause (hne := hne) run hUnbdd i p q lab S N' hTr
      exact ⟨k, hik, q', lab', S', hkl⟩
    · intro p q lab S hEn
      obtain ⟨N', hTr⟩ := hEn
      obtain ⟨k, hik, hkl⟩ := rr_deq_clause (hne := hne) run hUnbdd i p q lab S N' hTr
      exact ⟨k, hik, hkl⟩

/-- Labeled drain trace as DATA: the `Type`-valued twin of `rr_drain_trace`
    (same constructors). `Prop`-traces cannot build `seq` data
    (`propRecLargeElim` — the G0 finding); structural recursion and
    induction below are legal only because this twin is `Type`-valued
    (the `LabeledStar` precedent, now in the appendix below). -/
inductive RoundRobinDrainTraceT : Network → Network → Role → List net_label → Type where
  | refl (N r) : RoundRobinDrainTraceT N N r []
  | step {N1 N2 N3 r p lab S ls}
      (h : net_trans N1 (net_label.τ_dequeue r p lab S) N2)
      (hTail : RoundRobinDrainTraceT N2 N3 r ls) :
      RoundRobinDrainTraceT N1 N3 r (net_label.τ_dequeue r p lab S :: ls)

/-- Forget data (structural; feeds the existing `Prop`-trace lemmas). -/
def RoundRobinDrainTraceT.forget {N N' : Network} {r : Role} {ls : List net_label} :
    RoundRobinDrainTraceT N N' r ls → rr_drain_trace N N' r ls
  | RoundRobinDrainTraceT.refl _ _ => rr_drain_trace.refl _ _
  | RoundRobinDrainTraceT.step h hTail => rr_drain_trace.step h hTail.forget

/-- Length (structural — legal since `RoundRobinDrainTraceT` is `Type`-valued). -/
def RoundRobinDrainTraceT.length {N N' : Network} {r : Role} {ls : List net_label} :
    RoundRobinDrainTraceT N N' r ls → Nat
  | RoundRobinDrainTraceT.refl _ _ => 0
  | RoundRobinDrainTraceT.step _ hTail => hTail.length + 1

/-- Well-formedness along labeled drains (each step preserves). -/
private theorem RoundRobinDrainTraceT.preserves {N N' : Network} {r : Role}
    {ls : List net_label} (h : RoundRobinDrainTraceT N N' r ls)
    (hWF : N.WellFormed) : N'.WellFormed := by
  revert hWF
  induction h with
  | refl =>
    intro hWF
    exact hWF
  | step hTr hTail ih =>
    intro hWF
    exact ih (Network.wellFormedPreserved _ _ _ hWF hTr (by trivial))

/-- Empty labeled drains are stationary. -/
theorem RoundRobinDrainTraceT.nil_eq {N N' : Network} {r : Role}
    {ls : List net_label} (h : RoundRobinDrainTraceT N N' r ls) (hL : ls = []) :
    N' = N := by
  cases h with
  | refl => rfl
  | step => simp at hL

/-- Labeled drain computer (data version): from any well-formed state,
    drain `r` to quiescence while recording every label. Verbatim port
    of `rr_drain_trace_compute`, except the `Type`-valued trace is an
    existential *binder* (`∃ … (_ : RoundRobinDrainTraceT …)`), never an `∧`
    conjunct (`And` demands `Prop` both sides — the G0 finding). -/
lemma rr_drain_trace_compute_t (N : Network) (r : Role) (hWF : N.WellFormed) :
    ∃ Nmid, ∃ ls, ∃ _ : RoundRobinDrainTraceT N Nmid r ls, rr_quiescent Nmid r := by
  have key : ∀ (k : Nat) (N : Network), N.WellFormed →
      (∀ (T : SessionType) (Q : Queue), (r, (T, Q)) ∈ N → Q.length ≤ k) →
      ∃ Nmid, ∃ ls, ∃ _ : RoundRobinDrainTraceT N Nmid r ls, rr_quiescent Nmid r := by
    intro k
    induction k with
    | zero =>
      intro N hWF hlen
      refine ⟨N, [], RoundRobinDrainTraceT.refl _ _, ?_⟩
      intro T Q p lab S T' Q' hmem hSQ
      cases hSQ with
      | dequeue hST hQ =>
        cases Q with
        | nil =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQ
        | cons m rest =>
          have hle : (m :: rest).length ≤ 0 := hlen T (m :: rest) hmem
          simp at hle
    | succ k ih =>
      intro N hWF hlen
      by_cases hqui : ∃ (T : SessionType) (Q : Queue) (p : Role) (lab : Lab)
          (S : DataSort) (T' : SessionType) (Q' : Queue),
          (r, (T, Q)) ∈ N ∧ sq_trans (T, Q) (sq_action.dequeue p lab S) (T', Q')
      · obtain ⟨T, Q, p, lab, S, T', Q', hmem, hSQ⟩ := hqui
        cases hSQ with
        | dequeue hST hQ =>
          have hdrop := Queue.dequeue_length_drop hQ
          have hStep : net_trans N (net_label.τ_dequeue r p lab S)
              (N.replace r (T', Q')) :=
            net_trans.dequeue (sq_trans.dequeue hST hQ) hmem
          have hWF' : (N.replace r (T', Q')).WellFormed :=
            Network.wellFormedPreserved N _ _ hWF hStep (by trivial)
          have hlen' : ∀ (T0 : SessionType) (Q0 : Queue),
              (r, (T0, Q0)) ∈ N.replace r (T', Q') → Q0.length ≤ k := by
            intro T0 Q0 hmem0
            unfold Network.replace at hmem0
            simp only [List.mem_cons, List.mem_filter] at hmem0
            rcases hmem0 with hmem0 | ⟨hmem0, hcond⟩
            · obtain ⟨hrr, hTQ⟩ := Prod.mk.inj hmem0
              obtain ⟨hT, hQ⟩ := Prod.mk.inj hTQ
              have hleQ : Q.length ≤ k + 1 := hlen T Q hmem
              have hQlen : Q0.length = Q'.length := congrArg List.length hQ
              omega
            · have hr : (r, (T0, Q0)).1 = r := rfl
              exact (bne_iff_ne.mp hcond hr).elim
          obtain ⟨Nmid, ls, hTrace, hQuies⟩ := ih _ hWF' hlen'
          exact ⟨Nmid, net_label.τ_dequeue r p lab S :: ls,
            RoundRobinDrainTraceT.step hStep hTrace, hQuies⟩
      · refine ⟨N, [], RoundRobinDrainTraceT.refl _ _, ?_⟩
        intro T Q p lab S T' Q' hmem hSQ
        exact absurd ⟨T, Q, p, lab, S, T', Q', hmem, hSQ⟩ hqui
  by_cases hr : ∃ stq, (r, stq) ∈ N
  · obtain ⟨⟨T0, Q0⟩, hmem0⟩ := hr
    exact key Q0.length _ hWF (fun T Q hmem => by
      have heq := network_mem_unique hWF hmem0 hmem
      obtain ⟨hT, hQ⟩ := Prod.mk.inj heq
      have hQlen : Q0.length = Q.length := congrArg List.length hQ
      omega)
  · exact key 0 _ hWF (fun T Q hmem => absurd ⟨(T, Q), hmem⟩ hr)

/-- One labeled turn as DATA: the `Type`-valued twin of `RrTurnLabeled`
    (same shape, drain trace carried explicitly for G3 flattening). -/
inductive RoundRobinTurnT : Network → Network → Role → List net_label → Type where
  | fire {N Nmid N' r lsd} (q : Role) (lab : Lab) (S : DataSort)
      (hTrace : RoundRobinDrainTraceT N Nmid r lsd)
      (hQuies : rr_quiescent Nmid r)
      (hStep : net_trans Nmid (net_label.τ_comm r q lab S) N') :
      RoundRobinTurnT N N' r (lsd ++ [net_label.τ_comm r q lab S])
  | skip {N Nmid r lsd}
      (hTrace : RoundRobinDrainTraceT N Nmid r lsd)
      (hQuies : rr_quiescent Nmid r)
      (hAbs : ∀ (q : Role) (lab : Lab) (S : DataSort) (N2 : Network),
        ¬ net_trans Nmid (net_label.τ_comm r q lab S) N2) :
      RoundRobinTurnT N Nmid r lsd

/-- Turn computer (data version): drain any role, then apply the policy.
    Same hypotheses as `turnCompute` — the `Prop`-form drain
    preservation feeds via `forget`, so existing policy instances
    (e.g. `advR2Pol`) port without change. -/
lemma turn_compute_t (N : Network) (r : Role) (hWF : N.WellFormed)
    (Inv : Network → Prop) (hInvN : Inv N)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) :
    ∃ N', ∃ ls, ∃ _ : RoundRobinTurnT N N' r ls, N'.WellFormed ∧ Inv N' := by
  obtain ⟨Nmid, lsd, hTrace, hQuies⟩ := rr_drain_trace_compute_t N r hWF
  have hWFmid : Nmid.WellFormed := hTrace.preserves hWF
  have hInvMid : Inv Nmid := hInvDrain hWF hInvN hTrace.forget
  rcases pol r Nmid hInvMid hWFmid hQuies with
    ⟨q, lab, S, N', hStep, hInv'⟩ | habs
  · exact ⟨N', lsd ++ [net_label.τ_comm r q lab S],
      RoundRobinTurnT.fire q lab S hTrace hQuies hStep,
      Network.wellFormedPreserved _ _ _ hWFmid hStep (by trivial), hInv'⟩
  · exact ⟨Nmid, lsd, RoundRobinTurnT.skip hTrace hQuies habs, hWFmid, hInvMid⟩

/-- Turn endpoint as data (the `N'` index). Needed wherever a
    proof must identify a cased turn's endpoint with a projection
    term — casing a projection loses the link, so the identity
    `turnEndEq` is threaded as data from `turnNext` instead. -/
def turnEnd : ∀ {N N' : Network} {r : Role} {ls : List net_label},
    RoundRobinTurnT N N' r ls → Network
  | _, _, _, _, @RoundRobinTurnT.fire _ _ N' _ _ _ _ _ _ _ _ => N'
  | _, _, _, _, @RoundRobinTurnT.skip _ Nmid _ _ _ _ _ => Nmid

/-- Drain endpoint as data (pre-send landing for `fire`, turn endpoint
    for `skip`). Quiescence/absence live here. -/
def turnDrainEnd : ∀ {N N' : Network} {r : Role} {ls : List net_label},
    RoundRobinTurnT N N' r ls → Network
  | _, _, _, _, @RoundRobinTurnT.fire _ Nmid _ _ _ _ _ _ _ _ _ => Nmid
  | _, _, _, _, @RoundRobinTurnT.skip _ Nmid _ _ _ _ _ => Nmid

/-- Turn computer with the endpoint equation (Prop-level: the
    object and endpoint are free variables here, so casing preserves
    their link — the fact G3 rewrites with downstream). -/
theorem turn_compute_t_spec (N : Network) (r : Role) (hWF : N.WellFormed)
    (Inv : Network → Prop) (hInvN : Inv N)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) :
    ∃ N', ∃ ls, ∃ o : RoundRobinTurnT N N' r ls,
      turnEnd o = N' ∧ N'.WellFormed ∧ Inv N' := by
  obtain ⟨N', ls, o, hWFo, hInvo⟩ := turn_compute_t N r hWF Inv hInvN hInvDrain pol
  refine ⟨N', ls, o, ?_, hWFo, hInvo⟩
  cases o with
  | fire _ _ _ _ _ _ => rfl
  | skip _ _ _ => rfl

/-- Single-turn choice function: bundle endpoint, labels, turn object,
    and endpoint equation as DATA (subtype over a data-only `Sigma`;
    triple `indefiniteDescription` over `turn_compute_t_spec` — the
    choice-iteration step). Proof arguments are proof-irrelevant, so
    calls at the same `(N, r)` agree definitionally regardless of
    which `hWF`/`hInvN` proofs flow in downstream. -/
noncomputable def turnNext (N : Network) (r : Role) (hWF : N.WellFormed)
    (Inv : Network → Prop) (hInvN : Inv N)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) :
    { t : Σ N', Σ ls, RoundRobinTurnT N N' r ls //
      turnEnd t.2.2 = t.1 ∧ t.1.WellFormed ∧ Inv t.1 } :=
  let h := turn_compute_t_spec N r hWF Inv hInvN hInvDrain pol
  let d1 := Classical.indefiniteDescription
    (fun N' => ∃ ls, ∃ o : RoundRobinTurnT N N' r ls,
      turnEnd o = N' ∧ N'.WellFormed ∧ Inv N') h
  let d2 := Classical.indefiniteDescription
    (fun ls => ∃ o : RoundRobinTurnT N d1.1 r ls,
      turnEnd o = d1.1 ∧ d1.1.WellFormed ∧ Inv d1.1) d1.2
  let d3 := Classical.indefiniteDescription
    (fun o : RoundRobinTurnT N d1.1 r d2.1 =>
      turnEnd o = d1.1 ∧ d1.1.WellFormed ∧ Inv d1.1) d2.2
  ⟨⟨d1.1, d2.1, d3.1⟩, d3.2⟩

/-- Iterated turn boundaries: `turnData n` is the network after `n`
    turns cycling through `round_robin_roles Ni`, with WF and invariant threaded
    (each step via `turnNext` at that turn's role). -/
noncomputable def turnData (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni) :
    ℕ → { N : Network // N.WellFormed ∧ Inv N }
  | 0 => ⟨Ni, hWF0, hInv0⟩
  | n + 1 =>
    let cur := turnData Ni Inv hInvDrain pol hWF0 hInv0 n
    let nxt := turnNext cur.1 (round_robin_role_at Ni n) cur.2.1 Inv cur.2.2 hInvDrain pol
    ⟨nxt.1.1, nxt.2.2.1, nxt.2.2.2⟩

/-- Network after `n` turns (projection; G3 flattens between these). -/
noncomputable def turnState (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (n : ℕ) : Network :=
  (turnData Ni Inv hInvDrain pol hWF0 hInv0 n).1

/-- WF threads through the iteration. -/
theorem turn_wf (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (n : ℕ) : (turnState Ni Inv hInvDrain pol hWF0 hInv0 n).WellFormed :=
  (turnData Ni Inv hInvDrain pol hWF0 hInv0 n).2.1

/-- Invariant threads through the iteration. -/
theorem turn_inv (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (n : ℕ) : Inv (turnState Ni Inv hInvDrain pol hWF0 hInv0 n) :=
  (turnData Ni Inv hInvDrain pol hWF0 hInv0 n).2.2

/-- Turn-`n` package: endpoint, labels, turn object (with intra-turn
    drain data for G3), and preservation — all from one `turnNext`
    call at the turn-`n` state and role. -/
noncomputable def turnStep (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (n : ℕ) :
    { t : Σ N', Σ ls, RoundRobinTurnT (turnState Ni Inv hInvDrain pol hWF0 hInv0 n) N'
        (round_robin_role_at Ni n) ls //
      turnEnd t.2.2 = t.1 ∧ t.1.WellFormed ∧ Inv t.1 } :=
  turnNext (turnState Ni Inv hInvDrain pol hWF0 hInv0 n) (round_robin_role_at Ni n)
    (turn_wf Ni Inv hInvDrain pol hWF0 hInv0 n) Inv
    (turn_inv Ni Inv hInvDrain pol hWF0 hInv0 n) hInvDrain pol

/-- Coherence: turn-`n`'s endpoint IS the turn-`n+1` state (both unfold
    to the same `turnNext` call; proof arguments agree by proof
    irrelevance). -/
theorem turn_state_succ (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (n : ℕ) :
    turnState Ni Inv hInvDrain pol hWF0 hInv0 (n + 1) =
      (turnStep Ni Inv hInvDrain pol hWF0 hInv0 n).1.1 := by
  simp only [turnState, turnData, turnStep]

/-- Drain-relative networks: position `i` in `[0, lsd.length]` along the
    trace (beyond-end sticks at the endpoint, by the `refl` arm).
    The `preSeqL` dispatch shape: split on trace *and* position. -/
def traceNet : ∀ {N Nmid : Network} {r : Role} {lsd : List net_label},
    RoundRobinDrainTraceT N Nmid r lsd → ℕ → Network
  | _, _, _, _, @RoundRobinDrainTraceT.refl N _, _ => N
  | _, _, _, _, @RoundRobinDrainTraceT.step N1 _ _ _ _ _ _ _ _ hTail, 0 => N1
  | _, _, _, _, @RoundRobinDrainTraceT.step _ _ _ _ _ _ _ _ _ hTail, (i + 1) =>
    traceNet hTail i

/-- Drain-relative labels with explicit default (hit exactly at and
    past the drain end; valid positions never see it). -/
def traceLblD (dflt : net_label) :
    ∀ {N Nmid : Network} {r : Role} {lsd : List net_label},
    RoundRobinDrainTraceT N Nmid r lsd → ℕ → net_label
  | _, _, _, _, @RoundRobinDrainTraceT.refl _ _, _ => dflt
  | _, _, _, _, @RoundRobinDrainTraceT.step _ _ _ r p lab S _ _ hTail, 0 =>
    net_label.τ_dequeue r p lab S
  | _, _, _, _, @RoundRobinDrainTraceT.step _ _ _ _ _ _ _ _ _ hTail, (i + 1) =>
    traceLblD dflt hTail i

/-- Position 0 is the start. -/
theorem trace_net_zero {N Nmid : Network} {r : Role} {lsd : List net_label}
    (t : RoundRobinDrainTraceT N Nmid r lsd) : traceNet t 0 = N := by
  cases t with
  | refl => simp only [traceNet]
  | step => simp only [traceNet]

/-- The length field agrees with the label list. -/
theorem trace_len_eq {N Nmid : Network} {r : Role} {lsd : List net_label}
    (t : RoundRobinDrainTraceT N Nmid r lsd) : t.length = lsd.length := by
  induction t with
  | refl => simp [RoundRobinDrainTraceT.length]
  | step _ hTail ih => simp [RoundRobinDrainTraceT.length, ih]

/-- Draining to the end reaches the endpoint (via the length
    equation: trade `lsd.length` for `t.length`, then the length and
    dispatch equations compute in lockstep). -/
theorem trace_net_end {N Nmid : Network} {r : Role} {lsd : List net_label}
    (t : RoundRobinDrainTraceT N Nmid r lsd) : traceNet t lsd.length = Nmid := by
  rw [← trace_len_eq t]
  induction t with
  | refl => simp [traceNet, RoundRobinDrainTraceT.length]
  | step _ hTail ih =>
    simp only [RoundRobinDrainTraceT.length, traceNet]
    exact ih

/-- Succ positions step into the tail (variable-`i` succ form matches
    the dispatch equation directly — no arithmetic normalization). -/
theorem trace_net_step_succ {N1 N2 N3 : Network} {r p : Role} {lab : Lab}
    {S : DataSort} {ls : List net_label}
    (h : net_trans N1 (net_label.τ_dequeue r p lab S) N2)
    (hTail : RoundRobinDrainTraceT N2 N3 r ls) (i : ℕ) :
    traceNet (RoundRobinDrainTraceT.step h hTail) (i + 1) = traceNet hTail i := by
  simp only [traceNet]

/-- Step evidence at every valid position (dispatch: `refl`
    is vacuous by length, `step`-zero is the head step, `step`-succ is
    the IH — induction generalizing the position). -/
theorem trace_step {N Nmid : Network} {r : Role} {lsd : List net_label}
    (t : RoundRobinDrainTraceT N Nmid r lsd) (dflt : net_label) (i : ℕ)
    (hi : i < lsd.length) :
    ∃ (N1 N2 : Network) (p : Role) (lab : Lab) (S : DataSort),
      traceNet t i = N1 ∧ traceLblD dflt t i = net_label.τ_dequeue r p lab S ∧
      traceNet t (i + 1) = N2 ∧ net_trans N1 (net_label.τ_dequeue r p lab S) N2 := by
  induction t generalizing i with
  | refl =>
    simp at hi
  | @step N1 N2 _ _ p lab S _ h hTail ih =>
    cases i with
    | zero =>
      refine ⟨N1, N2, p, lab, S, by simp only [traceNet],
        by simp only [traceLblD], ?_, h⟩
      rw [trace_net_step_succ]
      exact trace_net_zero hTail
    | succ i =>
      simp at hi
      obtain ⟨M1, M2, p', lab', S', e1, e2, e3, hS⟩ := ih i hi
      exact ⟨M1, M2, p', lab', S', by simpa [traceNet] using e1,
        by simpa [traceLblD] using e2, by simpa [traceNet] using e3, hS⟩

/-- WF at every drain position (head WF feeds the step, then the IH). -/
theorem trace_wf {N Nmid : Network} {r : Role} {lsd : List net_label}
    (t : RoundRobinDrainTraceT N Nmid r lsd) (hWF : N.WellFormed) (i : ℕ) :
    (traceNet t i).WellFormed := by
  induction t generalizing i with
  | refl =>
    cases i with
    | zero => simpa [traceNet] using hWF
    | succ i => simpa [traceNet] using hWF
  | @step N1 N2 _ _ _ _ _ _ h hTail ih =>
    cases i with
    | zero => simpa [traceNet] using hWF
    | succ i =>
      simp only [traceNet]
      exact ih (Network.wellFormedPreserved _ _ _ hWF h (by trivial)) i

/-- Default label reached exactly at the drain end. -/
theorem trace_lbl_d_end (dflt : net_label) {N Nmid : Network} {r : Role}
    {lsd : List net_label} (t : RoundRobinDrainTraceT N Nmid r lsd) :
    traceLblD dflt t t.length = dflt := by
  induction t with
  | refl => simp [traceLblD, RoundRobinDrainTraceT.length]
  | step _ hTail ih =>
    simp only [RoundRobinDrainTraceT.length, traceLblD]
    exact ih

/-- Turn-relative networks: drain positions from the trace, past the
    drain the send landing (`fire`) or the drain end (`skip`, which is
    the turn endpoint). -/
def turnRelSeq : ∀ {N N' : Network} {r : Role} {ls : List net_label},
    RoundRobinTurnT N N' r ls → ℕ → Network
  | _, _, _, _, @RoundRobinTurnT.fire _ _ N' _ lsd _ _ _ hTrace _ _, i =>
    if i ≤ lsd.length then traceNet hTrace i else N'
  | _, _, _, _, @RoundRobinTurnT.skip _ _ _ _ hTrace _ _, i => traceNet hTrace i

/-- Turn-relative labels: drain labels from the trace, at/past the
    drain end the send label (`fire`) or a dummy (`skip`, never
    queried at a valid position of an empty turn). -/
def turnRelLbl : ∀ {N N' : Network} {r : Role} {ls : List net_label},
    RoundRobinTurnT N N' r ls → ℕ → net_label
  | _, _, _, _, @RoundRobinTurnT.fire _ _ _ r _ q lab S hTrace _ _, i =>
    traceLblD (net_label.τ_comm r q lab S) hTrace i
  | _, _, _, _, @RoundRobinTurnT.skip _ _ _ _ hTrace _ _, i =>
    traceLblD (net_label.τ_comm "" "" "" "") hTrace i

/-- Micro-steps contributed by a turn (drains + optional send). -/
def turnSteps : ∀ {N N' : Network} {r : Role} {ls : List net_label},
    RoundRobinTurnT N N' r ls → ℕ
  | _, _, _, _, @RoundRobinTurnT.fire _ _ _ _ _ _ _ _ hTrace _ _ =>
    hTrace.length + 1
  | _, _, _, _, @RoundRobinTurnT.skip _ _ _ _ hTrace _ _ => hTrace.length

/-- Drain part of a turn (for `dend`). -/
def turnDrainLen : ∀ {N N' : Network} {r : Role} {ls : List net_label},
    RoundRobinTurnT N N' r ls → ℕ
  | _, _, _, _, @RoundRobinTurnT.fire _ _ _ _ _ _ _ _ hTrace _ _ => hTrace.length
  | _, _, _, _, @RoundRobinTurnT.skip _ _ _ _ hTrace _ _ => hTrace.length

/-- Whether the turn fires its send. -/
def turnIsFire : ∀ {N N' : Network} {r : Role} {ls : List net_label},
    RoundRobinTurnT N N' r ls → Bool
  | _, _, _, _, @RoundRobinTurnT.fire _ _ _ _ _ _ _ _ _ _ _ => true
  | _, _, _, _, @RoundRobinTurnT.skip _ _ _ _ _ _ _ => false

/-- Relative position 0 is the turn start. -/
theorem turn_rel_seq_zero {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) : turnRelSeq o 0 = N := by
  cases o with
  | fire _ _ _ hTrace _ _ => simp [turnRelSeq, trace_net_zero]
  | skip hTrace _ _ => simp [turnRelSeq, trace_net_zero]

/-- `fire` turns land on the endpoint past the drain+send. -/
theorem turn_rel_seq_end_fire {N Nmid N' : Network} {r : Role}
    {lsd : List net_label} {q : Role} {lab : Lab} {S : DataSort}
    (hTrace : RoundRobinDrainTraceT N Nmid r lsd)
    (hQuies : rr_quiescent Nmid r)
    (hStep : net_trans Nmid (net_label.τ_comm r q lab S) N') :
    turnRelSeq (RoundRobinTurnT.fire q lab S hTrace hQuies hStep)
      (hTrace.length + 1) = N' := by
  simp only [turnRelSeq]
  exact if_neg (by rw [trace_len_eq hTrace]; omega)

/-- `skip` turns end at the drain endpoint. -/
theorem turn_rel_seq_end_skip {N Nmid : Network} {r : Role}
    {lsd : List net_label} (hTrace : RoundRobinDrainTraceT N Nmid r lsd)
    (hQuies : rr_quiescent Nmid r)
    (hAbs : ∀ (q : Role) (lab : Lab) (S : DataSort) (N2 : Network),
      ¬ net_trans Nmid (net_label.τ_comm r q lab S) N2) :
    turnRelSeq (RoundRobinTurnT.skip hTrace hQuies hAbs) hTrace.length = Nmid := by
  simp only [turnRelSeq]
  rw [trace_len_eq hTrace]
  exact trace_net_end hTrace

/-- Every turn ends on its endpoint. -/
theorem turn_rel_seq_end' {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) : turnRelSeq o (turnSteps o) = N' := by
  cases o with
  | fire _ _ _ hTrace _ _ =>
    simp only [turnSteps]
    exact turn_rel_seq_end_fire _ _ _
  | skip hTrace _ _ =>
    simp only [turnSteps]
    exact turn_rel_seq_end_skip _ _ _

/-- Stepless turns are stationary. -/
theorem turn_empty_state {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) (h0 : turnSteps o = 0) : N' = N := by
  cases o with
  | fire _ _ _ hTrace _ _ =>
    simp only [turnSteps] at h0
    omega
  | skip hTrace _ _ =>
    simp only [turnSteps] at h0
    rw [trace_len_eq hTrace] at h0
    exact hTrace.nil_eq (List.length_eq_zero_iff.mp h0)

/-- Relative steps inside a turn (drain positions by `trace_step`,
    the send position by endpoint evidence). -/
theorem turn_rel_tr {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) (hWF : N.WellFormed)
    (i : ℕ) (hi : i < turnSteps o) :
    net_trans (turnRelSeq o i) (turnRelLbl o i) (turnRelSeq o (i + 1)) := by
  cases o with
  | fire q lab S hTrace hQuies hStep =>
    simp only [turnSteps] at hi
    by_cases hd : i < hTrace.length
    · rw [trace_len_eq hTrace] at hd
      obtain ⟨M1, M2, p', lab', S', e1, e2, e3, hS⟩ :=
        trace_step hTrace _ i hd
      simp only [turnRelSeq, turnRelLbl]
      rw [if_pos (Nat.le_of_lt hd), if_pos (by omega : i + 1 ≤ _)]
      rw [e1, e2, e3]
      exact hS
    · have hi0 : i = hTrace.length := by omega
      subst hi0
      simp only [turnRelSeq, turnRelLbl]
      rw [trace_lbl_d_end _ hTrace]
      rw [trace_len_eq hTrace]
      rw [if_pos (le_refl _), if_neg (by omega)]
      rw [trace_net_end hTrace]
      exact hStep
  | skip hTrace hQuies hAbs =>
    simp only [turnSteps] at hi
    simp only [turnRelSeq, turnRelLbl]
    rw [trace_len_eq hTrace] at hi
    obtain ⟨M1, M2, p', lab', S', e1, e2, e3, hS⟩ :=
      trace_step hTrace (net_label.τ_comm "" "" "" "") i hi
    rw [e1, e2, e3]
    exact hS

/-- Prefix-sum turn boundaries: micro-steps before turn `j`. -/
noncomputable def turnBound (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni) :
    ℕ → ℕ
  | 0 => 0
  | j + 1 => turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
      turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2

/-- Bounds start at 0. -/
theorem turn_b0 (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni) :
    turnBound Ni Inv hInvDrain pol hWF0 hInv0 0 = 0 :=
  rfl

/-- One more turn never moves the bound backwards. -/
theorem turn_bound_succ (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (j : ℕ) :
    turnBound Ni Inv hInvDrain pol hWF0 hInv0 j ≤
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) := by
  simp only [turnBound]
  exact Nat.le_add_right _ _

/-- Bounds are monotone. -/
theorem turn_bmono (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni) :
    Monotone (turnBound Ni Inv hInvDrain pol hWF0 hInv0) := by
  intro a b h
  obtain ⟨c, rfl⟩ := Nat.le.dest h
  clear h
  induction c with
  | zero => exact Nat.le_refl _
  | succ c ih =>
    have h2 : a + (c + 1) = (a + c) + 1 := by omega
    rw [h2]
    exact Nat.le_trans ih
      (turn_bound_succ Ni Inv hInvDrain pol hWF0 hInv0 _)

/-- Block cover below a bound: every index under a bound lies in a
    turn block (verbatim port of `rr_cover_below`). -/
theorem turn_cover_has (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (k J : ℕ)
    (h : k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 J) :
    ∃ j, j < J ∧ turnBound Ni Inv hInvDrain pol hWF0 hInv0 j ≤ k ∧
      k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) := by
  have hex : ∃ m, k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 m := ⟨J, h⟩
  have hMspec : k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 (Nat.find hex) :=
    Nat.find_spec hex
  have hMmin : ∀ m, k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 m →
      Nat.find hex ≤ m :=
    fun m hm => Nat.find_min' hex hm
  have hMJ : Nat.find hex ≤ J := hMmin J h
  have hMpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exfalso
      rw [h0, turn_b0 Ni Inv hInvDrain pol hWF0 hInv0] at hMspec
      omega
    · exact hpos
  refine ⟨Nat.find hex - 1, by omega, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    have := hMmin _ hcon
    omega
  · have hEq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hEq]
    exact hMspec

/-- Block of micro-index `k` (with its bounds proof): choice over the
    cover witness — the flattening dispatch. -/
noncomputable def flatBlk (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (k : ℕ) :
    { j : ℕ // turnBound Ni Inv hInvDrain pol hWF0 hInv0 j ≤ k ∧
      k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) } :=
  Classical.indefiniteDescription
    (fun j => turnBound Ni Inv hInvDrain pol hWF0 hInv0 j ≤ k ∧
      k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1))
    (by
      obtain ⟨J, hJ⟩ := hUnbdd (k + 1)
      obtain ⟨j, _, hj1, hj2⟩ := turn_cover_has Ni Inv hInvDrain pol hWF0 hInv0
        k J (by omega)
      exact ⟨j, hj1, hj2⟩)

/-- Flattened networks: turn-relative dispatch at the block. -/
noncomputable def flatSeq (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (k : ℕ) : Network :=
  let j := (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).1
  turnRelSeq (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2
    (k - turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)

/-- Flattened labels: turn-relative dispatch at the block. -/
noncomputable def flatLbl (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (k : ℕ) : net_label :=
  let j := (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).1
  turnRelLbl (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2
    (k - turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)

/-- A bound-flat step preserves the state. -/
theorem turn_state_step_of_bound_eq (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (t : ℕ)
    (h : turnBound Ni Inv hInvDrain pol hWF0 hInv0 t =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 (t + 1)) :
    turnState Ni Inv hInvDrain pol hWF0 hInv0 (t + 1) =
      turnState Ni Inv hInvDrain pol hWF0 hInv0 t := by
  have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (t + 1) =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 t +
        turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 t).1.2.2 := by
    simp only [turnBound]
  have hS : turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 t).1.2.2 = 0 := by
    omega
  have hE : (turnStep Ni Inv hInvDrain pol hWF0 hInv0 t).1.1 =
      turnState Ni Inv hInvDrain pol hWF0 hInv0 t :=
    turn_empty_state _ hS
  rw [turn_state_succ]
  exact hE

/-- One-sided constancy: equal bounds over `a ≤ b` mean equal states
    (induction on the inequality proof; the bounds equation threads
    through the motive). -/
theorem turn_state_const_le (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (a b : ℕ) (hle : a ≤ b)
    (h : turnBound Ni Inv hInvDrain pol hWF0 hInv0 a =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 b) :
    turnState Ni Inv hInvDrain pol hWF0 hInv0 a =
      turnState Ni Inv hInvDrain pol hWF0 hInv0 b := by
  induction b generalizing a with
  | zero =>
    have ha0 : a = 0 := Nat.eq_zero_of_le_zero hle
    subst ha0
    rfl
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · have hle' : a ≤ b := by omega
      have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (b + 1) =
          turnBound Ni Inv hInvDrain pol hWF0 hInv0 b +
            turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 b).1.2.2 := by
        simp only [turnBound]
      have hle2 : turnBound Ni Inv hInvDrain pol hWF0 hInv0 a ≤
          turnBound Ni Inv hInvDrain pol hWF0 hInv0 b :=
        turn_bmono Ni Inv hInvDrain pol hWF0 hInv0 hle'
      have hbb : turnBound Ni Inv hInvDrain pol hWF0 hInv0 a =
          turnBound Ni Inv hInvDrain pol hWF0 hInv0 b := by omega
      have e1 : turnState Ni Inv hInvDrain pol hWF0 hInv0 a =
          turnState Ni Inv hInvDrain pol hWF0 hInv0 b := ih a hle' hbb
      have e2 : turnState Ni Inv hInvDrain pol hWF0 hInv0 (b + 1) =
          turnState Ni Inv hInvDrain pol hWF0 hInv0 b :=
        turn_state_step_of_bound_eq Ni Inv hInvDrain pol hWF0 hInv0 _ (by omega)
      exact e1.trans e2.symm
    · subst heq
      rfl

/-- Equal bounds mean equal states. -/
theorem turn_state_const (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (a b : ℕ)
    (h : turnBound Ni Inv hInvDrain pol hWF0 hInv0 a =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 b) :
    turnState Ni Inv hInvDrain pol hWF0 hInv0 a =
      turnState Ni Inv hInvDrain pol hWF0 hInv0 b := by
  rcases le_total a b with hle | hle
  · exact turn_state_const_le Ni Inv hInvDrain pol hWF0 hInv0 a b hle h
  · exact (turn_state_const_le Ni Inv hInvDrain pol hWF0 hInv0 b a hle h.symm).symm

/-- Blocks are unique: two blocks covering `k` coincide (the
    `RoundRobinRun` cover argument at turn level). -/
theorem flat_blk_unique (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (a b k : ℕ)
    (ha1 : turnBound Ni Inv hInvDrain pol hWF0 hInv0 a ≤ k)
    (ha2 : k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 (a + 1))
    (hb1 : turnBound Ni Inv hInvDrain pol hWF0 hInv0 b ≤ k)
    (hb2 : k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 (b + 1)) :
    a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · exfalso
    have hle : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (a + 1) ≤
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 b :=
      turn_bmono Ni Inv hInvDrain pol hWF0 hInv0 (by omega)
    omega
  · exact h
  · exfalso
    have hle : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (b + 1) ≤
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 a :=
      turn_bmono Ni Inv hInvDrain pol hWF0 hInv0 (by omega)
    omega

/-- Unfolding equations for the flattened functions. -/
theorem flat_seq_unfold (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (k : ℕ) :
    flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k =
      turnRelSeq (turnStep Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).1).1.2.2
        (k - turnBound Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).1) :=
  rfl

/-- The flattened schedule label unfolds one turn step: definitionally the turn relation's label at
   the post-bound offset. -/
theorem flat_lbl_unfold (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (k : ℕ) :
    flatLbl Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k =
      turnRelLbl (turnStep Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).1).1.2.2
        (k - turnBound Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).1) :=
  rfl

/-- Flattened networks agree with turn states at boundaries. -/
theorem flat_seq_at_bound (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (j : ℕ) :
    flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
        (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j) =
      turnState Ni Inv hInvDrain pol hWF0 hInv0 j := by
  have hj1 := (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
    (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).2.1
  have hje : j ≤ (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
      (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).1 := by
    by_contra hcon
    push Not at hcon
    have hle : turnBound Ni Inv hInvDrain pol hWF0 hInv0
        ((flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
          (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).1 + 1) ≤
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j :=
      turn_bmono Ni Inv hInvDrain pol hWF0 hInv0 (by omega)
    have hj2 := (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
      (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).2.2
    omega
  have hBeq : turnBound Ni Inv hInvDrain pol hWF0 hInv0
      (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
        (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).1 =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 j := by
    have hle : turnBound Ni Inv hInvDrain pol hWF0 hInv0 j ≤
        turnBound Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
            (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).1 :=
      turn_bmono Ni Inv hInvDrain pol hWF0 hInv0 hje
    omega
  have hr0 : turnBound Ni Inv hInvDrain pol hWF0 hInv0 j -
      turnBound Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
          (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).1 = 0 := by omega
  rw [flat_seq_unfold, hr0]
  have hz : turnRelSeq (turnStep Ni Inv hInvDrain pol hWF0 hInv0
      (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
        (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).1).1.2.2 0 =
      turnState Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
          (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)).1 :=
    turn_rel_seq_zero _
  rw [hz]
  exact turn_state_const Ni Inv hInvDrain pol hWF0 hInv0 _ _ hBeq

/-- Flattened start is the initial network. -/
theorem flat_seq_zero (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j) :
    flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd 0 = Ni := by
  have h0 := flat_seq_at_bound Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd 0
  rw [turn_b0 Ni Inv hInvDrain pol hWF0 hInv0] at h0
  have hS : turnState Ni Inv hInvDrain pol hWF0 hInv0 0 = Ni := rfl
  rw [hS] at h0
  exact h0

/-- WF at every turn-relative position. -/
theorem turn_rel_seq_wf {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) (hWF : N.WellFormed) (i : ℕ) :
    (turnRelSeq o i).WellFormed := by
  cases o with
  | fire q lab S hTrace hQuies hStep =>
    simp only [turnRelSeq]
    by_cases hc : i ≤ hTrace.length
    · rw [if_pos (trace_len_eq hTrace ▸ hc)]
      exact trace_wf hTrace hWF _
    · have hc' : ¬ i ≤ _ := trace_len_eq hTrace ▸ hc
      rw [if_neg hc']
      have hWFM := by
        have hw := trace_wf hTrace hWF hTrace.length
        rw [trace_len_eq hTrace] at hw
        rw [trace_net_end hTrace] at hw
        exact hw
      exact Network.wellFormedPreserved _ _ _ hWFM hStep (by trivial)
  | skip hTrace hQuies hAbs =>
    simp only [turnRelSeq]
    exact trace_wf hTrace hWF _

/-- Relative drain end is the drain endpoint. -/
theorem turn_rel_seq_drain_end {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) :
    turnRelSeq o (turnDrainLen o) = turnDrainEnd o := by
  cases o with
  | fire q lab S hTrace hQuies hStep =>
    have hle := Nat.le_of_eq (trace_len_eq hTrace)
    have eL : turnRelSeq (RoundRobinTurnT.fire q lab S hTrace hQuies hStep)
        (turnDrainLen (RoundRobinTurnT.fire q lab S hTrace hQuies hStep)) =
        traceNet hTrace hTrace.length := by
      simp only [turnDrainLen, turnRelSeq]
      exact if_pos hle
    rw [eL, trace_len_eq hTrace]
    exact trace_net_end hTrace
  | skip hTrace _ _ =>
    simp only [turnDrainLen, turnRelSeq, turnDrainEnd]
    rw [trace_len_eq hTrace]
    exact trace_net_end hTrace

/-- Drain-relative labels are dequeues of the turn role. -/
theorem turn_rel_lbl_drain {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) (i : ℕ)
    (hi : i < turnDrainLen o) :
    ∃ p lab S, turnRelLbl o i = net_label.τ_dequeue r p lab S := by
  cases o with
  | fire q lab S hTrace _ _ =>
    simp only [turnDrainLen] at hi
    simp only [turnRelLbl]
    rw [trace_len_eq hTrace] at hi
    obtain ⟨_, _, p', lab', S', _, e2, _, _⟩ := trace_step hTrace _ i hi
    exact ⟨p', lab', S', e2⟩
  | skip hTrace _ _ =>
    simp only [turnDrainLen] at hi
    simp only [turnRelLbl]
    rw [trace_len_eq hTrace] at hi
    obtain ⟨_, _, p', lab', S', _, e2, _, _⟩ :=
      trace_step hTrace (net_label.τ_comm "" "" "" "") i hi
    exact ⟨p', lab', S', e2⟩

/-- Endpoint-identity accessor: the turn object's endpoint IS the
    chosen endpoint (the bridge G3 rewrites with instead of casing
    projections). -/
theorem turn_step_end_eq (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (j : ℕ) :
    turnEnd (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
      (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.1 :=
  (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).2.1

/-- On non-firing turns the endpoints coincide. -/
theorem turn_end_skip_eq_drain {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) (h : turnIsFire o = false) :
    turnEnd o = turnDrainEnd o := by
  cases o with
  | fire _ _ _ _ _ _ => simp [turnIsFire] at h
  | skip _ _ _ => simp only [turnEnd, turnDrainEnd]

/-- Drain never exceeds steps. -/
theorem turn_drain_len_le_steps {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) : turnDrainLen o ≤ turnSteps o := by
  cases o with
  | fire _ _ _ hTrace _ _ => simp only [turnDrainLen, turnSteps]; omega
  | skip _ _ _ => simp only [turnDrainLen, turnSteps]; omega

/-- Firing turns add exactly the send. -/
theorem turn_drain_len_succ_of_fire {N N' : Network} {r : Role}
    {ls : List net_label} (o : RoundRobinTurnT N N' r ls)
    (h : turnIsFire o = true) :
    turnDrainLen o + 1 = turnSteps o := by
  cases o with
  | fire _ _ _ hTrace _ _ => simp only [turnDrainLen, turnSteps]
  | skip _ _ _ => simp [turnIsFire] at h

/-- Non-firing turns are drain-only. -/
theorem turn_steps_eq_drain_of_skip {N N' : Network} {r : Role}
    {ls : List net_label} (o : RoundRobinTurnT N N' r ls)
    (h : turnIsFire o = false) :
    turnSteps o = turnDrainLen o := by
  cases o with
  | fire _ _ _ _ _ _ => simp [turnIsFire] at h
  | skip _ _ _ => simp only [turnDrainLen, turnSteps]

/-- The drain end is quiescent. -/
theorem turn_drain_quies {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) : rr_quiescent (turnDrainEnd o) r := by
  cases o with
  | fire _ _ _ _ hQuies _ => simpa [turnDrainEnd] using hQuies
  | skip _ hQuies _ => simpa [turnDrainEnd] using hQuies

/-- Non-firing turns decline every send at the drain end. -/
theorem turn_skip_abs {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) (h : turnIsFire o = false) :
    ∀ (q : Role) (lab : Lab) (S : DataSort) (N2 : Network),
      ¬ net_trans (turnDrainEnd o) (net_label.τ_comm r q lab S) N2 := by
  cases o with
  | fire _ _ _ _ _ _ => simp [turnIsFire] at h
  | skip _ _ hAbs =>
    intro q lab S N2 hTr
    exact hAbs _ _ _ _ hTr

/-- Firing turns label the drain end with the send. -/
theorem turn_fire_lbl {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) (h : turnIsFire o = true) :
    ∃ q lab S, turnRelLbl o (turnDrainLen o) = net_label.τ_comm r q lab S := by
  cases o with
  | fire q lab S hTrace _ _ =>
    refine ⟨q, lab, S, ?_⟩
    simp only [turnDrainLen, turnRelLbl]
    exact trace_lbl_d_end _ hTrace
  | skip _ _ _ => simp [turnIsFire] at h

/-- Drain end of turn `j` (micro-index where the send, if any, fires). -/
noncomputable def turnDend (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (j : ℕ) : ℕ :=
  turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
    turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2

/-- Send flag of turn `j`. -/
noncomputable def turnSend (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (j : ℕ) : Bool :=
  turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2

/-- Fusion: the flattened successor stays in the same turn-relative
    frame (same block: uniqueness; turn end: boundary via `H1`,
    coherence, and the uniform end lemma). -/
theorem flat_seq_succ_fusion (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (i : ℕ) :
    flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd (i + 1) =
      turnRelSeq (turnStep Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1).1.2.2
        ((i - turnBound Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1) + 1) := by
  have hj1 := (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).2.1
  have hj2 := (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).2.2
  by_cases hlt : i + 1 < turnBound Ni Inv hInvDrain pol hWF0 hInv0
      ((flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 + 1)
  · have hJ' : (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd (i + 1)).1 =
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 :=
      flat_blk_unique Ni Inv hInvDrain pol hWF0 hInv0 _ _ _
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd (i + 1)).2.1
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd (i + 1)).2.2
        (le_trans (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).2.1
          (Nat.le_succ _)) hlt
    rw [flat_seq_unfold, hJ']
    have hrr : i + 1 - turnBound Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 =
        (i - turnBound Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1) + 1 := by omega
    rw [hrr]
  · have hBe : i + 1 = turnBound Ni Inv hInvDrain pol hWF0 hInv0
        ((flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 + 1) := by omega
    have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0
        ((flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 + 1) =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 +
          turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0
            (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1).1.2.2 := by
      simp only [turnBound]
    have hsr : (i - turnBound Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1) + 1 =
        turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1).1.2.2 := by omega
    have hL : flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd (i + 1) =
        turnState Ni Inv hInvDrain pol hWF0 hInv0
          ((flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 + 1) := by
      rw [hBe]
      exact flat_seq_at_bound Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd _
    have hR : turnRelSeq (turnStep Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1).1.2.2
        ((i - turnBound Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1) + 1) =
        turnState Ni Inv hInvDrain pol hWF0 hInv0
          ((flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 + 1) := by
      rw [hsr]
      exact (turn_rel_seq_end' _).trans
        (turn_state_succ Ni Inv hInvDrain pol hWF0 hInv0 _).symm
    rw [hL]
    exact hR.symm

/-- Every flattened step is genuine. -/
theorem flat_tr (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (i : ℕ) :
    net_trans (flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i)
      (flatLbl Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i)
      (flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd (i + 1)) := by
  have hj1 := (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).2.1
  have hj2 := (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).2.2
  have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0
      ((flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 + 1) =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 +
        turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1).1.2.2 := by
    simp only [turnBound]
  have hilt : i - turnBound Ni Inv hInvDrain pol hWF0 hInv0
      (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1 <
      turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1).1.2.2 := by omega
  have hObj := turn_rel_tr
    (turnStep Ni Inv hInvDrain pol hWF0 hInv0
      (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1).1.2.2
    (turn_wf Ni Inv hInvDrain pol hWF0 hInv0
      (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1)
    (i - turnBound Ni Inv hInvDrain pol hWF0 hInv0
      (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i).1) hilt
  have e3 := flat_seq_succ_fusion Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd i
  rw [e3, flat_seq_unfold, flat_lbl_unfold]
  exact hObj

/-- Every flattened state is well-formed. -/
theorem flat_wf (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (k : ℕ) :
    (flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).WellFormed := by
  rw [flat_seq_unfold]
  exact turn_rel_seq_wf _
    (turn_wf Ni Inv hInvDrain pol hWF0 hInv0
      (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).1) _

/-- Bounds sandwich the drain end. -/
theorem turn_bounds_ok (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (j : ℕ) :
    turnBound Ni Inv hInvDrain pol hWF0 hInv0 j ≤
        turnDend Ni Inv hInvDrain pol hWF0 hInv0 j ∧
      turnDend Ni Inv hInvDrain pol hWF0 hInv0 j ≤
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) := by
  have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
        turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
    simp only [turnBound]
  have hle := Nat.add_le_add_left
    (turn_drain_len_le_steps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2)
    (turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
  have hd : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
        turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := rfl
  omega

/-- Flattened drain-end states of skipped turns (used by `quies` and
    `nosend_none`: `dend` is the next boundary, routed back through
    `H1`, coherence, and the endpoint equation). -/
theorem flat_seq_dend_skip (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j)
    (j : ℕ)
    (hf0 : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
      false) :
    flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
        (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j) =
      turnDrainEnd (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
  have hde : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j =
      turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) := by
    have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
          turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
      simp only [turnBound]
    have h3 := turn_steps_eq_drain_of_skip _ hf0
    simp only [turnDend]
    omega
  rw [hde]
  have h1 := flat_seq_at_bound Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd (j + 1)
  rw [h1]
  have h2 : turnState Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) =
      turnDrainEnd (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
    have hc := turn_state_succ Ni Inv hInvDrain pol hWF0 hInv0 j
    exact hc.trans ((turn_step_end_eq Ni Inv hInvDrain pol hWF0 hInv0 j).symm.trans
      (turn_end_skip_eq_drain _ hf0))
  exact h2

/-- The assembled micro-run: flattened turns grouped into turn blocks
    (unbounded case — every bound is passed, so every micro-index has
    a block and all steps/labels come from turn-relative dispatch). -/
noncomputable def turnRun (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j) :
    RoundRobinRun Ni where
  seq := flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
  lbl := flatLbl Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
  tr := flat_tr Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
  f0 := flat_seq_zero Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
  wf := flat_wf Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
  bound := turnBound Ni Inv hInvDrain pol hWF0 hInv0
  b0 := turn_b0 Ni Inv hInvDrain pol hWF0 hInv0
  bmono := turn_bmono Ni Inv hInvDrain pol hWF0 hInv0
  dend := turnDend Ni Inv hInvDrain pol hWF0 hInv0
  send := turnSend Ni Inv hInvDrain pol hWF0 hInv0
  bounds_ok := turn_bounds_ok Ni Inv hInvDrain pol hWF0 hInv0
  drain_lbl := by
    intro j k h1 h2
    have hB2 : k < turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) :=
      lt_of_lt_of_le h2 (turn_bounds_ok Ni Inv hInvDrain pol hWF0 hInv0 j).2
    have hJ : (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).1 = j :=
      flat_blk_unique Ni Inv hInvDrain pol hWF0 hInv0 _ _ _
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).2.1
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k).2.2 h1 hB2
    have hr : k - turnBound Ni Inv hInvDrain pol hWF0 hInv0 j <
        turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
      have hd : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j =
          turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
            turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 :=
        rfl
      omega
    rw [flat_lbl_unfold, hJ]
    obtain ⟨p, lab, S, hL⟩ := turn_rel_lbl_drain _ _ hr
    exact ⟨p, lab, S, hL⟩
  send_pos := by
    intro j hs
    have hf : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
        true := hs
    have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
          turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
      simp only [turnBound]
    have h2 := turn_drain_len_succ_of_fire _ hf
    have hd : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
          turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := rfl
    omega
  send_is := by
    intro j hs
    have hf : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
        true := hs
    have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
          turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
      simp only [turnBound]
    have hlt : turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 <
        turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
      have h2 := turn_drain_len_succ_of_fire _ hf
      omega
    have hd : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
          turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := rfl
    have hJ : (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
        (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j)).1 = j :=
      flat_blk_unique Ni Inv hInvDrain pol hWF0 hInv0 _ _ _
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
          (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j)).2.1
        (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
          (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j)).2.2
        (by simp only [turnDend]; omega)
        (by omega)
    have hrel : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j -
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j =
        turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
      simp only [turnDend]
      omega
    rw [flat_lbl_unfold, hJ, hrel]
    obtain ⟨q, lab, S, hL⟩ := turn_fire_lbl _ hf
    exact ⟨q, lab, S, hL⟩
  nosend_pos := by
    intro j hs
    have hf : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
        false := hs
    have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
          turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
      simp only [turnBound]
    have h3 := turn_steps_eq_drain_of_skip _ hf
    have hd : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
          turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := rfl
    omega
  nosend_none := by
    intro j hs q lab S N2 hTr
    have hf : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
        false := hs
    have hf0 : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
        false := hs
    have hRoute : flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
        (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j) =
        turnDrainEnd (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 :=
      flat_seq_dend_skip Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd j hf0
    rw [hRoute] at hTr
    exact turn_skip_abs _ hf _ _ _ _ hTr
  quies := by
    intro j
    by_cases hf : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
        true
    · have hlt : turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 <
          turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
        have h2 := turn_drain_len_succ_of_fire _ hf
        omega
      have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 (j + 1) =
          turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
            turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
        simp only [turnBound]
      have hd : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j =
          turnBound Ni Inv hInvDrain pol hWF0 hInv0 j +
            turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 :=
        rfl
      have hJ : (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
          (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j)).1 = j :=
        flat_blk_unique Ni Inv hInvDrain pol hWF0 hInv0 _ _ _
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
            (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j)).2.1
          (flatBlk Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
            (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j)).2.2
          (by simp only [turnDend]; omega)
          (by omega)
      have hrel : turnDend Ni Inv hInvDrain pol hWF0 hInv0 j -
          turnBound Ni Inv hInvDrain pol hWF0 hInv0 j =
          turnDrainLen (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
        simp only [turnDend]
        omega
      have hRoute : flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
          (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j) =
          turnDrainEnd (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 := by
        rw [flat_seq_unfold, hJ, hrel]
        exact turn_rel_seq_drain_end _
      rw [hRoute]
      exact turn_drain_quies _
    · have hf0 : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 =
          false := by simpa using hf
      have hRoute : flatSeq Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd
          (turnDend Ni Inv hInvDrain pol hWF0 hInv0 j) =
          turnDrainEnd (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2 :=
        flat_seq_dend_skip Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd j hf0
      rw [hRoute]
      exact turn_drain_quies _

/-- Fair path from any unbounded policy run (assembly + wrapper). -/
theorem turn_run_fair (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    {hne : round_robin_roles Ni ≠ []}
    (hUnbdd : ∀ K, ∃ j, K < turnBound Ni Inv hInvDrain pol hWF0 hInv0 j) :
    ∃ path : InfiniteNetworkPath, path.seq 0 = Ni ∧ IsFair path ∧
      ∀ k, path.δ k = flatLbl Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd k := by
  obtain ⟨path, h0, hfair, hlab⟩ :=
    RoundRobinRun.toFairPath (hne := hne)
      (turnRun Ni Inv hInvDrain pol hWF0 hInv0 hUnbdd) hUnbdd
  exact ⟨path, h0, hfair, hlab⟩

/-- Stepless turns never fire. -/
theorem turn_is_fire_of_steps_eq_zero {N N' : Network} {r : Role}
    {ls : List net_label} (o : RoundRobinTurnT N N' r ls)
    (h0 : turnSteps o = 0) : turnIsFire o = false := by
  cases o with
  | fire _ _ _ _ _ _ => simp only [turnSteps] at h0; omega
  | skip _ _ _ => rfl

/-- Drain traces replay as stars. -/
theorem trace_star {N Nmid : Network} {r : Role} {lsd : List net_label}
    (t : RoundRobinDrainTraceT N Nmid r lsd) : net_trans_star N Nmid := by
  induction t with
  | refl => exact net_trans_star.refl _
  | @step N1 N2 _ r p lab S _ h hTail ih =>
    have hI : is_internal_net_label (net_label.τ_dequeue r p lab S) := True.intro
    exact net_trans_star.trans (net_trans_star.step hI h (net_trans_star.refl _)) ih

/-- Turns replay as stars landing on the turn endpoint. -/
theorem turn_step_star {N N' : Network} {r : Role} {ls : List net_label}
    (o : RoundRobinTurnT N N' r ls) : net_trans_star N (turnEnd o) := by
  cases o with
  | @fire Nmid N'' r lsd q lab S hTrace hQuies hStep =>
    have hI : is_internal_net_label (net_label.τ_comm r q lab S) := True.intro
    exact net_trans_star.trans (trace_star hTrace)
      (net_trans_star.step hI hStep (net_trans_star.refl _))
  | skip hTrace hQuies hAbs => exact trace_star hTrace

/-- Turn states are reachable from the start. -/
theorem turn_reachable (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (j : ℕ) : net_trans_star Ni (turnState Ni Inv hInvDrain pol hWF0 hInv0 j) := by
  induction j with
  | zero =>
    have h0 : turnState Ni Inv hInvDrain pol hWF0 hInv0 0 = Ni := rfl
    rw [h0]
    exact net_trans_star.refl _
  | succ j ih =>
    have hC := turn_state_succ Ni Inv hInvDrain pol hWF0 hInv0 j
    rw [hC]
    have hS := turn_step_star (turnStep Ni Inv hInvDrain pol hWF0 hInv0 j).1.2.2
    rw [turn_step_end_eq Ni Inv hInvDrain pol hWF0 hInv0 j] at hS
    exact net_trans_star.trans ih hS

/-- Empty turns are quiescent and send-free at their (preserved) state. -/
theorem turn_empty_facts (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    (t : ℕ)
    (h0 : turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 t).1.2.2 = 0) :
    rr_quiescent (turnState Ni Inv hInvDrain pol hWF0 hInv0 t) (round_robin_role_at Ni t) ∧
      (∀ q lab S N2, ¬ net_trans (turnState Ni Inv hInvDrain pol hWF0 hInv0 t)
        (net_label.τ_comm (round_robin_role_at Ni t) q lab S) N2) := by
  have hf0 : turnIsFire (turnStep Ni Inv hInvDrain pol hWF0 hInv0 t).1.2.2 =
      false :=
    turn_is_fire_of_steps_eq_zero _ h0
  have hE : turnState Ni Inv hInvDrain pol hWF0 hInv0 t =
      turnDrainEnd (turnStep Ni Inv hInvDrain pol hWF0 hInv0 t).1.2.2 := by
    have hEs := turn_empty_state _ h0
    have hEe := turn_step_end_eq Ni Inv hInvDrain pol hWF0 hInv0 t
    have hEk := turn_end_skip_eq_drain _ hf0
    exact hEs.symm.trans (hEe.symm.trans hEk)
  refine ⟨?_, ?_⟩
  · rw [hE]
    exact turn_drain_quies _
  · intro q lab S N2 hTr
    rw [hE] at hTr
    exact turn_skip_abs _ hf0 _ _ _ _ hTr

/-- Stuck arm: bounded bounds stabilize into a full cycle of empty
    turns, so the stabilized state admits no internal step (a full cycle
    of empty turns ends stuck, at turn level). -/
theorem turn_run_stuck (Ni : Network) (Inv : Network → Prop)
    (hInvDrain : ∀ {N1 N2 : Network} {r : Role} {ls : List net_label},
      N1.WellFormed → Inv N1 → rr_drain_trace N1 N2 r ls → Inv N2)
    (pol : turn_policy Inv) (hWF0 : Ni.WellFormed) (hInv0 : Inv Ni)
    {hne : round_robin_roles Ni ≠ []}
    (hBdd : ∃ K, ∀ j, turnBound Ni Inv hInvDrain pol hWF0 hInv0 j ≤ K) :
    ∃ Nst, IsStuckNetwork Nst ∧ net_trans_star Ni Nst ∧ Inv Nst := by
  obtain ⟨K, hK⟩ := hBdd
  obtain ⟨J, hJ⟩ := rr_bounded_const
    (turn_bmono Ni Inv hInvDrain pol hWF0 hInv0) ⟨K, hK⟩
  have hReach := turn_reachable Ni Inv hInvDrain pol hWF0 hInv0 J
  refine ⟨turnState Ni Inv hInvDrain pol hWF0 hInv0 J, ?_,
    hReach, turn_inv Ni Inv hInvDrain pol hWF0 hInv0 J⟩
  intro h
  obtain ⟨δ, N', hInt, hTr⟩ := h
  have hempty : ∀ t, t < (round_robin_roles Ni).length →
      turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 (J + t)).1.2.2 = 0 := by
    intro t htt
    have e1 := hJ (J + t) (Nat.le_add_right _ _)
    have e2 := hJ ((J + t) + 1) (by omega)
    have hBs : turnBound Ni Inv hInvDrain pol hWF0 hInv0 ((J + t) + 1) =
        turnBound Ni Inv hInvDrain pol hWF0 hInv0 (J + t) +
          turnSteps (turnStep Ni Inv hInvDrain pol hWF0 hInv0 (J + t)).1.2.2 := by
      simp only [turnBound]
    omega
  have hconst : ∀ t, t ≤ (round_robin_roles Ni).length →
      turnState Ni Inv hInvDrain pol hWF0 hInv0 (J + t) =
        turnState Ni Inv hInvDrain pol hWF0 hInv0 J := by
    intro t ht
    apply turn_state_const Ni Inv hInvDrain pol hWF0 hInv0
    have h1 := hJ (J + t) (by omega : J ≤ J + t)
    have h2 := hJ J (Nat.le_refl _)
    omega
  cases δ with
  | io_send _ _ _ _ => simp [is_internal_net_label] at hInt
  | io_recv _ _ _ _ => simp [is_internal_net_label] at hInt
  | τ_dequeue _ _ _ _ =>
    cases hTr with
    | dequeue hSQ hmem =>
      have hmemR := rr_roles_mono hReach _ _ hmem
      obtain ⟨t, htt, hrole⟩ := rr_cycle_cover Ni hne J _
        (List.mem_eraseDups.mpr hmemR)
      have hFacts := turn_empty_facts Ni Inv hInvDrain pol hWF0 hInv0 (J + t)
        (hempty t htt)
      have hQ := hFacts.1
      rw [hconst t (by omega), hrole] at hQ
      simp only [rr_quiescent] at hQ
      exact hQ _ _ _ _ _ _ _ hmem hSQ
  | τ_comm _ _ _ _ =>
    have hTr' := hTr
    cases hTr with
    | comm _hne _ _ hmem_p hmem_q =>
      have hmemR := rr_roles_mono hReach _ _ hmem_p
      obtain ⟨t, htt, hrole⟩ := rr_cycle_cover Ni hne J _
        (List.mem_eraseDups.mpr hmemR)
      have hFacts := turn_empty_facts Ni Inv hInvDrain pol hWF0 hInv0 (J + t)
        (hempty t htt)
      have hNS := hFacts.2
      rw [hconst t (by omega), hrole] at hNS
      exact hNS _ _ _ _ hTr'

section LabeledStars
/-- Labeled τ-stars: like `net_trans_star` but a `Type` carrying step
    labels as DATA (all binders explicit so patterns bind everything
    positionally). This is the durable fix for two Lean
    limitations: matching a `Type`-valued inductive to build data is
    small elimination (no `propRecLargeElim` — contrast
    `net_trans_star`-proofs), and `Type` indices substitute under
    `cases`/`induction` (no shared-index splitting). Mirrors
    the `InfiniteNetworkPath.δ` precedent (labels explicit). -/
inductive LabeledStar : Network → Network → Type where
  | refl (N : Network) : LabeledStar N N
  | step (N1 N2 N3 : Network) (δ : net_label)
      (hInt : is_internal_net_label δ) (hTr : net_trans N1 δ N2)
      (rest : LabeledStar N2 N3) : LabeledStar N1 N3

/-- Length (structural — legal since `LabeledStar` is `Type`-valued). -/
def LabeledStar.length {Ni N' : Network} : LabeledStar Ni N' → Nat
  | LabeledStar.refl _ => 0
  | LabeledStar.step _ _ _ _ _ _ rest => LabeledStar.length rest + 1

/-- Append (structural on the first star; middle index varies). -/
def LabeledStar.trans {Ni N'' : Network} : ∀ {N' : Network}, LabeledStar Ni N' →
    LabeledStar N' N'' → LabeledStar Ni N''
  | _, LabeledStar.refl _, s2 => s2
  | _, LabeledStar.step N1 N2 N3 δ hInt hTr rest, s2 =>
    LabeledStar.step N1 N2 _ δ hInt hTr (LabeledStar.trans rest s2)

/-- Length relation for labeled stars (induction on these
    derivations substitutes reliably, unlike proof-valued indices). -/
inductive LabeledStarLen : ∀ {Ni N' : Network}, LabeledStar Ni N' → Nat → Prop where
  | refl (N) : LabeledStarLen (LabeledStar.refl N) 0
  | step {N1 N2 N3 : Network} {δ : net_label}
      {hInt : is_internal_net_label δ} {hTr : net_trans N1 δ N2}
      {rest : LabeledStar N2 N3} {k : Nat} (h : LabeledStarLen rest k) :
      LabeledStarLen (LabeledStar.step N1 N2 N3 δ hInt hTr rest) (k + 1)

/-- A labeled star is forced: at each node, the star's next step is
    the only enabled internal action. Labels are carried as data, so
    uniqueness lifts to every prefix position by star induction
    (`prefix_unique`) with no proof-matching. Per-use-site `hside`
    discharge then needs only these local enabledness-negations. -/
inductive LabeledStar.Forced : {Ni N' : Network} → LabeledStar Ni N' → Prop where
  | refl (N : Network) : LabeledStar.Forced (LabeledStar.refl N)
  | step {N1 N2 N3 : Network} {δ : net_label}
      {hInt : is_internal_net_label δ} {hTr : net_trans N1 δ N2}
      {rest : LabeledStar N2 N3} :
      LabeledStar.Forced rest →
      (∀ (δ' : net_label) (N'' : Network), is_internal_net_label δ' →
        net_trans N1 δ' N'' → δ' = δ) →
      LabeledStar.Forced (LabeledStar.step N1 N2 N3 δ hInt hTr rest)

section R2Avoidance
/-- Roles touched by a label (data): dequeue owner, comm
    sender+receiver. Stars only fire internal labels. -/
def net_label.touched : net_label → List Role
  | net_label.τ_dequeue r _ _ _ => [r]
  | net_label.τ_comm p q _ _ => [p, q]
  | _ => []

/-- A labeled star avoids a role: no step touches it. Entries at
    avoided roles are constant along the star (data-level
    non-interference, no queue reasoning). -/
inductive LabeledStar.Avoids (r0 : Role) : {Ni N' : Network} → LabeledStar Ni N' → Prop where
  | refl (N : Network) : LabeledStar.Avoids r0 (LabeledStar.refl N)
  | step {N1 N2 N3 : Network} {δ : net_label}
      {hInt : is_internal_net_label δ} {hTr : net_trans N1 δ N2}
      {rest : LabeledStar N2 N3} :
      LabeledStar.Avoids r0 rest → r0 ∉ net_label.touched δ →
      LabeledStar.Avoids r0 (LabeledStar.step N1 N2 N3 δ hInt hTr rest)
