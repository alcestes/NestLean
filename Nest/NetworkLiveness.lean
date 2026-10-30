import Nest.MonitorLTS

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# NetworkLiveness: Half-duplex, fairness, and output liveness.

Half-duplex networks, overapproximated steps, infinite fair paths, output
liveness (infinite + finite-maximal), session budgets, and network-step
preservation.
-/

-- ================================================================
-- Half-duplex
-- ================================================================

/-- A network contains role r with queue Q as a top-level pair. -/
def NetworkHasQueue (N : Network) (r : Role) (Q : Queue) : Prop :=
  ∃ (T : SessionType), (r, (T, Q)) ∈ N

/-- Membership of a message in a queue. -/
inductive QueueMem : QueueMessage → Queue → Prop where
  | head {msg : QueueMessage} {Q : Queue} : QueueMem msg (msg :: Q)
  | tail {msg msg' : QueueMessage} {Q : Queue} (h : QueueMem msg Q) : QueueMem msg (msg' :: Q)

/-- Membership is preserved under tail extension of the queue. -/
lemma queueMem_append_left {m : QueueMessage} {l1 l2 : Queue}
    (h : QueueMem m l1) : QueueMem m (l1 ++ l2) := by
  induction h with
  | head => exact QueueMem.head
  | tail _ ih => exact QueueMem.tail ih

/-- The appended message is always a member. -/
lemma queueMem_append_single (Q : Queue) (m : QueueMessage) :
    QueueMem m (Q ++ [m]) := by
  induction Q with
  | nil => exact QueueMem.head
  | cons hd tl ih =>
    by_cases heq : hd = m
    · rw [heq]
      exact QueueMem.head
    · exact QueueMem.tail ih

/-- A queue Q contains a message from role p. -/
def QueueContainsFrom (Q : Queue) (p : Role) : Prop :=
  ∃ (lab : Lab) (S : DataSort), QueueMem (QueueMessage.msg p lab S) Q

/-- Reflexive-transitive closure of internal (τ) transitions in a network. -/
inductive net_trans_star : Network → Network → Prop where
  | refl (N : Network) : net_trans_star N N
  | step {N1 N2 N3 : Network} {δ : net_label}
    (hInt : is_internal_net_label δ)
    (hTr : net_trans N1 δ N2)
    (hStar : net_trans_star N2 N3) : net_trans_star N1 N3

/-- A network is half-duplex if for any two roles p and q,
    data flows only in one direction at a time.
    Formally: whenever N -τ→* N' = { p_i ↦ (T_i, Q_i) }_{i∈I},
    then for all i,j ∈ I, Q_i contains a message from p_j implies
    Q_j does not contain any message from p_i. -/
def IsHalfDuplex (N : Network) : Prop :=
  ∀ (N' : Network), net_trans_star N N' →
    ∀ (p q : Role) (Qp Qq : Queue),
      NetworkHasQueue N' p Qp →
      NetworkHasQueue N' q Qq →
      (QueueContainsFrom Qp q) → ¬ QueueContainsFrom Qq p

/-- `τ*`-reachability is transitive. -/
lemma net_trans_star.trans {N1 N2 N3 : Network} (h12 : net_trans_star N1 N2) (h23 : net_trans_star N2 N3) : net_trans_star N1 N3 := by
  induction h12 with
  | refl => exact h23
  | step hInt hTr hStar' ih => exact net_trans_star.step hInt hTr (ih h23)

/-- Half-duplexity persists along `τ*`-reachability. -/
lemma IsHalfDuplex.star {N N' : Network} (hHD : IsHalfDuplex N) (hStar : net_trans_star N N') : IsHalfDuplex N' := by
  intro N'' hStar'
  exact hHD N'' (net_trans_star.trans hStar hStar')

/-- `NoSelf` persists along network steps under `NoRec` (targets are branch
    subterms or unchanged sessions; membership inversion discards the boolean
    filter proof). -/
lemma net_trans_preserves_no_self {N N' : Network} {δ : net_label}
    (hTr : net_trans N δ N') (hNS : N.NoSelf) : N'.NoSelf := by
  intro q T Q hmem' hOcc
  cases hTr with
  | io_send hSQ hmem0 =>
    unfold Network.replace at hmem'
    simp only [List.mem_cons, List.mem_filter] at hmem'
    rcases hmem' with ⟨rfl, rfl⟩ | ⟨hmemN, -⟩
    · cases hSQ with
      | @send T0 T0' Q0 _ _ _ hST =>
        exact hNS _ _ _ hmem0 (occurs_of_st_trans_target hST hOcc)
    · exact hNS q T Q hmemN hOcc
  | io_recv hSQ hmem0 =>
    unfold Network.replace at hmem'
    simp only [List.mem_cons, List.mem_filter] at hmem'
    rcases hmem' with ⟨rfl, rfl⟩ | ⟨hmemN, -⟩
    · cases hSQ with
      | recv =>
        exact hNS _ _ _ hmem0 hOcc
    · exact hNS q T Q hmemN hOcc
  | dequeue hSQ hmem0 =>
    unfold Network.replace at hmem'
    simp only [List.mem_cons, List.mem_filter] at hmem'
    rcases hmem' with ⟨rfl, rfl⟩ | ⟨hmemN, -⟩
    · cases hSQ with
      | @dequeue T0 T0' Q0 Q0' _ _ _ hST hQ =>
        exact hNS _ _ _ hmem0 (occurs_of_st_trans_target hST hOcc)
    · exact hNS q T Q hmemN hOcc
  | @comm p rr _ _ stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    simp only [Network.replace] at hmem'
    simp only [List.mem_cons, List.mem_filter] at hmem'
    rcases hmem' with ⟨rfl, rfl⟩ | ⟨hmid, -⟩
    · cases h_recv with
      | recv =>
        exact hNS _ _ _ hmem_q hOcc
    · rcases hmid with ⟨rfl, rfl⟩ | ⟨hmemN, -⟩
      · cases h_send with
        | @send T0 T0' Q0 _ _ _ hST =>
          exact hNS _ _ _ hmem_p (occurs_of_st_trans_target hST hOcc)
      · exact hNS q T Q hmemN hOcc

/-- `NoSelf` persists along τ-stars. -/
lemma net_trans_star_preserves_no_self {N N' : Network}
    (hStar : net_trans_star N N') (hNS : N.NoSelf) : N'.NoSelf := by
  revert hNS
  induction hStar with
  | refl =>
    intro hNS
    exact hNS
  | step hInt hTr _ ih =>
    intro hNS
    exact ih (net_trans_preserves_no_self hTr hNS)

-- ================================================================
-- Overapproximated session-type-with-queue semantics.
-- ================================================================

/-- Overapproximated reduction for `(T, Q)`: internal choices fire via
    `sendFresh` (queue unchanged, all branch senders fresh for `Q`);
    external choices fire by dequeuing the oldest
    matching message (`dequeue`, as usual); or fire *speculatively* for a
    role absent from `Q` (`specInp`, queue unchanged) — modelling help from
    future arrivals. Labels reuse `st_label` (`out`/`inp`).
    Contrapositive use: no fold ⟹
    every maximal reduction gets stuck with content, i.e. some messages
    can never be dequeued even with help — feeding non-liveness
    (see `Nest.OverapproxTest` for the separation witnesses). -/
inductive over_trans : SessionTypeWithQueue → st_label → SessionTypeWithQueue → Prop where
  | dequeue {T T' : SessionType} {Q Q' : Queue} {p : Role} {lab : Lab} {S : DataSort}
      {branches : List (Lab × DataSort × SessionType)}
      (hEq : T = SessionType.externalChoice p branches)
      (hmem : (lab, S, T') ∈ branches)
      (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q') :
    over_trans (T, Q) (st_label.inp p lab S) (T', Q')
  | specInp {T T' : SessionType} {Q : Queue} {p : Role} {lab : Lab} {S : DataSort}
      {branches : List (Lab × DataSort × SessionType)}
      (hEq : T = SessionType.externalChoice p branches)
      (hmem : (lab, S, T') ∈ branches)
      (hAbs : ∀ m ∈ Q, m.1 ≠ p) :
    over_trans (T, Q) (st_label.inp p lab S) (T', Q)
  | sendFresh {T T' : SessionType} {Q : Queue} {p : Role} {lab : Lab} {S : DataSort}
      {branches : List (Role × Lab × DataSort × SessionType)}
      (hEq : T = SessionType.internalChoice branches)
      (hST : st_trans T (st_label.out p lab S) T')
      (hFresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
        (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r') :
    over_trans (T, Q) (st_label.out p lab S) (T', Q)
  /-- Silent unfold: visit the unfolded type with the queue unchanged
      (no label, no monitor observation). The ONLY `over_trans` rule at
      `tRec` heads (all other rules pin choice heads), so every drain
      trace visits unfold boundaries. -/
  | tauUnfold {T U : SessionType} {Q : Queue}
      (hU : Unfold1 T U) :
    over_trans (T, Q) st_label.tau (U, Q)


/-- An infinite network path is a sequence of network configurations
    (N_i)_{i ∈ ℕ} where each step is an internal (τ) transition. -/
structure InfiniteNetworkPath where
  /-- The underlying sequence of networks. -/
  seq : ℕ → Network
  /-- The label of the transition at step `i`, carried explicitly (not via
      choice) so that per-step label equations are provable by construction. -/
  δ : ℕ → net_label
  /-- Every step label is an internal (τ) label. -/
  δ_form : ∀ (i : ℕ), ∃ (r p : Role) (lab : Lab) (S : DataSort),
    δ i = net_label.τ_dequeue r p lab S ∨ δ i = net_label.τ_comm r p lab S
  /-- The labels witness genuine transitions between consecutive states. -/
  δ_tr : ∀ (i : ℕ), net_trans (seq i) (δ i) (seq (i + 1))

namespace InfiniteNetworkPath

lemma δ_spec (path : InfiniteNetworkPath) (i : ℕ) :
    (∃ (r p : Role) (lab : Lab) (S : DataSort),
      path.δ i = net_label.τ_dequeue r p lab S ∨ path.δ i = net_label.τ_comm r p lab S) ∧
    net_trans (path.seq i) (path.δ i) (path.seq (i + 1)) :=
  ⟨path.δ_form i, path.δ_tr i⟩

end InfiniteNetworkPath

/--
  An infinite network path is fair iff whenever
  (1) at some step i role P can communicate with someone, then eventually some
      communication involving P occurs; and
  (2) at some step i a specific dequeue (P ? Q lab(S)) is enabled, then
      that dequeue eventually occurs.
 -/
def IsFair (path : InfiniteNetworkPath) : Prop :=
  let f := path.seq
  ∀ (i : ℕ),
    (∀ (p : Role),
      (∃ (q : Role) (lab : Lab) (S : DataSort) (N' : Network),
        net_trans (f i) (net_label.τ_comm p q lab S) N') →
      ∃ (k : ℕ), i ≤ k ∧
        (∃ (q : Role) (lab : Lab) (S : DataSort),
          path.δ k = net_label.τ_comm p q lab S)) ∧
    (∀ (p q : Role) (lab : Lab) (S : DataSort),
      (∃ (N' : Network),
        net_trans (f i) (net_label.τ_dequeue p q lab S) N') →
      ∃ (k : ℕ), i ≤ k ∧ path.δ k = net_label.τ_dequeue p q lab S)

-- ================================================================
-- Finite-maximal-path liveness (paper's "possibly infinite" path indexed by I)
-- ================================================================

/-- A network is stuck if it has no outgoing internal (τ) transition. -/
def IsStuckNetwork (N : Network) : Prop :=
  ¬ ∃ (δ : net_label) (N' : Network), is_internal_net_label δ ∧ net_trans N δ N'

/-- A network has no orphan messages: no queue entry is dequeueable
    (`Q.dequeue msg = some`). For a stuck `N'`, this is exactly output-liveness
    of the finite maximal path ending in `N'` (no future dequeue possible, so
    the premise must be vacuous). -/
def NoOrphanMessages (N : Network) : Prop :=
  ∀ (r : Role) (T : SessionType) (Q : Queue) (p : Role) (lab : Lab) (S : DataSort)
    (Q' : Queue), (r, (T, Q)) ∈ N → Q.dequeue (QueueMessage.msg p lab S) = some Q' → False

/-- An (infinite) network path is output-live iff whenever
    at step i a role's queue contains a message from q with label lab and sort S,
    then that message is eventually dequeued. -/
def IsOutputLiveInfinitePath (path : InfiniteNetworkPath) : Prop :=
  let f := path.seq
  ∀ (i : ℕ), ∀ (p : Role) (Qp : Queue),
    NetworkHasQueue (f i) p Qp →
    ∀ (q : Role) (lab : Lab) (S : DataSort),
      (∃ (Q' : Queue), Qp.dequeue (QueueMessage.msg q lab S) = some Q') →
      ∃ (k : ℕ), i ≤ k ∧ path.δ k = net_label.τ_dequeue p q lab S

/-- A network N is output-live if every (infinite) fair path starting from N is output-live.
    See `IsOutputLiveNetwork` below for the
    finite-maximal-path extension (paper's "possibly infinite" `I`). -/
def IsOutputLiveInfinitePathNetwork (N : Network) : Prop :=
  ∀ (path : InfiniteNetworkPath), path.seq 0 = N → IsFair path → IsOutputLiveInfinitePath path


/-- Output-liveness "proper" (covering both finite and infinite paths):
    infinite fair paths are output-live, and every τ-reachable stuck configuration has no orphans.
    Without the second conjunct, stuck networks with orphans would be vacuously
    live under the infinite-only `InfiniteNetworkPath` (`ℕ → Network`), breaking
    the input-liveness argument (counterexample: `q = tEnd` with
    `p` able to send; `N` has only the finite maximal path `N → N1 stuck
    with orphan`, no infinite paths). -/
def IsOutputLiveNetwork (N : Network) : Prop :=
  IsOutputLiveInfinitePathNetwork N ∧
  (∀ (N' : Network), net_trans_star N N' → IsStuckNetwork N' → NoOrphanMessages N')

-- ================================================================
-- Session budgets and termination for `NoRec` networks
--
-- Every internal step moves some role's session to a strict subterm
-- (`NoRec` rules out `tRec`-unfold growth; receiver sessions are
-- unchanged; `net_trans.comm` requires `p ≠ q` so no step overwrites its
-- own session move — without it, self-delivery restores the session
-- and the budget need not decrease). Hence the budget strictly
-- decreases and all internal activity is finite.
-- ================================================================

/-- Session-size budget of a network (sum of entry session sizes). -/
noncomputable def networkBudget (N : Network) : ℕ :=
  (N.map fun x : Role × SessionTypeWithQueue => sizeOf x.2.1).sum

/-- Filtering out absent roles preserves the budget (no entry removed). -/
private lemma filter_sum_eq_of_no_role (l : List (Role × SessionTypeWithQueue)) (r : Role)
    (h : ∀ x ∈ l, x.1 ≠ r) :
    (((l.filter fun x => x.1 != r).map fun x : Role × SessionTypeWithQueue => sizeOf x.2.1).sum) =
    ((l.map fun x => sizeOf x.2.1).sum) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hpos : ((fun x : Role × SessionTypeWithQueue => x.1 != r) hd) :=
      bne_iff_ne.mpr (h hd (List.mem_cons.mpr (Or.inl rfl)))
    have htl : ∀ x ∈ tl, x.1 ≠ r :=
      fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
    rw [List.filter_cons_of_pos (p := fun x : Role × SessionTypeWithQueue => x.1 != r)
      (a := hd) hpos, List.map_cons, List.map_cons,
      List.sum_cons, List.sum_cons, ih htl]

/-- Replace-bookkeeping as an equation: the new budget plus the old entry
    size equals the old budget plus the new entry size. -/
private lemma budget_replace_eq (l : List (Role × SessionTypeWithQueue)) (r : Role)
    (stq stq' : SessionTypeWithQueue)
    (hmem : (r, stq) ∈ l)
    (hnd : (l.map fun x : Role × SessionTypeWithQueue => x.1).Nodup) :
    ((((r, stq') :: l.filter fun x => x.1 != r).map
      fun x : Role × SessionTypeWithQueue => sizeOf x.2.1).sum) + sizeOf stq.1 =
    ((l.map fun x => sizeOf x.2.1).sum) + sizeOf stq'.1 := by
  revert hmem hnd
  induction l with
  | nil =>
    intro hmem hnd
    simp at hmem
  | cons hd tl ih =>
    intro hmem hnd
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, htlnd⟩ := hnd
    by_cases heq : hd.1 = r
    · -- `hd` is the replaced entry: the filter drops exactly it.
      have hhd : hd = (r, stq) := by
        rcases List.mem_cons.mp hmem with heq2 | hmemT
        · exact heq2.symm
        · exfalso
          rw [heq] at hnotin
          exact hnotin (List.mem_map.mpr ⟨(r, stq), hmemT, rfl⟩)
      subst hhd
      have hno : ∀ x ∈ tl, x.1 ≠ r := by
        intro x hx heq2
        exact hnotin (List.mem_map.mpr ⟨x, hx, heq2⟩)
      have hfsum := filter_sum_eq_of_no_role tl r hno
      rw [List.filter_cons_of_neg (p := fun x : Role × SessionTypeWithQueue => x.1 != r)
        (a := (r, stq)) (fun h => (bne_iff_ne.mp h) rfl)]
      simp only [List.map_cons, List.sum_cons]
      rw [hfsum]
      show (sizeOf stq'.1 + _) + sizeOf stq.1 = (sizeOf stq.1 + _) + sizeOf stq'.1
      omega
    · -- `hd` kept: recurse on the tail.
      have hmemT : (r, stq) ∈ tl := by
        rcases List.mem_cons.mp hmem with heq2 | hT
        · exfalso
          have hrh : hd.1 = r := by rw [← heq2]
          exact heq hrh
        · exact hT
      rw [List.filter_cons_of_pos (p := fun x : Role × SessionTypeWithQueue => x.1 != r)
        (a := hd) (bne_iff_ne.mpr heq)]
      simp only [List.map_cons, List.sum_cons]
      have ih' := ih hmemT htlnd
      simp only [List.map_cons, List.sum_cons] at ih'
      omega

/-- Well-formedness persists along τ-stars. -/
lemma net_trans_preserves_well_formed {N N' : Network}
    (hWF : N.WellFormed) (hStar : net_trans_star N N') : N'.WellFormed := by
  revert hWF
  induction hStar with
  | refl =>
    intro hWF
    exact hWF
  | step hInt hTr _ ih =>
    intro hWF
    exact ih (Network.wellFormedPreserved _ _ _ hWF hTr hInt)

/-- Membership survives replacing another role's entry. -/
lemma mem_replace_other {N : Network} {r0 : Role} {stq0 : SessionTypeWithQueue}
    {r : Role} {stq : SessionTypeWithQueue}
    (h : (r, stq) ∈ N) (hne : r ≠ r0) :
    (r, stq) ∈ Network.replace N r0 stq0 := by
  unfold Network.replace
  simp
  right
  exact ⟨h, hne⟩

/-- Well-formed networks have unique entries per role. -/
lemma network_mem_unique {N : Network} (hwf : N.WellFormed)
    {r : Role} {stq1 stq2 : SessionTypeWithQueue}
    (h1 : (r, stq1) ∈ N) (h2 : (r, stq2) ∈ N) : stq1 = stq2 := by
  suffices key : ∀ (L : Network), (L.map Prod.fst).Nodup →
      ∀ {r : Role} {a b : SessionTypeWithQueue},
      (r, a) ∈ L → (r, b) ∈ L → a = b from key N hwf.1 h1 h2
  intro L hnd r a b h1 h2
  induction L with
  | nil => simp at h1
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, hndtl⟩ := hnd
    simp only [List.mem_cons] at h1 h2
    rcases h1 with rfl | h1
    · rcases h2 with h2 | h2
      · exact (congrArg Prod.snd h2).symm
      · exfalso
        exact hnotin (List.mem_map.mpr ⟨_, h2, rfl⟩)
    · rcases h2 with rfl | h2
      · exfalso
        exact hnotin (List.mem_map.mpr ⟨_, h1, rfl⟩)
      · exact ih hndtl h1 h2

/-- Single-replace preservation of presence: occurrences in the new session
    back-propagate to the old session (`hBack`) or name the replaced role
    itself (whose new entry witnesses presence). -/
lemma RolesPresent_of_replace {N : Network} {r0 : Role}
    {stq0 stq' : SessionTypeWithQueue}
    (hPres : N.RolesPresent) (hmem0 : (r0, stq0) ∈ N)
    (hBack : ∀ s : Role, stq'.1.Occurs s → stq0.1.Occurs s) :
    (N.replace r0 stq').RolesPresent := by
  intro q T Q s hmem' hOcc
  unfold Network.replace at hmem'
  simp only [List.mem_cons, List.mem_filter] at hmem'
  rcases hmem' with heq | ⟨hmemN, -⟩
  · simp only [Prod.mk.injEq] at heq
    obtain ⟨_, hTQ⟩ := heq
    have hNew : stq'.1.Occurs s := by rw [← hTQ]; exact hOcc
    by_cases heq2 : s = r0
    · subst heq2
      refine ⟨stq', ?_⟩
      unfold Network.replace
      simp
    · obtain ⟨stq, hs⟩ := hPres _ _ _ _ hmem0 (hBack _ hNew)
      exact ⟨stq, mem_replace_other hs heq2⟩
  · obtain ⟨stq, hs⟩ := hPres _ _ _ _ hmemN hOcc
    by_cases heq2 : s = r0
    · subst heq2
      refine ⟨stq', ?_⟩
      unfold Network.replace
      simp
    · exact ⟨stq, mem_replace_other hs heq2⟩

/-- Presence persists along network steps under `NoRec` (send/dequeue
    targets back-propagate via `occurs_of_st_trans_target`; receives keep
    the session). -/
lemma net_trans_preserves_roles_present {N N' : Network} {δ : net_label}
    (hTr : net_trans N δ N') (hPres : N.RolesPresent) :
    N'.RolesPresent := by
  cases hTr with
  | io_send hSQ hmem0 =>
    cases hSQ with
    | @send T0 T0' Q0 _ _ _ hST =>
      exact RolesPresent_of_replace hPres hmem0
        (fun s h => occurs_of_st_trans_target hST h)
  | io_recv hSQ hmem0 =>
    cases hSQ with
    | recv =>
      exact RolesPresent_of_replace hPres hmem0 (fun s h => h)
  | dequeue hSQ hmem0 =>
    cases hSQ with
    | @dequeue T0 T0' Q0 Q0' _ _ _ hST hQ =>
      exact RolesPresent_of_replace hPres hmem0
        (fun s h => occurs_of_st_trans_target hST h)
  | @comm p q _ _ stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    have hMid : (N.replace p stqp').RolesPresent := by
      cases h_send with
      | @send T0 T0' Q0 _ _ _ hST =>
        exact RolesPresent_of_replace hPres hmem_p
          (fun s h => occurs_of_st_trans_target hST h)
    have hmem_q_mid : (q, stqq) ∈ N.replace p stqp' :=
      mem_replace_other hmem_q (Ne.symm hne)
    cases h_recv with
    | recv =>
      exact RolesPresent_of_replace hMid hmem_q_mid (fun s h => h)

/-- Presence persists along τ-stars. -/
lemma net_trans_star_preserves_roles_present {N N' : Network}
    (hStar : net_trans_star N N') (hPres : N.RolesPresent) :
    N'.RolesPresent := by
  revert hPres
  induction hStar with
  | refl =>
    intro hPres
    exact hPres
  | step hInt hTr _ ih =>
    intro hPres
    exact ih (net_trans_preserves_roles_present hTr hPres)

/-- Mapped filter is a sublist of the mapped list. -/
private lemma map_filter_sublist (l : List (Role × SessionTypeWithQueue))
    (p : (Role × SessionTypeWithQueue) → Bool) (f : (Role × SessionTypeWithQueue) → Role) :
    List.Sublist ((l.filter p).map f) (l.map f) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons hd tl ih =>
    by_cases h : p hd = true
    · rw [List.filter_cons_of_pos (a := hd) (by rw [h])]
      simp only [List.map_cons]
      exact List.Sublist.cons_cons _ ih
    · rw [List.filter_cons_of_neg (a := hd) h]
      exact List.Sublist.cons _ ih

/-- Role-nodup survives `Network.replace`. -/
private lemma nodup_replace_roles {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    (hnd : (N.map fun x : Role × SessionTypeWithQueue => x.1).Nodup) :
    (((Network.replace N r stq).map fun x : Role × SessionTypeWithQueue => x.1)).Nodup := by
  unfold Network.replace
  simp only [List.map_cons]
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hmem
    obtain ⟨x, hx, hxx⟩ := List.mem_map.mp hmem
    have hpred : ((fun x : Role × SessionTypeWithQueue => x.1 != r) x) :=
      (List.mem_filter.mp hx).2
    exact (bne_iff_ne.mp hpred) hxx
  · exact hnd.sublist (map_filter_sublist _ _ _)

/-- Reachability along an infinite path (each prefix is a τ-star). -/
private lemma path_star_reachable_of (π : InfiniteNetworkPath) (Ni : Network)
    (h0 : π.seq 0 = Ni) (i : ℕ) : net_trans_star Ni (π.seq i) := by
  induction i with
  | zero =>
    rw [h0]
    exact net_trans_star.refl _
  | succ k ih =>
    have hTr := π.δ_tr k
    obtain ⟨r, p, lab, S, h | h⟩ := π.δ_form k
    · rw [h] at hTr
      exact net_trans_star.trans ih (net_trans_star.step (by trivial) hTr (net_trans_star.refl _))
    · rw [h] at hTr
      exact net_trans_star.trans ih (net_trans_star.step (by trivial) hTr (net_trans_star.refl _))


/-- A non-stuck network has an outgoing internal step (classical). -/
private lemma stuckStep_of_notStuck {N : Network} (h : ¬ IsStuckNetwork N) :
    ∃ δ N', is_internal_net_label δ ∧ net_trans N δ N' := by
  unfold IsStuckNetwork at h
  exact Classical.byContradiction h

