import Nest.StuckWitness

/-!
# MonitorToolkit: instrumentation bridge and liveness persistence.

Step-freeness bank, maximal-derivation height (`max_deriv_height`),
consistent-instrumentation bridge (`mem_consistentInstrumentation`,
`consistentInstrumentation_replace`), queue/dequeue toolkit,
well-formedness/role preservation, comm/dequeue persistence, liveness
persistence (`output_live_persistent`), fairness-path prepending
(`prepend_single`).
-/

-- Unfold-spine height as a `Prop`-valued relation (`pfx` subproofs count
-- 0; never recurse into `hall`/`hallMax` functions). A `Nat`-valued
-- recursive definition is blocked by `propRecLargeElim` (proofs cannot
-- recurse into data), so the height lives in `Prop` and the `tRec` arm of
-- determinism goes through explicit bounds + well-founded `Nat` induction
-- with inversion inline (`cases` on height proofs).
/-- Maximal-derivation height: fuel measure for maximal `mon_tr_yes` derivations (avoids recursing
   into `Prop`). -/
inductive max_deriv_height : ∀ {T : SessionType} {γ : ext_tag} {V : SessionType}
    (hE : mon_tr_yes_exist T γ V), mon_tr_yes_max_deriv hE → Nat → Prop where
  | base {T : SessionType} {γ : ext_tag} {V : SessionType} {h : mon_tr_yes_base T γ V} :
      max_deriv_height (mon_tr_yes_exist.base h) (@mon_tr_yes_max_deriv.base _ _ _ h) 0
  | pfxInt {branches kept : List (Role × Lab × DataSort × SessionType)}
      {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
      {hne : branches ≠ [] ∧ kept ≠ []}
      {hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ branches → q ≠ p'}
      {hkept : T' = SessionType.internalChoice kept}
      {hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
        (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1}
      {hNodupKept : List.Nodup (kept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)))}
      {hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
        (r, l, s, T1) ∈ kept → ∃ T0, (r, l, s, T0) ∈ branches}
      (hallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort)
        (hmemB : (r, l, s, T0) ∈ branches) (hmemK : (r, l, s, T1) ∈ kept)
        (hsub : mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1),
        mon_tr_yes_max_deriv hsub)
      (hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
        (r, l, s, T0) ∈ branches → (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) →
          ∃ T1, (r, l, s, T1) ∈ kept)
      (horder : List.Sublist (kept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
        (branches.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))) :
      max_deriv_height (@mon_tr_yes_exist.pfxInt branches kept q lab S T' hne hno hkept hall hNodupKept hkey)
        (@mon_tr_yes_max_deriv.pfxInt branches kept q lab S T' hne hno hkept hall hNodupKept hkey hallMax hcover horder) 0
  | pfxExt {p : Role} {branches kept : List (Lab × DataSort × SessionType)}
      {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
      {hne : branches ≠ [] ∧ kept ≠ []}
      {hneq : q ≠ p}
      {hkept : T' = SessionType.externalChoice p kept}
      {hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
        (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1}
      {hNodupKept : List.Nodup (kept.map (λ x : Lab × DataSort × SessionType => x.1))}
      {hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
        (l, s, T1) ∈ kept → ∃ T0, (l, s, T0) ∈ branches}
      (hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
        (hmemB : (l, s, T0) ∈ branches) (hmemK : (l, s, T1) ∈ kept)
        (hsub : mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1),
        mon_tr_yes_max_deriv hsub)
      (hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
        (l, s, T0) ∈ branches → (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) →
          ∃ T1, (l, s, T1) ∈ kept)
      (horder : List.Sublist (kept.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)))
        (branches.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)))) :
      max_deriv_height (@mon_tr_yes_exist.pfxExt p branches kept q lab S T' hne hneq hkept hall hNodupKept hkey)
        (@mon_tr_yes_max_deriv.pfxExt p branches kept q lab S T' hne hneq hkept hall hNodupKept hkey hallMax hcover horder) 0
  | unfold {X : String} {B : SessionType} {γ : ext_tag} {V : SessionType}
      {h : mon_tr_yes_exist (substSessionType B X (SessionType.tRec X B)) γ V}
      {hmax : mon_tr_yes_max_deriv h} {n : Nat} (hh : max_deriv_height h hmax n) :
      max_deriv_height (mon_tr_yes_exist.unfold h) (mon_tr_yes_max_deriv.unfold hmax) (n + 1)

/-- Membership in the network is inherited by the consistent instrumentation, with the
    entry of `stq` carrying its encoder value. -/
lemma mem_consistentInstrumentation {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    {MN : MonitoredNetwork} (hmem : (r, stq) ∈ N) (hCons : consistentInstrumentation N = some MN) :
    ∃ M, monitor_fold_val_partial stq = some M ∧ (r, (stq, M)) ∈ MN := by
  induction N generalizing MN with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨r0, stq0⟩
    rw [consistentInstrumentation] at hCons
    cases h_e : monitor_fold_val_partial stq0 with
    | none => simp [h_e] at hCons
    | some M0 =>
      cases h_c : consistentInstrumentation tl with
      | none => simp [h_e, h_c] at hCons
      | some MNtl =>
        rw [h_e, h_c] at hCons
        injection hCons with hMN_eq
        simp at hmem
        rcases hmem with (⟨rfl, rfl⟩ | htl)
        · exact ⟨M0, h_e, by rw [← hMN_eq]; simp⟩
        · rcases ih htl h_c with ⟨M, h_ev, h_mem⟩
          exact ⟨M, h_ev, by rw [← hMN_eq]; simpa using (Or.inr h_mem)⟩

/-- Inversion of `mem_consistentInstrumentation`: an entry `(r, (stq, M))` of the monitored
    network comes from a network entry `(r, stq)`, and `M` is the encoding value of `stq`. -/
lemma consistentInstrumentation_inv_mem {N : Network} {r : Role} {stq : SessionTypeWithQueue} {M : SessionType}
    {MN : MonitoredNetwork} (hmem : (r, (stq, M)) ∈ MN) (hCons : consistentInstrumentation N = some MN) :
    (r, stq) ∈ N ∧ monitor_fold_val_partial stq = some M := by
  induction N generalizing MN with
  | nil =>
      simp [consistentInstrumentation] at hCons
      rw [hCons] at hmem
      simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨r0, stq0⟩
    rw [consistentInstrumentation] at hCons
    cases h_e : monitor_fold_val_partial stq0 with
    | none => simp [h_e] at hCons
    | some M0 =>
      cases h_c : consistentInstrumentation tl with
      | none => simp [h_e, h_c] at hCons
      | some MNtl =>
        rw [h_e, h_c] at hCons
        injection hCons with hMN_eq
        rw [← hMN_eq] at hmem
        simp at hmem
        rcases hmem with (⟨rfl, ⟨rfl, rfl⟩⟩ | htl)
        · exact ⟨by simp, h_e⟩
        · rcases ih htl h_c with ⟨hmem', hev⟩
          exact ⟨by simpa using (Or.inr hmem'), hev⟩

/-- Consistent instrumentation commutes with filtering the network by role. -/
lemma consistentInstrumentation_filter {N : Network} {MN : MonitoredNetwork} (P : Role → Prop)
    [DecidablePred P] (hCons : consistentInstrumentation N = some MN) :
    consistentInstrumentation (N.filter (λ x : Role × SessionTypeWithQueue => P x.1)) =
      some (MN.filter (λ x : Role × MonitoredSessionType => P x.1)) := by
  induction N generalizing MN with
  | nil =>
    have hMN : MN = [] := by
      simpa [consistentInstrumentation] using (Option.some_inj.mp hCons.symm)
    simp [consistentInstrumentation, hMN]
  | cons hd tl ih =>
    rcases hd with ⟨r0, stq0⟩
    rw [consistentInstrumentation] at hCons
    cases h_e : monitor_fold_val_partial stq0 with
    | none => simp [h_e] at hCons
    | some M0 =>
      cases h_c : consistentInstrumentation tl with
      | none => simp [h_e, h_c] at hCons
      | some MNtl =>
        rw [h_e, h_c] at hCons
        injection hCons with hMN_eq
        by_cases hp : P r0
        · have h_ih : consistentInstrumentation (tl.filter (λ x : Role × SessionTypeWithQueue => P x.1)) =
              some (MNtl.filter (λ x : Role × MonitoredSessionType => P x.1)) := ih h_c
          rw [← hMN_eq]
          simp [consistentInstrumentation, h_e, h_ih, hp]
        · have h_ih : consistentInstrumentation (tl.filter (λ x : Role × SessionTypeWithQueue => P x.1)) =
              some (MNtl.filter (λ x : Role × MonitoredSessionType => P x.1)) := ih h_c
          rw [← hMN_eq]
          simp [h_ih, hp]

/-- Consistent instrumentation commutes with replacing a role's session type with queue. -/
lemma consistentInstrumentation_replace {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    {MN : MonitoredNetwork} {M : SessionType}
    (hCons : consistentInstrumentation N = some MN) (hM : monitor_fold_val_partial stq = some M) :
    consistentInstrumentation (Network.replace N r stq) = some (MN.replace r (stq, M)) := by
  have hf : consistentInstrumentation (N.filter (λ x : Role × SessionTypeWithQueue => x.1 != r)) =
      some (MN.filter (λ x : Role × MonitoredSessionType => x.1 != r)) :=
    consistentInstrumentation_filter (fun _x => _x != r) hCons
  unfold Network.replace MonitoredNetwork.replace
  rw [consistentInstrumentation]
  rw [hM, hf]

/-- A silent (dequeue) step at the session-type-with-queue level lifts to the monitored
    network, where the monitor state is unchanged. -/
lemma mon_net_trans.dequeue {MN : MonitoredNetwork} {r p : Role} {lab : Lab} {S : DataSort}
    {stq stq' : SessionTypeWithQueue} {M : SessionType}
    (hSQ : sq_trans stq (sq_action.dequeue p lab S) stq')
    (hmem : (r, (stq, M)) ∈ MN) :
    mon_net_trans MN (mon_net_label.τ_dequeue r p lab S) (MN.replace r (stq', M)) := by
  simpa [mon_net_label.ofmon_label] using (mon_net_trans.lift (mon_trans.dequeue hSQ) hmem)

/-- Successful `dequeue.go` scans split the remainder around the found message (`seen`-accumulator
   soundness). -/
lemma dequeue_go_some {acc : Queue} {left : Queue} {msg : QueueMessage} {Q' : Queue}
    (h : Queue.dequeue.go acc left msg = some Q')
    (hacc : ∀ m ∈ acc, m.1 ≠ msg.1) :
    ∃ left_l left_r : Queue,
      left = left_l ++ [msg] ++ left_r ∧
      Q' = acc ++ left_l ++ left_r ∧
      (∀ m ∈ left_l, m.1 ≠ msg.1) := by
  induction left generalizing acc with
  | nil => simp [Queue.dequeue.go] at h
  | cons m rest ih =>
      by_cases hm_eq : m = msg
      · subst m
        have hQ'' : Q' = acc ++ rest := by
          simp [Queue.dequeue.go] at h
          exact h.symm
        refine ⟨[], rest, by simp, ?_, ?_⟩
        · simpa [List.append_nil] using hQ''
        · simp
      · have hm_ne : m ≠ msg := hm_eq
        by_cases hs : m.1 = msg.1
        · exfalso
          simp [Queue.dequeue.go, hm_ne, hs] at h
        · have hnots : m.1 ≠ msg.1 := hs
          have hacc' : ∀ m' ∈ acc ++ [m], m'.1 ≠ msg.1 := by
            intro m' hm'
            rcases List.mem_append.mp hm' with hmem | hmem
            · exact hacc m' hmem
            · rw [List.mem_singleton] at hmem
              simpa [hmem] using hnots
          simp [Queue.dequeue.go, hm_eq, hnots] at h
          rcases ih h hacc' with ⟨left_l, left_r, hleft, hQ', hcond_l⟩
          refine ⟨m :: left_l, left_r, ?_, ?_, ?_⟩
          · rw [List.cons_append]
            exact congrArg (λ q => m :: q) hleft
          · calc
              Q' = (acc ++ [m]) ++ left_l ++ left_r := hQ'
              _ = acc ++ (m :: left_l) ++ left_r := by simp [List.cons_append]
          · intro m' hm'
            simp at hm'
            rcases hm' with rfl | hm'
            · exact hnots
            · exact hcond_l m' hm'

/-- Structural statement of a successful dequeue. -/
lemma queue_dequeue_some_iff {Q Q' : Queue} {msg : QueueMessage}
    (h : Q.dequeue msg = some Q') :
    ∃ seen left : Queue, Q = seen ++ [msg] ++ left ∧ Q' = seen ++ left ∧ ∀ m ∈ seen, m.1 ≠ msg.1 := by
  rcases msg with ⟨p, lab, S⟩
  rw [Queue.dequeue] at h
  rcases dequeue_go_some h (by simp) with ⟨left_l, left_r, hQ, hQ', hcond_l⟩
  refine ⟨left_l, left_r, hQ, ?_, hcond_l⟩
  simpa [List.nil_append] using hQ'

/-- Auxiliary: an input step's sender is determined by the target's shape (used once for
   uniqueness). -/
private lemma sttr_inp_sender_aux : ∀ {T T' : SessionType} {α : st_label},
    st_trans T α T' →
    (∀ (p1 : Role) (lab1 : Lab) (S1 : DataSort) (T1 : SessionType)
      (p2 : Role) (lab2 : Lab) (S2 : DataSort) (T2 : SessionType),
      α = st_label.inp p1 lab1 S1 → T' = T1 →
      st_trans T (st_label.inp p2 lab2 S2) T2 → p1 = p2) := by
  intro T T' α hST
  induction hST with
  | intC hmem =>
    intro p1 lab1 S1 T1 p2 lab2 S2 T2 hEq hT hIn
    cases hEq
  | extC hmem =>
    intro p1 lab1 S1 T1 p2 lab2 S2 T2 hEq hT hIn
    cases hEq
    cases hT
    match hIn with
    | st_trans.extC hmem2 => rfl
  | tRec hsub ih =>
    intro p1 lab1 S1 T1 p2 lab2 S2 T2 hEq hT hIn
    match hIn with
    | st_trans.tRec hsub2 => exact ih p1 lab1 S1 T1 p2 lab2 S2 T2 hEq hT hsub2

/-- A `dequeue.go` scan that hits a same-sender message reports it (no-skip case). -/
private lemma dequeue_go_same_sender {acc : Queue} {left : Queue}
    {msg1 msg2 : QueueMessage} {Q1' Q2' : Queue}
    (h1 : Queue.dequeue.go acc left msg1 = some Q1')
    (h2 : Queue.dequeue.go acc left msg2 = some Q2')
    (hsame : msg1.1 = msg2.1) :
    msg1 = msg2 := by
  induction left generalizing acc Q1' Q2' with
  | nil => simp [Queue.dequeue.go] at h1
  | cons m rest ih =>
    by_cases hm1 : m = msg1
    · subst hm1
      by_cases hm2 : m = msg2
      · exact hm2
      · exfalso
        simp [Queue.dequeue.go, hm2, hsame] at h2
    · have hm1_ne : m ≠ msg1 := hm1
      by_cases hs1 : m.1 = msg1.1
      · exfalso
        simp [Queue.dequeue.go, hm1_ne, hs1] at h1
      · have hns1 : m.1 ≠ msg1.1 := hs1
        simp [Queue.dequeue.go, hm1_ne, hns1] at h1
        by_cases hm2 : m = msg2
        · exfalso
          have hm_eq : m.1 = msg2.1 := congrArg (fun x : QueueMessage => x.1) hm2
          rw [← hsame] at hm_eq
          exact hns1 hm_eq
        · have hm2_ne : m ≠ msg2 := hm2
          have hns2 : m.1 ≠ msg2.1 := by
            rw [← hsame]
            exact hns1
          simp [Queue.dequeue.go, hm2_ne, hns2] at h2
          exact ih h1 h2

/-- `dequeue.go` commutes with appending to the unexplored tail. -/
private lemma dequeue_go_append {acc left : Queue} {msg msg2 : QueueMessage} {Q' : Queue}
    (h : Queue.dequeue.go acc left msg = some Q') :
    Queue.dequeue.go acc (left ++ [msg2]) msg = some (Q' ++ [msg2]) := by
  induction left generalizing acc Q' with
  | nil =>
    simp [Queue.dequeue.go] at h
  | cons m rest ih =>
    by_cases hm : m = msg
    · subst hm
      have hQ : Q' = acc ++ rest := by
        simp [Queue.dequeue.go] at h
        exact h.symm
      have hgoal : Queue.dequeue.go acc ((m :: rest) ++ [msg2]) m =
          some (acc ++ (rest ++ [msg2])) := by
        simp [Queue.dequeue.go]
      rw [hgoal, hQ]
      simp [List.append_assoc]
    · have hm_ne : m ≠ msg := hm
      by_cases hs : m.1 = msg.1
      · exfalso
        simp [Queue.dequeue.go, hm_ne, hs] at h
      · have hns : m.1 ≠ msg.1 := hs
        simp [Queue.dequeue.go, hm_ne, hns] at h
        have ih' := ih h
        have hgoal : Queue.dequeue.go acc ((m :: rest) ++ [msg2]) msg =
            Queue.dequeue.go (acc ++ [m]) (rest ++ [msg2]) msg := by
          simp [Queue.dequeue.go, hm_ne, hns]
        rw [hgoal, ih']

/-- `Queue.dequeue` commutes with appending to the queue. -/
private lemma queue_dequeue_append {Q Q' : Queue} {msg msg2 : QueueMessage}
    (h : Q.dequeue msg = some Q') :
    (Q ++ [msg2]).dequeue msg = some (Q' ++ [msg2]) := by
  unfold Queue.dequeue at h ⊢
  have hgo : Queue.dequeue.go [] (Q ++ [msg2]) msg = some (Q' ++ [msg2]) :=
    dequeue_go_append h
  simpa using hgo

/-- Same-queue dequeue steps agree on sender, label, and sort. -/
private lemma sq_dequeue_label_unique {T : SessionType} {Q : Queue}
    {p1 : Role} {lab1 : Lab} {S1 : DataSort} {T1 : SessionType} {Q1' : Queue}
    {p2 : Role} {lab2 : Lab} {S2 : DataSort} {T2 : SessionType} {Q2' : Queue}
    (h1 : sq_trans (T, Q) (sq_action.dequeue p1 lab1 S1) (T1, Q1'))
    (h2 : sq_trans (T, Q) (sq_action.dequeue p2 lab2 S2) (T2, Q2')) :
    p1 = p2 ∧ lab1 = lab2 ∧ S1 = S2 := by
  cases h1 with
  | dequeue hST1 hQ1 =>
    cases h2 with
    | dequeue hST2 hQ2 =>
      have hp : p1 = p2 :=
        sttr_inp_sender_aux hST1 p1 lab1 S1 T1 p2 lab2 S2 T2 rfl rfl hST2
      subst hp
      have hmsg : QueueMessage.msg p1 lab1 S1 = QueueMessage.msg p1 lab2 S2 := by
        unfold Queue.dequeue at hQ1 hQ2
        have hsame : (QueueMessage.msg p1 lab1 S1).1 = (QueueMessage.msg p1 lab2 S2).1 := rfl
        exact dequeue_go_same_sender hQ1 hQ2 hsame
      have hlab : lab1 = lab2 := by injection hmsg
      have hS : S1 = S2 := by injection hmsg
      exact ⟨rfl, hlab, hS⟩

/-- Roles are preserved under any network transition (single or double replace). -/
private lemma role_preserved {N N2 : Network} {δ : net_label} (hTr : net_trans N δ N2) :
    ∀ (q0 : Role) (stqq : SessionTypeWithQueue),
      (q0, stqq) ∈ N → ∃ stqq', (q0, stqq') ∈ N2 := by
  intro q0 stqq hmem_q
  cases hTr with
  | io_send hSQ hmem =>
    rename_i r p stq stq' lab S
    by_cases heq : q0 = r
    · subst heq
      exact ⟨stq', by unfold Network.replace; simp⟩
    · exact ⟨stqq, mem_replace_other hmem_q heq⟩
  | io_recv hSQ hmem =>
    rename_i r p stq stq' lab S
    by_cases heq : q0 = r
    · subst heq
      exact ⟨stq', by unfold Network.replace; simp⟩
    · exact ⟨stqq, mem_replace_other hmem_q heq⟩
  | dequeue hSQ hmem =>
    rename_i r p stq stq' lab S
    by_cases heq : q0 = r
    · subst heq
      exact ⟨stq', by unfold Network.replace; simp⟩
    · exact ⟨stqq, mem_replace_other hmem_q heq⟩
  | comm _hne h_send h_recv hmem_p hmem_q2 =>
    rename_i p q lab S stqp stqp' stqq0 stqq0'
    by_cases heq_q : q0 = q
    · subst heq_q
      exact ⟨stqq0', by unfold Network.replace; simp⟩
    · by_cases heq_p : q0 = p
      · subst heq_p
        have hmid : (q0, stqp') ∈ Network.replace N q0 stqp' := by
          unfold Network.replace
          simp
        exact ⟨stqp', mem_replace_other hmid heq_q⟩
      · have hmid : (q0, stqq) ∈ Network.replace N p stqp' :=
          mem_replace_other hmem_q heq_p
        exact ⟨stqq, mem_replace_other hmid heq_q⟩

/-- A send capability (`p` can `τ_comm`) persists across an internal step that is not
    itself a `p`-send. Uses `WellFormed` (unique entries) and `st_trans` exclusivity:
    a dequeue at `p` would need `Tp` to both send and receive (impossible), and a
    `p`-send step is excluded by `hNotFirst`; otherwise `p`'s type is unchanged
    (receiver steps only extend the queue, preserving `st_trans`). -/
lemma comm_persists {N N2 : Network} (hwf : N.WellFormed)
    {p q : Role} {lab : Lab} {S : DataSort} {Tp Tp' : SessionType} {Qp : Queue}
    {Tq : SessionType} {Qq : Queue}
    (hne : p ≠ q)
    (hMemP : (p, (Tp, Qp)) ∈ N) (hMemQ : (q, (Tq, Qq)) ∈ N)
    (hST : st_trans Tp (st_label.out q lab S) Tp')
    {δ0 : net_label} (hStep : net_trans N δ0 N2) (hInt : is_internal_net_label δ0)
    (hNotFirst : ∀ q' lab' S', δ0 ≠ net_label.τ_comm p q' lab' S') :
    ∃ N'', net_trans N2 (net_label.τ_comm p q lab S) N'' := by
  cases hStep with
  | io_send hSQ hmem =>
    simp [is_internal_net_label] at hInt
  | io_recv hSQ hmem =>
    simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    rename_i r p0 stq stq' lab0 S0
    by_cases heq : r = p
    · subst heq
      rcases stq with ⟨T0, Q0⟩
      rcases stq' with ⟨T0', Q0'⟩
      have hEq : (Tp, Qp) = (T0, Q0) := network_mem_unique hwf hMemP hmem
      have hTp_eq : Tp = T0 := congrArg Prod.fst hEq
      subst hTp_eq
      cases hSQ with
      | dequeue hST0 hQ0 =>
        exact (sttr_out_not_inp hST hST0).elim
    · have hNe : p ≠ r := Ne.symm heq
      have hMemP2 : (p, (Tp, Qp)) ∈ Network.replace N r stq' :=
        mem_replace_other hMemP hNe
      rcases role_preserved (net_trans.dequeue hSQ hmem) q (Tq, Qq) hMemQ with ⟨stqq', hmem_q2⟩
      rcases stqq' with ⟨Tq2, Qq2⟩
      exact ⟨_, net_trans.comm hne (sq_trans.send hST) sq_trans.recv hMemP2 hmem_q2⟩
  | comm hneStep h_send h_recv hmem_p hmem_q2 =>
    rename_i p' q' lab' S' stqp stqp' stqq stqq'
    by_cases heq_send : p' = p
    · subst heq_send
      exfalso
      exact hNotFirst q' lab' S' rfl
    · have hNeSend : p ≠ p' := Ne.symm heq_send
      by_cases heq_recv : p = q'
      · subst heq_recv
        rcases stqq with ⟨Trecv, Qrecv⟩
        have hEq : (Tp, Qp) = (Trecv, Qrecv) := network_mem_unique hwf hMemP hmem_q2
        have hTp_eq : Tp = Trecv := congrArg Prod.fst hEq
        have hQp_eq : Qp = Qrecv := congrArg Prod.snd hEq
        subst hTp_eq
        subst hQp_eq
        cases h_recv with
        | recv =>
          have hMemP2 : (p, (Tp, Qp ++ [QueueMessage.msg p' lab' S'])) ∈
              (Network.replace N p' stqp').replace p (Tp, Qp ++ [QueueMessage.msg p' lab' S']) := by
            unfold Network.replace
            simp
          have hStep2 : net_trans N (net_label.τ_comm p' p lab' S')
              ((Network.replace N p' stqp').replace p (Tp, Qp ++ [QueueMessage.msg p' lab' S'])) :=
            net_trans.comm (Ne.symm hNeSend) h_send (@sq_trans.recv Tp Qp p' lab' S') hmem_p hmem_q2
          rcases role_preserved hStep2 q (Tq, Qq) hMemQ with ⟨stqq2', hmem_q2'⟩
          rcases stqq2' with ⟨Tq2, Qq2⟩
          exact ⟨_, net_trans.comm hne (sq_trans.send hST) sq_trans.recv hMemP2 hmem_q2'⟩
      · have hmid : (p, (Tp, Qp)) ∈ Network.replace N p' stqp' :=
          mem_replace_other hMemP hNeSend
        have hMemP2 : (p, (Tp, Qp)) ∈ (Network.replace N p' stqp').replace q' stqq' :=
          mem_replace_other hmid heq_recv
        rcases role_preserved (net_trans.comm hneStep h_send h_recv hmem_p hmem_q2) q (Tq, Qq)
          hMemQ with ⟨stqq', hmem_q2'⟩
        rcases stqq' with ⟨Tq2, Qq2⟩
        exact ⟨_, net_trans.comm hne (sq_trans.send hST) sq_trans.recv hMemP2 hmem_q2'⟩

/-- A dequeue capability persists across an internal step that is not itself that
    exact dequeue. Same-role different-label steps are impossible by
    `sq_dequeue_label_unique` (using `WellFormed` for unique entries); a send by the
    same role is impossible by `st_trans` exclusivity; receiver steps only extend the
    queue, preserving dequeueability via `queue_dequeue_append`. -/
lemma dequeue_persists {N N2 : Network} (hwf : N.WellFormed)
    {r p : Role} {lab : Lab} {S : DataSort} {T T' : SessionType} {Q Q' : Queue}
    (hMem : (r, (T, Q)) ∈ N) (hST : st_trans T (st_label.inp p lab S) T')
    (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q')
    {δ0 : net_label} (hStep : net_trans N δ0 N2) (hInt : is_internal_net_label δ0)
    (hNotFirst : δ0 ≠ net_label.τ_dequeue r p lab S) :
    ∃ N'', net_trans N2 (net_label.τ_dequeue r p lab S) N'' := by
  cases hStep with
  | io_send hSQ hmem =>
    simp [is_internal_net_label] at hInt
  | io_recv hSQ hmem =>
    simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    rename_i r' p0 stq0 stq0' lab0 S0
    by_cases heq_r : r' = r
    · subst heq_r
      rcases stq0 with ⟨T0, Q0⟩
      rcases stq0' with ⟨T0', Q0'⟩
      have hEq : (T, Q) = (T0, Q0) := network_mem_unique hwf hMem hmem
      have hT_eq : T = T0 := congrArg Prod.fst hEq
      have hQ_eq : Q = Q0 := congrArg Prod.snd hEq
      subst hT_eq
      subst hQ_eq
      cases hSQ with
      | dequeue hST0 hQ0 =>
        have hLab := sq_dequeue_label_unique (sq_trans.dequeue hST hQ) (sq_trans.dequeue hST0 hQ0)
        rcases hLab with ⟨rfl, rfl, rfl⟩
        exfalso
        exact hNotFirst rfl
    · have hNe : r ≠ r' := Ne.symm heq_r
      have hMem2 : (r, (T, Q)) ∈ Network.replace N r' stq0' :=
        mem_replace_other hMem hNe
      exact ⟨_, net_trans.dequeue (sq_trans.dequeue hST hQ) hMem2⟩
  | comm _hne h_send h_recv hmem_p hmem_q2 =>
    rename_i p' q' lab' S' stqp stqp' stqq stqq'
    by_cases heq_send : r = p'
    · subst heq_send
      rcases stqp with ⟨T0, Q0⟩
      have hEq : (T, Q) = (T0, Q0) := network_mem_unique hwf hMem hmem_p
      have hT_eq : T = T0 := congrArg Prod.fst hEq
      subst hT_eq
      cases h_send with
      | send hST0 =>
        exact (sttr_out_not_inp hST0 hST).elim
    · have hNeSend : r ≠ p' := heq_send
      by_cases heq_recv : r = q'
      · subst heq_recv
        rcases stqq with ⟨Trecv, Qrecv⟩
        have hEq : (T, Q) = (Trecv, Qrecv) := network_mem_unique hwf hMem hmem_q2
        have hT_eq : T = Trecv := congrArg Prod.fst hEq
        have hQ_eq : Q = Qrecv := congrArg Prod.snd hEq
        subst hT_eq
        subst hQ_eq
        cases h_recv with
        | recv =>
          have hQnew : (Q ++ [QueueMessage.msg p' lab' S']).dequeue (QueueMessage.msg p lab S) =
              some (Q' ++ [QueueMessage.msg p' lab' S']) :=
            queue_dequeue_append hQ
          have hMem2 : (r, (T, Q ++ [QueueMessage.msg p' lab' S'])) ∈
              (Network.replace N p' stqp').replace r (T, Q ++ [QueueMessage.msg p' lab' S']) := by
            unfold Network.replace
            simp
          exact ⟨_, net_trans.dequeue (sq_trans.dequeue hST hQnew) hMem2⟩
      · have hmid : (r, (T, Q)) ∈ Network.replace N p' stqp' :=
          mem_replace_other hMem hNeSend
        have hMem2 : (r, (T, Q)) ∈ (Network.replace N p' stqp').replace q' stqq' :=
          mem_replace_other hmid heq_recv
        exact ⟨_, net_trans.dequeue (sq_trans.dequeue hST hQ) hMem2⟩

/- Persistence note: enabled capabilities lapse only by being served.
    Use `comm_persists` / `dequeue_persists` directly at role granularity —
    this is what `Nest.FairScheduler.rr_comm_clause` / `rr_deq_clause` do. -/

/-- Prepend a single internal step to an infinite path (path shifting, Prop. 4.9).
    `f' 0 = N`, `f' (n+1) = path.seq n`. Tail `seq`/`δ` coincide definitionally
    (`rfl`), so fairness/liveness transfer via `rfl` for `n+1`. Only head (`i=0`)
    needs frame lemmas (`comm_persists`/`dequeue_persists`). -/
private def prepend_single {N N2 : Network} {δ0 : net_label}
    (hTr : net_trans N δ0 N2) (hInt : is_internal_net_label δ0)
    (path : InfiniteNetworkPath) (h0 : path.seq 0 = N2) :
    InfiniteNetworkPath := by
  let f' : ℕ → Network := fun i => match i with | 0 => N | Nat.succ n => path.seq n
  let dl' : ℕ → net_label := fun i => match i with | 0 => δ0 | Nat.succ n => path.δ n
  have hForm : ∀ i, ∃ (r p : Role) (lab : Lab) (S : DataSort),
      dl' i = net_label.τ_dequeue r p lab S ∨ dl' i = net_label.τ_comm r p lab S := by
    intro i
    cases i with
    | zero =>
      show ∃ (r p : Role) (lab : Lab) (S : DataSort),
        δ0 = net_label.τ_dequeue r p lab S ∨ δ0 = net_label.τ_comm r p lab S
      cases δ0 with
      | τ_dequeue r p lab S =>
        exact ⟨r, p, lab, S, Or.inl rfl⟩
      | τ_comm p q lab S =>
        exact ⟨p, q, lab, S, Or.inr rfl⟩
      | io_send r p lab S =>
        simp [is_internal_net_label] at hInt
      | io_recv r p lab S =>
        simp [is_internal_net_label] at hInt
    | succ n =>
      show ∃ (r p : Role) (lab : Lab) (S : DataSort),
        path.δ n = net_label.τ_dequeue r p lab S ∨ path.δ n = net_label.τ_comm r p lab S
      exact path.δ_form n
  have hStep : ∀ i, net_trans (f' i) (dl' i) (f' (i + 1)) := by
    intro i
    cases i with
    | zero =>
      have h2 : f' 1 = N2 := by simp [f', h0]
      show net_trans N δ0 (f' 1)
      rw [h2]
      exact hTr
    | succ n =>
      have h1 : f' (n + 1) = path.seq n := rfl
      have h1d : dl' (n + 1) = path.δ n := rfl
      have h2 : f' (n + 2) = path.seq (n + 1) := rfl
      rw [h1, h1d, h2]
      exact path.δ_tr n
  exact ⟨f', dl', hForm, hStep⟩

/-- Prepended path is fair if the suffix is fair (using persistence for head).
    Tail (`i+1`) follows from suffix fairness via definitional `δ` equality (`rfl`);
    head (`0`) uses `comm_persists`/`dequeue_persists` for the actual first step
    (`prepend.δ 0`, from `δ_spec`, not the original `δ0`), falling back to `k=0`
    when the first step already matches, otherwise via suffix fairness at `0`. -/
private lemma prepend_fair {N N2 : Network} {δ0 : net_label} (hwf : N.WellFormed)
    (hTr : net_trans N δ0 N2) (hInt : is_internal_net_label δ0)
    (path : InfiniteNetworkPath) (h0 : path.seq 0 = N2) (hFair : IsFair path) :
    IsFair (prepend_single hTr hInt path h0) := by
  intro i
  constructor
  · intro p hEnabled
    cases i with
    | zero =>
      rcases hEnabled with ⟨q, lab, S, N', hComm⟩
      cases hComm with
      | comm hne h_send h_recv hmem_p hmem_q =>
        cases h_recv with
        | recv =>
          rename_i Tq Qq
          rcases h_send with ⟨hST⟩
          rename_i Tp Tp' Qp
          have hSpec0 := (prepend_single hTr hInt path h0).δ_spec 0
          rcases hSpec0 with ⟨hCond0, hTr0⟩
          have hTr0' : net_trans N ((prepend_single hTr hInt path h0).δ 0) N2 := by
            have h1 : (prepend_single hTr hInt path h0).seq 0 = N := rfl
            have h2 : (prepend_single hTr hInt path h0).seq 1 = N2 := h0
            rw [h1, h2] at hTr0
            exact hTr0
          have hInt0 : is_internal_net_label ((prepend_single hTr hInt path h0).δ 0) := by
            rcases hCond0 with ⟨r, p0, lab0, S0, hEq | hEq⟩
            · rw [hEq]; simp [is_internal_net_label]
            · rw [hEq]; simp [is_internal_net_label]
          by_cases hFirst : ∃ q' lab' S', (prepend_single hTr hInt path h0).δ 0 =
              net_label.τ_comm p q' lab' S'
          · rcases hFirst with ⟨q', lab', S', hEq⟩
            exact ⟨0, Nat.zero_le 0, q', lab', S', hEq⟩
          · have hNotFirst : ∀ q' lab' S', (prepend_single hTr hInt path h0).δ 0 ≠
                net_label.τ_comm p q' lab' S' := by
              intro q' lab' S' hEq
              exact hFirst ⟨q', lab', S', hEq⟩
            rcases comm_persists hwf hne hmem_p hmem_q hST hTr0' hInt0 hNotFirst with
              ⟨N'', hComm2⟩
            have hEnabled2 : ∃ q lab S N', net_trans (path.seq 0) (net_label.τ_comm p q lab S) N' := by
              rw [← h0] at hComm2
              exact ⟨q, lab, S, N'', hComm2⟩
            rcases (hFair 0).1 p hEnabled2 with ⟨k, _, q', lab', S', hEq⟩
            exact ⟨k + 1, Nat.zero_le (k + 1), q', lab', S', hEq⟩
    | succ n =>
      have hEnabled2 : ∃ q lab S N', net_trans (path.seq n) (net_label.τ_comm p q lab S) N' :=
        hEnabled
      rcases (hFair n).1 p hEnabled2 with ⟨k, hk, q', lab', S', hEq⟩
      exact ⟨k + 1, Nat.succ_le_succ hk, q', lab', S', hEq⟩
  · intro r p lab S hEnabled
    cases i with
    | zero =>
      rcases hEnabled with ⟨N', hDeq⟩
      cases hDeq with
      | dequeue hSQ hmem =>
        cases hSQ with
        | dequeue hST hQ =>
          rename_i T Q T' Q'
          have hSpec0 := (prepend_single hTr hInt path h0).δ_spec 0
          rcases hSpec0 with ⟨hCond0, hTr0⟩
          have hTr0' : net_trans N ((prepend_single hTr hInt path h0).δ 0) N2 := by
            have h1 : (prepend_single hTr hInt path h0).seq 0 = N := rfl
            have h2 : (prepend_single hTr hInt path h0).seq 1 = N2 := h0
            rw [h1, h2] at hTr0
            exact hTr0
          have hInt0 : is_internal_net_label ((prepend_single hTr hInt path h0).δ 0) := by
            rcases hCond0 with ⟨r0, p0, lab0, S0, hEq | hEq⟩
            · rw [hEq]; simp [is_internal_net_label]
            · rw [hEq]; simp [is_internal_net_label]
          by_cases hFirst : (prepend_single hTr hInt path h0).δ 0 =
              net_label.τ_dequeue r p lab S
          · exact ⟨0, Nat.zero_le 0, hFirst⟩
          · have hNotFirst : (prepend_single hTr hInt path h0).δ 0 ≠
                net_label.τ_dequeue r p lab S := hFirst
            rcases dequeue_persists hwf hmem hST hQ hTr0' hInt0 hNotFirst with
              ⟨N'', hDeq2⟩
            have hEnabled2 : ∃ N', net_trans (path.seq 0)
                (net_label.τ_dequeue r p lab S) N' := by
              rw [← h0] at hDeq2
              exact ⟨N'', hDeq2⟩
            rcases (hFair 0).2 r p lab S hEnabled2 with ⟨k, _, hEq⟩
            exact ⟨k + 1, Nat.zero_le (k + 1), hEq⟩
    | succ n =>
      have hEnabled2 : ∃ N', net_trans (path.seq n)
          (net_label.τ_dequeue r p lab S) N' := hEnabled
      rcases (hFair n).2 r p lab S hEnabled2 with ⟨k, hk, hEq⟩
      exact ⟨k + 1, Nat.succ_le_succ hk, hEq⟩

/-- If the prepended path is output-live, so is the suffix (witness `k' ≥ i+1`
    must lie in the tail, `k' = k+1`, and `δ` coincides definitionally via `rfl`). -/
private lemma prepend_live_transfer {N N2 : Network} {δ0 : net_label}
    (hTr : net_trans N δ0 N2) (hInt : is_internal_net_label δ0)
    (path : InfiniteNetworkPath) (h0 : path.seq 0 = N2)
    (hLive : IsOutputLiveInfinitePath (prepend_single hTr hInt path h0)) :
    IsOutputLiveInfinitePath path := by
  intro i p Qp hHasQ q lab S hDeqAble
  have hHasQ' : NetworkHasQueue ((prepend_single hTr hInt path h0).seq (i + 1)) p Qp :=
    hHasQ
  rcases hLive (i + 1) p Qp hHasQ' q lab S hDeqAble with ⟨k', hk', hEq⟩
  cases k' with
  | zero =>
    exfalso
    omega
  | succ k =>
    have hk : i ≤ k := by omega
    exact ⟨k, hk, hEq⟩

/-- Single-step persistence: live + well-formed + one internal step gives live target.
    Stuck part via `net_trans_star.trans` with single step; infinite part via `prepend_single`
    (`prepend_fair` to get fair extension, apply liveness, transfer via
    `prepend_live_transfer`). -/
private lemma output_live_persistent_single {N N2 : Network} (hwf : N.WellFormed)
    (hLive : IsOutputLiveNetwork N) {δ0 : net_label} (hTr : net_trans N δ0 N2)
    (hInt : is_internal_net_label δ0) :
    IsOutputLiveNetwork N2 := by
  constructor
  · intro path h0 hFair
    have hPreFair : IsFair (prepend_single hTr hInt path h0) :=
      prepend_fair hwf hTr hInt path h0 hFair
    have hPreSeq0 : (prepend_single hTr hInt path h0).seq 0 = N := rfl
    have hPreLive : IsOutputLiveInfinitePath (prepend_single hTr hInt path h0) :=
      hLive.1 _ hPreSeq0 hPreFair
    exact prepend_live_transfer hTr hInt path h0 hPreLive
  · intro N' hStar' hStuck'
    exact hLive.2 N' (net_trans_star.trans (net_trans_star.step hInt hTr (net_trans_star.refl _)) hStar') hStuck'

/-- Output-liveness is preserved under τ steps (Prop. 2.14 for `IsOutputLiveNetwork`).

    The infinite-path conjunct follows as in the cited Prop. 4.9 (path shifting);
    the stuck-no-orphan conjunct follows by transitivity of `net_trans_star`
    (a stuck reachable from `Ni` is reachable from `N`).
    Needs `N` well-formed (no duplicate roles): otherwise a duplicate role can make
    `N` vacuously live (two enabled dequeues disabling each other, so no fair infinite
    path) while a successor is non-live. All callers have `N.WellFormed` available. -/
lemma output_live_persistent {N Ni : Network}
    (hwf : N.WellFormed) (h : IsOutputLiveNetwork N) (hStar : net_trans_star N Ni) :
    IsOutputLiveNetwork Ni := by
  revert hwf h
  induction hStar with
  | refl =>
    intro hwf h
    exact h
  | step hInt hTr hStar' ih =>
    intro hwf h
    have hwf2 : _ := Network.wellFormedPreserved _ _ _ hwf hTr hInt
    have h2 : IsOutputLiveNetwork _ :=
      output_live_persistent_single hwf h hTr hInt
    exact ih hwf2 h2
