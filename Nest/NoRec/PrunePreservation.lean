import Nest.SessionUtils
import Nest.MonitorToolkit
import Nest.StuckWitness
import Nest.NoRec.PruneFunctions
import Nest.NoRec.NoRecEncoder
import Nest.NoRec.DrainCore

/-!
# PrunePreservation: step classification and prune-function preservation.

Dequeue-scan skipping, over_trans vs st_trans step classification (`deep_prepend_*`),
fuel-free prune-function key/map lemmas, and `pruneGo` NoDupl/NoRec preservation.
Uses the public substitution/`Has` lemmas from `Nest.SessionAdequacy`.
-/

section DequeueSkip

/-- Dequeue scans skip non-`p` prefixes: reaching the oldest
    `p`-message drops exactly it (accumulator-generalized induction;
    the head is apart from the target by sender, then by message). -/
lemma dequeue_skip_seen {p : Role} {lab : Lab} {S : DataSort}
    {rest : Queue} {acc seen : Queue} (hseen : ∀ m ∈ seen, m.1 ≠ p) :
    Queue.dequeue.go acc (seen ++ QueueMessage.msg p lab S :: rest)
      (QueueMessage.msg p lab S) = some (acc ++ seen ++ rest) := by
  revert hseen
  induction seen generalizing acc with
  | nil =>
    intro hseen
    simp [Queue.dequeue.go]
  | cons s0 seen' ih =>
    intro hseen
    have h0 : s0.1 ≠ p := hseen _ (List.mem_cons.mpr (Or.inl rfl))
    have hne : s0 ≠ QueueMessage.msg p lab S := by
      intro hcon
      rw [hcon] at h0
      simp at h0
    have h0' : s0.1 ≠ (QueueMessage.msg p lab S).1 := h0
    have hrest : ∀ m ∈ seen', m.1 ≠ p := fun m hm =>
      hseen m (List.mem_cons.mpr (Or.inr hm))
    have hstep := ih (acc := acc ++ [s0]) hrest
    simp only [List.cons_append] at *
    simp only [Queue.dequeue.go, hne, h0'] at *
    simpa [List.append_assoc] using hstep


/-- At an `extC`-`p` head holding a `p`-message, every step dequeues:
    specs need absence, sends need `intC`. -/
theorem extC_step_is_dequeue {p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Q : Queue}
    {α : st_label} {stq' : SessionTypeWithQueue} {m : QueueMessage}
    (hmem : m ∈ Q) (hm1 : m.1 = p)
    (hS : over_trans (SessionType.externalChoice p branches, Q) α stq') :
    ∃ (T' : SessionType) (Q' : Queue) (lab : Lab) (S : DataSort),
      α = st_label.inp p lab S ∧ stq' = (T', Q') ∧
      st_trans (SessionType.externalChoice p branches) (st_label.inp p lab S) T' ∧
      Q.dequeue (QueueMessage.msg p lab S) = some Q' := by
  cases hS with
  | dequeue hEq hmemST hQd =>
    cases hEq
    exact ⟨_, _, _, _, rfl, rfl, st_trans.extC hmemST, hQd⟩
  | specInp hEq _ hAbs =>
    cases hEq
    exact (hAbs _ hmem hm1).elim
  | sendFresh hEq hST hFresh =>
    cases hEq
  | tauUnfold hU => cases hU


/-- Two steps at an `extC`-`p` head holding a `p`-message coincide:
    both dequeues hit the oldest `p`-message and `NoDupl` pins the
    target. -/
theorem extC_steps_coincide {p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Q : Queue}
    (hND : (SessionType.externalChoice p branches).NoDupl)
    {α1 α2 : st_label} {stq1 stq2 : SessionTypeWithQueue} {m : QueueMessage}
    (hmem : m ∈ Q) (hm1 : m.1 = p)
    (hS1 : over_trans (SessionType.externalChoice p branches, Q) α1 stq1)
    (hS2 : over_trans (SessionType.externalChoice p branches, Q) α2 stq2) :
    α1 = α2 ∧ stq1 = stq2 := by
  obtain ⟨T1, Q1, lab1, S1, rfl, rfl, hST1, hQd1⟩ :=
    extC_step_is_dequeue hmem hm1 hS1
  obtain ⟨T2, Q2, lab2, S2, rfl, rfl, hST2, hQd2⟩ :=
    extC_step_is_dequeue hmem hm1 hS2
  cases hST1 with
  | extC hmem1 =>
    cases hST2 with
    | extC hmem2 =>
      obtain ⟨seen1, left1, hQeq1, -, hseen1⟩ := queue_dequeue_some_iff hQd1
      obtain ⟨seen2, left2, hQeq2, -, hseen2⟩ := queue_dequeue_some_iff hQd2
      have hQeq1' : Q = seen1 ++ QueueMessage.msg p lab1 S1 :: left1 := by
        simpa using hQeq1
      have hQeq2' : Q = seen2 ++ QueueMessage.msg p lab2 S2 :: left2 := by
        simpa using hQeq2
      have hEq : QueueMessage.msg p lab1 S1 = QueueMessage.msg p lab2 S2 :=
        oldest_from_unique ⟨seen1, left1, hQeq1', rfl, hseen1⟩
          ⟨seen2, left2, hQeq2', rfl, hseen2⟩
      rw [QueueMessage.msg.injEq] at hEq
      obtain ⟨-, rfl, rfl⟩ := hEq
      have hT : T1 = T2 := ext_target_unique_norec hND hmem1 hmem2
      have hQ : Q1 = Q2 := Option.some_inj.mp (hQd1.symm.trans hQd2)
      subst hT
      subst hQ
      exact ⟨rfl, rfl⟩


/-- At an `extC`-`p` head with no `p`-message queued, every step
    is a spec step (dequeus need an owner message in the queue,
    sends need `intC`). -/
theorem extC_step_is_spec {p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Q : Queue}
    {α : st_label} {stq' : SessionTypeWithQueue}
    (hAbs : ∀ m ∈ Q, m.1 ≠ p)
    (hS : over_trans (SessionType.externalChoice p branches, Q) α stq') :
    ∃ (T' : SessionType) (lab : Lab) (S : DataSort),
      α = st_label.inp p lab S ∧ stq' = (T', Q) ∧
      st_trans (SessionType.externalChoice p branches) (st_label.inp p lab S) T' := by
  cases hS with
  | @dequeue _ _ _ _ _ lab S _ hEq hmem hQd =>
    cases hEq
    obtain ⟨seen2, left2, hQeq2, hseen2⟩ := dequeue_oldest_of_some hQd
    have hmemQ : QueueMessage.msg p lab S ∈ Q := by
      rw [hQeq2]
      simp
    exact (hAbs _ hmemQ rfl).elim
  | specInp hEq hmem hAbs =>
    cases hEq
    exact ⟨_, _, _, rfl, rfl, st_trans.extC hmem⟩
  | sendFresh hEq hST hFresh =>
    cases hEq
  | tauUnfold hU => cases hU


/-- At an `intC` head, every step is a send step. -/
theorem intC_step_is_send
    {branches : List (Role × Lab × DataSort × SessionType)} {Q : Queue}
    {α : st_label} {stq' : SessionTypeWithQueue}
    (hS : over_trans (SessionType.internalChoice branches, Q) α stq') :
    ∃ (T' : SessionType) (p : Role) (lab : Lab) (S : DataSort),
      α = st_label.out p lab S ∧ stq' = (T', Q) ∧
      st_trans (SessionType.internalChoice branches) (st_label.out p lab S) T' := by
  cases hS with
  | dequeue hEq hmem hQd => cases hEq
  | specInp hEq hmem hAbs => cases hEq
  | sendFresh hEq hST hFresh =>
    exact ⟨_, _, _, _, rfl, rfl, hST⟩
  | tauUnfold hU => cases hU


/-- Prepend a dequeue step onto a `Deep` witness at an `extC` head:
    other first steps are impossible (specs need absence, but the
    dequeued message is present; sends need `intC`), same-key
    dequeues coincide. -/
theorem deep_prepend_dequeue_at_extC {p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Q Q1 : Queue}
    {T1 : SessionType} {labW : Lab} {SW : DataSort}
    (hND : (SessionType.externalChoice p branches).NoDupl)
    (hmemW : (labW, SW, T1) ∈ branches)
    (hQdW : Q.dequeue (QueueMessage.msg p labW SW) = some Q1)
    (hTail : CanAlwaysDrainInternalDeep T1 Q1)
    (hHeadInt : ∀ (branches2 : List (Role × Lab × DataSort × SessionType)),
      SessionType.externalChoice p branches =
        SessionType.internalChoice branches2 → branches2 ≠ [] →
      ∀ (br : Role × Lab × DataSort × SessionType),
        br ∈ branches2 → CanAlwaysDrainInternalDeepCore br.2.2.2 Q)
    (hHeadExt : ∀ (q : Role) (branches2 : List (Lab × DataSort × SessionType)),
      SessionType.externalChoice p branches =
        SessionType.externalChoice q branches2 → branches2 ≠ [] →
      NoDequeueFrom (SessionType.externalChoice p branches) Q →
      ∃ (br : Lab × DataSort × SessionType),
        br ∈ branches2 ∧ CanAlwaysDrainInternalDeepCore br.2.2 Q) :
    CanAlwaysDrainInternalDeep (SessionType.externalChoice p branches) Q := by
  obtain ⟨Tn, ρ', hTr, hallT⟩ := hTail
  obtain ⟨seenW, leftW, hQeqW, -, hseenW⟩ := queue_dequeue_some_iff hQdW
  have hQeqW' : Q = seenW ++ QueueMessage.msg p labW SW :: leftW := by
    simpa using hQeqW
  have hpmem : QueueMessage.msg p labW SW ∈ Q := by
    rw [hQeqW]
    simp
  have hm1 : (QueueMessage.msg p labW SW).1 = p := rfl
  refine ⟨Tn, st_label.inp p labW SW :: ρ',
    over_trans_trace.step (over_trans.dequeue rfl hmemW hQdW) hTr, ?_⟩
  intro Ti Qi σ1 σ2 g1 g2 geq
  cases σ1 with
  | nil =>
    have hST := overTrTrace_nil_eq g1
    cases hST
    refine ⟨hHeadInt, hHeadExt, ?_⟩
    intro X B hEq
    cases hEq
  | cons α σ1' =>
    cases g1 with
    | step hS hT2 =>
      obtain ⟨T', Q', lab, S, -, hEqS, hST, hQd⟩ :=
        extC_step_is_dequeue hpmem hm1 hS
      subst hEqS
      cases hST with
      | extC hmem =>
        obtain ⟨seen2, left2, hQeq2, hseen2⟩ := dequeue_oldest_of_some hQd
        have hEq : QueueMessage.msg p labW SW = QueueMessage.msg p lab S :=
          oldest_from_unique ⟨seenW, leftW, hQeqW', rfl, hseenW⟩
            ⟨seen2, left2, hQeq2, rfl, hseen2⟩
        rw [QueueMessage.msg.injEq] at hEq
        obtain ⟨-, rfl, rfl⟩ := hEq
        have hT : T1 = T' := ext_target_unique_norec hND hmemW hmem
        have hQ : Q1 = Q' :=
          Option.some_inj.mp (hQdW.symm.trans hQd)
        subst hT
        subst hQ
        have hρ : ρ' = σ1' ++ σ2 := by
          rw [List.cons_append] at geq
          cases geq
          rfl
        exact hallT Ti Qi σ1' σ2 hT2 g2 hρ


/-- Prepend a spec step onto a `Deep` witness at an `extC` head under
    absence: dequeues need an owner message, sends need `intC`;
    same-key specs coincide. -/
theorem deep_prepend_spec_at_extC {p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Q : Queue}
    {T1 : SessionType} {labW : Lab} {SW : DataSort}
    (hND : (SessionType.externalChoice p branches).NoDupl)
    (hmemW : (labW, SW, T1) ∈ branches)
    (hAbsW : ∀ m ∈ Q, m.1 ≠ p)
    (hTail : CanAlwaysDrainInternalDeep T1 Q)
    (hHeadInt : ∀ (branches2 : List (Role × Lab × DataSort × SessionType)),
      SessionType.externalChoice p branches =
        SessionType.internalChoice branches2 → branches2 ≠ [] →
      ∀ (br : Role × Lab × DataSort × SessionType),
        br ∈ branches2 → CanAlwaysDrainInternalDeepCore br.2.2.2 Q)
    (hHeadExt : ∀ (q : Role) (branches2 : List (Lab × DataSort × SessionType)),
      SessionType.externalChoice p branches =
        SessionType.externalChoice q branches2 → branches2 ≠ [] →
      NoDequeueFrom (SessionType.externalChoice p branches) Q →
      ∃ (br : Lab × DataSort × SessionType),
        br ∈ branches2 ∧ CanAlwaysDrainInternalDeepCore br.2.2 Q) :
    CanAlwaysDrainInternalDeep (SessionType.externalChoice p branches) Q := by
  obtain ⟨Tn, ρ', hTr, hallT⟩ := hTail
  refine ⟨Tn, st_label.inp p labW SW :: ρ',
    over_trans_trace.step (over_trans.specInp rfl hmemW hAbsW) hTr, ?_⟩
  intro Ti Qi σ1 σ2 g1 g2 geq
  cases σ1 with
  | nil =>
    have hST := overTrTrace_nil_eq g1
    cases hST
    refine ⟨hHeadInt, hHeadExt, ?_⟩
    intro X B hEq
    cases hEq
  | cons α σ1' =>
    cases g1 with
    | step hS hT2 =>
      obtain ⟨T', lab, S, hEqA, hEqS, hST⟩ :=
        extC_step_is_spec hAbsW hS
      subst hEqS
      rw [List.cons_append] at geq
      cases geq
      cases hEqA
      cases hST with
      | extC hmem =>
        have hT : T1 = T' := ext_target_unique_norec hND hmemW hmem
        subst hT
        exact hallT Ti Qi σ1' σ2 hT2 g2 rfl


/-- Prepend a send step onto a `Deep` witness at an `intC` head:
    dequeues/specs need `inp` (unavailable at `intC`); same-key
    sends coincide. -/
theorem deep_prepend_send_at_intC
    {branches : List (Role × Lab × DataSort × SessionType)} {Q : Queue}
    {T1 : SessionType} {p0 : Role} {lp0 : Lab} {Sp0 : DataSort}
    (hND : (SessionType.internalChoice branches).NoDupl)
    (hmemW : (p0, lp0, Sp0, T1) ∈ branches)
    (hFreshW : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
      (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r')
    (hTail : CanAlwaysDrainInternalDeep T1 Q)
    (hHeadInt : ∀ (branches2 : List (Role × Lab × DataSort × SessionType)),
      SessionType.internalChoice branches =
        SessionType.internalChoice branches2 → branches2 ≠ [] →
      ∀ (br : Role × Lab × DataSort × SessionType),
        br ∈ branches2 → CanAlwaysDrainInternalDeepCore br.2.2.2 Q)
    (hHeadExt : ∀ (q : Role) (branches2 : List (Lab × DataSort × SessionType)),
      SessionType.internalChoice branches =
        SessionType.externalChoice q branches2 → branches2 ≠ [] →
      NoDequeueFrom (SessionType.internalChoice branches) Q →
      ∃ (br : Lab × DataSort × SessionType),
        br ∈ branches2 ∧ CanAlwaysDrainInternalDeepCore br.2.2 Q) :
    CanAlwaysDrainInternalDeep (SessionType.internalChoice branches) Q := by
  obtain ⟨Tn, ρ', hTr, hallT⟩ := hTail
  have hSTW : st_trans (SessionType.internalChoice branches)
      (st_label.out p0 lp0 Sp0) T1 :=
    st_trans.intC hmemW
  have hSend : over_trans (SessionType.internalChoice branches, Q)
      (st_label.out p0 lp0 Sp0) (T1, Q) :=
    over_trans.sendFresh rfl hSTW hFreshW
  refine ⟨Tn, st_label.out p0 lp0 Sp0 :: ρ',
    over_trans_trace.step hSend hTr, ?_⟩
  intro Ti Qi σ1 σ2 g1 g2 geq
  cases σ1 with
  | nil =>
    have hST := overTrTrace_nil_eq g1
    cases hST
    refine ⟨hHeadInt, hHeadExt, ?_⟩
    intro X B hEq
    cases hEq
  | cons α σ1' =>
    cases g1 with
    | step hS hT2 =>
      obtain ⟨T', q, l, s, hEqA, hEqS, hST⟩ :=
        intC_step_is_send hS
      subst hEqS
      rw [List.cons_append] at geq
      cases geq
      cases hEqA
      cases hST with
      | intC hmem =>
        have hT : T1 = T' := int_target_unique_norec hND hmemW hmem
        subst hT
        exact hallT Ti Qi σ1' σ2 hT2 g2 rfl


-- ================================================================
-- Pruning preserves drainability (`drain_survives_pruning_norec`).
-- ================================================================


end DequeueSkip

section PruneKeys

/-- Mapped internal branches keep their `(role, label)` keys. -/
theorem prune_go_int_keys (p : Role) (lab : Lab) (S : DataSort)
    (branches : List (Role × Lab × DataSort × SessionType)) :
    List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
      (pruneGoInt p lab S branches) =
    List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
      branches := by
  induction branches with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneGoInt]
    by_cases hqp : q = p
    · subst hqp
      simp [ih]
    · have hbeq : ¬ ((q == p) = true) :=
        fun hcon => hqp (beq_iff_eq.mp hcon)
      rw [ite_eq_right hbeq]
      simp [ih]


/-- Mapped external branches keep their labels. -/
private theorem prune_go_ext_keys (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (branches : List (Lab × DataSort × SessionType)),
    List.map (fun x : Lab × DataSort × SessionType => x.1)
      (pruneGoExt p lab S branches) =
    List.map (fun x : Lab × DataSort × SessionType => x.1) branches := by
  intro branches
  induction branches with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨l, S', U⟩ := hd
    simp only [pruneGoExt, List.map_cons, ih]


/-- Original non-`p` branches map into mapped internal branches. -/
theorem prune_go_int_map_mem (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (branches : List (Role × Lab × DataSort × SessionType))
    (x : Role × Lab × DataSort × SessionType),
    x ∈ branches → x.1 ≠ p →
    (x.1, x.2.1, x.2.2.1, pruneFirstInputGo p lab S x.2.2.2) ∈
      pruneGoInt p lab S branches := by
  intro branches
  induction branches with
  | nil =>
    intro x hm _
    simp at hm
  | cons hd tl ih =>
    intro x hm hne
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneGoInt]
    rcases List.mem_cons.mp hm with hxh | htl
    · subst hxh
      by_cases hbeq : (q == p) = true
      · exfalso
        exact hne (beq_iff_eq.mp hbeq)
      · rw [ite_eq_right hbeq]
        exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (ih _ htl hne))


/-- A witnessed branch forces the `goInt` existence check. -/
theorem prune_has_int_true_of_mem (p : Role) (lab : Lab) (S : DataSort)
    (q : Role) (l : Lab) (S' : DataSort) (U : SessionType)
    (hne : q ≠ p) (hU : pruneFirstInputHas p lab S U = true) :
    ∀ (bs : List (Role × Lab × DataSort × SessionType)),
    (q, l, S', U) ∈ bs → pruneHasInt p lab S bs = true := by
  intro bs
  induction bs with
  | nil =>
    intro hm
    exact False.elim (List.not_mem_nil hm)
  | cons hd tl ih =>
    intro hm
    obtain ⟨q0, l0, S0, U0⟩ := hd
    simp only [pruneHasInt]
    rcases List.mem_cons.mp hm with h | h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp [hne, hU]
    · have h2 := ih h
      simp [h2]


/-- Membership in mapped external branches resolves to an original
    branch target. -/
private theorem prune_go_ext_mem (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (branches : List (Lab × DataSort × SessionType))
    (br : Lab × DataSort × SessionType),
    br ∈ pruneGoExt p lab S branches →
    ∃ (l : Lab) (S' : DataSort) (U : SessionType),
      (l, S', U) ∈ branches ∧
        br = (l, S', pruneFirstInputGo p lab S U) := by
  intro branches
  induction branches with
  | nil =>
    intro br hmem
    simp [pruneGoExt] at hmem
  | cons hd tl ih =>
    intro br hmem
    obtain ⟨l, S', U⟩ := hd
    simp only [pruneGoExt, List.mem_cons] at hmem
    rcases hmem with hmem | hmem
    · obtain rfl := hmem
      exact ⟨l, S', U, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨l2, S2, U2, hm2, heq⟩ := ih _ hmem
      exact ⟨l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), heq⟩


/-- Membership in mapped internal branches resolves to an original
    branch (kept as-is if `p`-sender, pruned otherwise). -/
theorem prune_go_int_mem (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (branches : List (Role × Lab × DataSort × SessionType))
    (br : Role × Lab × DataSort × SessionType),
    br ∈ pruneGoInt p lab S branches →
    (∃ (q : Role) (l : Lab) (S' : DataSort) (U : SessionType),
      (q, l, S', U) ∈ branches ∧ q = p ∧
        br = (q, l, S', U)) ∨
    (∃ (q : Role) (l : Lab) (S' : DataSort) (U : SessionType),
      (q, l, S', U) ∈ branches ∧ q ≠ p ∧
        br = (q, l, S', pruneFirstInputGo p lab S U)) := by
  intro branches
  induction branches with
  | nil =>
    intro br hmem
    simp [pruneGoInt] at hmem
  | cons hd tl ih =>
    intro br hmem
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneGoInt, List.mem_cons] at hmem
    rcases hmem with hmem | hmem
    · by_cases hqp : q = p
      · have hbeq : ((q == p) = true) := beq_iff_eq.mpr hqp
        rw [ite_eq_left hbeq] at hmem
        obtain rfl := hmem
        exact Or.inl ⟨q, l, S', U, List.mem_cons.mpr (Or.inl rfl), hqp,
          rfl⟩
      · have hbeq : ¬ ((q == p) = true) :=
          fun hcon => hqp (beq_iff_eq.mp hcon)
        rw [ite_eq_right hbeq] at hmem
        obtain rfl := hmem
        exact Or.inr ⟨q, l, S', U, List.mem_cons.mpr (Or.inl rfl), hqp,
          rfl⟩
    · obtain h | h := ih _ hmem
      · obtain ⟨q2, l2, S2, U2, hm2, heq2, heq⟩ := h
        exact Or.inl ⟨q2, l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), heq2,
          heq⟩
      · obtain ⟨q2, l2, S2, U2, hm2, hne, heq⟩ := h
        exact Or.inr ⟨q2, l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), hne,
          heq⟩



end PruneKeys

section PrunePreservation

/-- Pruning preserves `NoDupl` (resolved targets are branch targets or
    `tEnd`; mapped branches keep their keys). -/
theorem prune_first_input_go_preserves_no_dupl (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (n : Nat) (U : SessionType), sizeOf U ≤ n → U.NoDupl →
    (pruneFirstInputGo p lab S U).NoDupl := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hsize hND
    cases U with
    | tEnd =>
      simp only [pruneFirstInputGo]
      exact SessionType.NoDupl.end
    | tVar X =>
      simp only [pruneFirstInputGo]
      exact SessionType.NoDupl.tVar X
    | tRec X B =>
      have hBND : B.NoDupl := by cases hND with | tRec h => exact h
      have hlt : sizeOf B < n := by
        have h1 : sizeOf B < sizeOf (SessionType.tRec X B) := by simp
        omega
      simp only [pruneFirstInputGo]
      exact SessionType.NoDupl.tRec (ih _ hlt _ (Nat.le_refl _) hBND)
    | internalChoice branches =>
      cases hND with
      | internalChoice h_nodup h_ne h_branches =>
        simp only [pruneFirstInputGo]
        refine SessionType.NoDupl.internalChoice ?_ ?_ ?_
        · rw [prune_go_int_keys]
          exact h_nodup
        · intro hcon
          apply h_ne
          cases branches with
          | nil => rfl
          | cons hd tl => simp [pruneGoInt] at hcon
        · intro x hmem
          obtain h | h := prune_go_int_mem p lab S branches x hmem
          · obtain ⟨q, l, S', U, hmemU, _, rfl⟩ := h
            exact h_branches _ hmemU
          · obtain ⟨q, l, S', U, hmemU, hqp, rfl⟩ := h
            have hltU : sizeOf U < n := by
              have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice hmemU
              omega
            exact ih _ hltU _ (Nat.le_refl _)
              (h_branches _ hmemU)
    | externalChoice q branches =>
      by_cases hbeq : (q == p) = true
      · simp only [pruneFirstInputGo, hbeq, ite_true]
        cases hND with
        | externalChoice h_nodup h_ne h_branches =>
          refine match hF : branches.find? (fun b => match b with
              | (l, S', _) => l == lab && S' == S) with
            | none => ?_
            | some v => ?_
          · simp only [hF]
            exact SessionType.NoDupl.end
          · obtain ⟨l, S', U⟩ := v
            obtain ⟨hmemU, -⟩ := find?_some_mem hF
            simp only [hF]
            exact h_branches _ hmemU
      · simp only [pruneFirstInputGo, hbeq]
        cases hND with
        | externalChoice h_nodup h_ne h_branches =>
          refine SessionType.NoDupl.externalChoice ?_ ?_ ?_
          · rw [prune_go_ext_keys]
            exact h_nodup
          · intro hcon
            apply h_ne
            cases branches with
            | nil => rfl
            | cons hd tl => simp [pruneGoExt] at hcon
          · intro x hmem
            obtain ⟨l, S', U, hmemU, rfl⟩ :=
              prune_go_ext_mem p lab S branches x hmem
            have hltU : sizeOf U < n := by
              have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice (p := q)
                hmemU
              omega
            exact ih _ hltU _ (Nat.le_refl _) (h_branches _ hmemU)


/-- Original external branches map into mapped external branches. -/
theorem prune_go_ext_map_mem (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (branches : List (Lab × DataSort × SessionType))
    (x : Lab × DataSort × SessionType),
    x ∈ branches →
    (x.1, x.2.1, pruneFirstInputGo p lab S x.2.2) ∈
      pruneGoExt p lab S branches := by
  intro branches
  induction branches with
  | nil =>
    intro x hm
    simp at hm
  | cons hd tl ih =>
    intro x hm
    obtain ⟨l, S', U⟩ := hd
    obtain ⟨l2, S2, U2⟩ := x
    simp only [pruneGoExt, List.mem_cons] at hm ⊢
    rcases hm with hm | hm
    · obtain ⟨rfl, rfl, rfl⟩ := hm
      exact Or.inl rfl
    · exact Or.inr (ih _ hm)


/-- A witnessed external branch forces the `goExt` existence check. -/
theorem prune_has_ext_true_of_mem (p : Role) (lab : Lab) (S : DataSort)
    (l : Lab) (S' : DataSort) (U : SessionType)
    (hU : pruneFirstInputHas p lab S U = true) :
    ∀ (bs : List (Lab × DataSort × SessionType)),
    (l, S', U) ∈ bs → pruneHasExt p lab S bs = true := by
  intro bs
  induction bs with
  | nil =>
    intro hm
    exact False.elim (List.not_mem_nil hm)
  | cons hd tl ih =>
    intro hm
    obtain ⟨l0, S0, U0⟩ := hd
    simp only [pruneHasExt]
    rcases List.mem_cons.mp hm with h | h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp [hU]
    · have h2 := ih h
      simp [h2]


/-- Membership in deep-filtered internal branches resolves to a reaching
    original branch target. -/
theorem prune_go_deep_int_mem (p : Role) (lab : Lab) (S : DataSort)
    (fuel : Nat) :
    ∀ (branches : List (Role × Lab × DataSort × SessionType))
    (br : Role × Lab × DataSort × SessionType),
    br ∈ pruneGoDeepInt p lab S fuel branches →
    ∃ (q : Role) (l : Lab) (S' : DataSort) (U : SessionType),
      (q, l, S', U) ∈ branches ∧
        pruneFirstInputDeepHas p lab S U = true ∧
        br = (q, l, S', pruneFirstInputDeepGo p lab S fuel U) := by
  intro branches
  induction branches with
  | nil =>
    intro br hmem
    simp [pruneGoDeepInt] at hmem
  | cons hd tl ih =>
    intro br hmem
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneGoDeepInt] at hmem
    by_cases hHasU : pruneFirstInputDeepHas p lab S U = true
    · rw [ite_eq_left hHasU] at hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · obtain rfl := hmem
        exact ⟨q, l, S', U, List.mem_cons.mpr (Or.inl rfl), hHasU, rfl⟩
      · obtain ⟨q2, l2, S2, U2, hm2, hHasU2, heq⟩ := ih _ hmem
        exact ⟨q2, l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), hHasU2,
          heq⟩
    · rw [ite_eq_right hHasU] at hmem
      obtain ⟨q2, l2, S2, U2, hm2, hHasU2, heq⟩ := ih _ hmem
      exact ⟨q2, l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), hHasU2, heq⟩


/-- A reaching branch maps into deep-filtered internal branches. -/
theorem prune_go_deep_int_map_mem (p : Role) (lab : Lab)
    (S : DataSort) (fuel : Nat) :
    ∀ (branches : List (Role × Lab × DataSort × SessionType))
    (x : Role × Lab × DataSort × SessionType),
    x ∈ branches → pruneFirstInputDeepHas p lab S x.2.2.2 = true →
    (x.1, x.2.1, x.2.2.1, pruneFirstInputDeepGo p lab S fuel x.2.2.2) ∈
      pruneGoDeepInt p lab S fuel branches := by
  intro branches
  induction branches with
  | nil =>
    intro x hm _
    simp at hm
  | cons hd tl ih =>
    intro x hm hHas
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneGoDeepInt]
    by_cases hHasU : pruneFirstInputDeepHas p lab S U = true
    · rw [ite_eq_left hHasU]
      rcases List.mem_cons.mp hm with hxh | htl
      · subst hxh
        exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih _ htl hHas))
    · rw [ite_eq_right hHasU]
      rcases List.mem_cons.mp hm with hxh | htl
      · subst hxh
        exact absurd hHas hHasU
      · exact ih _ htl hHas


/-- Membership in deep-filtered external branches resolves to an original
    branch target with reachability. -/
theorem prune_go_deep_ext_mem (p : Role) (lab : Lab) (S : DataSort)
    (fuel : Nat) :
    ∀ (branches : List (Lab × DataSort × SessionType))
    (br : Lab × DataSort × SessionType),
    br ∈ pruneGoDeepExt p lab S fuel branches →
    ∃ (l : Lab) (S' : DataSort) (U : SessionType),
      (l, S', U) ∈ branches ∧ pruneFirstInputDeepHas p lab S U = true ∧
        br = (l, S', pruneFirstInputDeepGo p lab S fuel U) := by
  intro branches
  induction branches with
  | nil =>
    intro br hmem
    simp [pruneGoDeepExt] at hmem
  | cons hd tl ih =>
    intro br hmem
    obtain ⟨l, S', U⟩ := hd
    simp only [pruneGoDeepExt] at hmem
    by_cases hHasU : pruneFirstInputDeepHas p lab S U = true
    · rw [ite_eq_left hHasU] at hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · obtain rfl := hmem
        exact ⟨l, S', U, List.mem_cons.mpr (Or.inl rfl), hHasU, rfl⟩
      · obtain ⟨l2, S2, U2, hm2, hHasU2, heq⟩ := ih _ hmem
        exact ⟨l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), hHasU2, heq⟩
    · rw [ite_eq_right hHasU] at hmem
      obtain ⟨l2, S2, U2, hm2, hHasU2, heq⟩ := ih _ hmem
      exact ⟨l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), hHasU2, heq⟩


/-- A reaching external branch maps into deep-filtered branches. -/
theorem prune_go_deep_ext_map_mem (p : Role) (lab : Lab)
    (S : DataSort) (fuel : Nat) :
    ∀ (branches : List (Lab × DataSort × SessionType))
    (x : Lab × DataSort × SessionType),
    x ∈ branches → pruneFirstInputDeepHas p lab S x.2.2 = true →
    (x.1, x.2.1, pruneFirstInputDeepGo p lab S fuel x.2.2) ∈
      pruneGoDeepExt p lab S fuel branches := by
  intro branches
  induction branches with
  | nil =>
    intro x hm _
    simp at hm
  | cons hd tl ih =>
    intro x hm hHas
    obtain ⟨l, S', U⟩ := hd
    simp only [pruneGoDeepExt]
    by_cases hHasU : pruneFirstInputDeepHas p lab S U = true
    · rw [ite_eq_left hHasU]
      rcases List.mem_cons.mp hm with hxh | htl
      · subst hxh
        exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih _ htl hHas))
    · rw [ite_eq_right hHasU]
      rcases List.mem_cons.mp hm with hxh | htl
      · subst hxh
        exact absurd hHas hHasU
      · exact ih _ htl hHas


/-- Deep-filtered internal branches keep a sublist of the `(role, label)`
    keys. -/
theorem prune_go_deep_int_keys_sublist (p : Role) (lab : Lab)
    (S : DataSort) (fuel : Nat)
    (branches : List (Role × Lab × DataSort × SessionType)) :
    List.Sublist
      (List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
        (pruneGoDeepInt p lab S fuel branches))
      (List.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
        branches) := by
  induction branches with
  | nil =>
    simp only [pruneGoDeepInt, List.map_nil]
    exact List.Sublist.refl _
  | cons hd tl ih =>
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneGoDeepInt]
    by_cases hHasU : pruneFirstInputDeepHas p lab S U = true
    · rw [ite_eq_left hHasU]
      simp only [List.map_cons]
      exact List.Sublist.cons_cons _ ih
    · rw [ite_eq_right hHasU]
      simp only [List.map_cons]
      exact List.Sublist.cons _ ih


/-- Deep-filtered external branches keep a sublist of the labels. -/
theorem prune_go_deep_ext_keys_sublist (p : Role) (lab : Lab)
    (S : DataSort) (fuel : Nat)
    (branches : List (Lab × DataSort × SessionType)) :
    List.Sublist
      (List.map (fun x : Lab × DataSort × SessionType => x.1)
        (pruneGoDeepExt p lab S fuel branches))
      (List.map (fun x : Lab × DataSort × SessionType => x.1)
        branches) := by
  induction branches with
  | nil =>
    simp only [pruneGoDeepExt, List.map_nil]
    exact List.Sublist.refl _
  | cons hd tl ih =>
    obtain ⟨l, S', U⟩ := hd
    simp only [pruneGoDeepExt]
    by_cases hHasU : pruneFirstInputDeepHas p lab S U = true
    · rw [ite_eq_left hHasU]
      simp only [List.map_cons]
      exact List.Sublist.cons_cons _ ih
    · rw [ite_eq_right hHasU]
      simp only [List.map_cons]
      exact List.Sublist.cons _ ih


/-- Deep-pruning `NoDupl` preservation at a fixed fuel, given smaller-fuel
    preservation (`ihF`): size induction; the `tRec` unfolding (when `Has`
    holds) is the only step that consumes fuel and goes through `ihF`. -/
private theorem prune_first_input_deep_go_preserves_no_dupl_at_fuel (p : Role)
    (lab : Lab) (S : DataSort) (fuel : Nat)
    (ihF : ∀ (f : Nat), f < fuel → ∀ (n : Nat) (U : SessionType),
      sizeOf U ≤ n → U.NoDupl →
      (pruneFirstInputDeepGo p lab S f U).NoDupl) :
    ∀ (n : Nat) (U : SessionType), sizeOf U ≤ n → U.NoDupl →
    (pruneFirstInputDeepGo p lab S fuel U).NoDupl := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hsize hND
    cases U with
    | tEnd =>
      simp only [pruneFirstInputDeepGo]
      exact SessionType.NoDupl.end
    | tVar X =>
      simp only [pruneFirstInputDeepGo]
      exact SessionType.NoDupl.tVar X
    | tRec X B =>
      by_cases hf : fuel = 0
      · subst hf
        simp only [pruneFirstInputDeepGo]
        exact SessionType.NoDupl.end
      · obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hf
        by_cases hHas : pruneFirstInputDeepHas p lab S
            (SessionType.tRec X B) = true
        · simp only [pruneFirstInputDeepGo, hHas, ite_true]
          have hBND : B.NoDupl := by cases hND with | tRec h => exact h
          have hNDsubst :
              (substSessionType B X (SessionType.tRec X B)).NoDupl :=
            NoDupl_subst hBND hND
          exact ihF f (by omega) _ _ (Nat.le_refl _) hNDsubst
        · simp only [pruneFirstInputDeepGo, hHas, ite_false]
          by_cases hfree : X ∈ B.fv
          · simp only [hfree, ite_true]
            exact SessionType.NoDupl.end
          · simp only [hfree, ite_false]
            have hBND : B.NoDupl := by cases hND with | tRec h => exact h
            exact ihF f (by omega) _ _ (Nat.le_refl _) hBND
    | internalChoice branches =>
      cases hND with
      | internalChoice h_nodup h_ne h_branches =>
        simp only [pruneFirstInputDeepGo]
        cases hF : pruneGoDeepInt p lab S fuel branches with
        | nil =>
          simp only [hF]
          exact SessionType.NoDupl.end
        | cons hd tl =>
          simp only [hF]
          refine SessionType.NoDupl.internalChoice ?_ ?_ ?_
          · have hsub := prune_go_deep_int_keys_sublist p lab S fuel branches
            rw [hF] at hsub
            exact hsub.nodup h_nodup
          · intro hcon
            exact absurd hcon (by simp)
          · intro x hmem
            have hmem' : x ∈ pruneGoDeepInt p lab S fuel branches := by
              rw [hF]
              exact hmem
            obtain ⟨q, l, S', U, hmemU, _, rfl⟩ :=
              prune_go_deep_int_mem p lab S fuel branches x hmem'
            have hltU : sizeOf U < n := by
              have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice
                hmemU
              omega
            exact ih _ hltU _ (Nat.le_refl _)
              (h_branches _ hmemU)
    | externalChoice q branches =>
      by_cases hbeq : (q == p) = true
      · simp only [pruneFirstInputDeepGo, hbeq, ite_true]
        cases hND with
        | externalChoice h_nodup h_ne h_branches =>
          refine match hF : branches.find? (fun b => match b with
              | (l, S', _) => l == lab && S' == S) with
            | none => ?_
            | some v => ?_
          · simp only [hF]
            exact SessionType.NoDupl.end
          · obtain ⟨l, S', U⟩ := v
            obtain ⟨hmemU, -⟩ := find?_some_mem hF
            simp only [hF]
            exact h_branches _ hmemU
      · simp only [pruneFirstInputDeepGo, hbeq]
        cases hND with
        | externalChoice h_nodup h_ne h_branches =>
          cases hF : pruneGoDeepExt p lab S fuel branches with
          | nil =>
            simp only [hF]
            exact SessionType.NoDupl.end
          | cons hd tl =>
            simp only [hF]
            refine SessionType.NoDupl.externalChoice ?_ ?_ ?_
            · have hsub := prune_go_deep_ext_keys_sublist p lab S fuel branches
              rw [hF] at hsub
              exact hsub.nodup h_nodup
            · intro hcon
              exact absurd hcon (by simp)
            · intro x hmem
              have hmem' : x ∈ pruneGoDeepExt p lab S fuel branches := by
                rw [hF]
                exact hmem
              obtain ⟨l, S', U, hmemU, _, rfl⟩ :=
                prune_go_deep_ext_mem p lab S fuel branches x hmem'
              have hltU : sizeOf U < n := by
                have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice
                  (p := q) hmemU
                omega
              exact ih _ hltU _ (Nat.le_refl _) (h_branches _ hmemU)


/-- Deep pruning preserves `NoDupl` (filtered keys form a sublist;
    resolved targets are branch targets or `tEnd`). Outer induction on
    `fuel` (unfoldings); the work is in
    `prune_first_input_deep_go_preserves_no_dupl_at_fuel`. -/
theorem prune_first_input_deep_go_preserves_no_dupl (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (fuel : Nat) (n : Nat) (U : SessionType), sizeOf U ≤ n → U.NoDupl →
    (pruneFirstInputDeepGo p lab S fuel U).NoDupl := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihF =>
    intro n U hsize hND
    exact prune_first_input_deep_go_preserves_no_dupl_at_fuel p lab S fuel ihF n U
      hsize hND


/-- Deep pruning preserves `NoRec` (resolved targets are branch targets
    or `tEnd`; filtered branches recurse structurally). -/
theorem prune_first_input_deep_go_preserves_norec (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (fuel : Nat) (n : Nat) (U : SessionType), sizeOf U ≤ n → U.NoRec →
    (pruneFirstInputDeepGo p lab S fuel U).NoRec := by
  intro fuel n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hsize hNR
    cases U with
    | tEnd =>
      simp only [pruneFirstInputDeepGo]
      exact SessionType.NoRec.end
    | tVar X =>
      simp only [pruneFirstInputDeepGo]
      exact SessionType.NoRec.tVar X
    | tRec X B => cases hNR
    | internalChoice branches =>
      cases hNR with
      | internalChoice h_branches =>
        simp only [pruneFirstInputDeepGo]
        cases hF : pruneGoDeepInt p lab S fuel branches with
        | nil =>
          simp only [hF]
          exact SessionType.NoRec.end
        | cons hd tl =>
          simp only [hF]
          apply SessionType.NoRec.internalChoice
          intro x hmem
          have hmem' : x ∈ pruneGoDeepInt p lab S fuel branches := by
            rw [hF]
            exact hmem
          obtain ⟨q, l, S', U, hmemU, _, rfl⟩ :=
            prune_go_deep_int_mem p lab S fuel branches x hmem'
          have hltU : sizeOf U < n := by
            have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice hmemU
            omega
          exact ih _ hltU _ (Nat.le_refl _) (h_branches _ hmemU)
    | externalChoice q branches =>
      by_cases hbeq : (q == p) = true
      · simp only [pruneFirstInputDeepGo, hbeq, ite_true]
        cases hNR with
        | externalChoice h_branches =>
          refine match hF : branches.find? (fun b => match b with
              | (l, S', _) => l == lab && S' == S) with
            | none => ?_
            | some v => ?_
          · simp only [hF]
            exact SessionType.NoRec.end
          · obtain ⟨l, S', U⟩ := v
            obtain ⟨hmemU, -⟩ := find?_some_mem hF
            simp only [hF]
            exact h_branches _ hmemU
      · simp only [pruneFirstInputDeepGo, hbeq]
        cases hNR with
        | externalChoice h_branches =>
          cases hF : pruneGoDeepExt p lab S fuel branches with
          | nil =>
            simp only [hF]
            exact SessionType.NoRec.end
          | cons hd tl =>
            simp only [hF]
            apply SessionType.NoRec.externalChoice
            intro x hmem
            have hmem' : x ∈ pruneGoDeepExt p lab S fuel branches := by
              rw [hF]
              exact hmem
            obtain ⟨l, S', U, hmemU, _, rfl⟩ :=
              prune_go_deep_ext_mem p lab S fuel branches x hmem'
            have hltU : sizeOf U < n := by
              have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice
                (p := q) hmemU
              omega
            exact ih _ hltU _ (Nat.le_refl _) (h_branches _ hmemU)



end PrunePreservation

section DequeueSkipHead

/-- Dequeue skipping a foreign head replays on the tail: removing `k`
    (whose sender differs from the head's) leaves the head in place and
    behaves as the tail scan. -/
theorem dequeue_skip_head {m₀ : QueueMessage} {Q' : Queue} {k : QueueMessage}
    {Qd' : Queue} (hne : m₀.1 ≠ k.1)
    (hQd : Queue.dequeue (m₀ :: Q') k = some Qd') :
    ∃ Q'' : Queue, Qd' = m₀ :: Q'' ∧ Queue.dequeue Q' k = some Q'' := by
  obtain ⟨pk, lk, Sk⟩ := k
  obtain ⟨seen, left, hQeq, hQ1eq, hseen⟩ := queue_dequeue_some_iff hQd
  cases seen with
  | nil =>
    exfalso
    have hQeq2 : m₀ :: Q' = QueueMessage.msg pk lk Sk :: left := by
      simpa using hQeq
    have hhead : m₀ = QueueMessage.msg pk lk Sk := by
      cases hQeq2
      rfl
    exact hne (congrArg (fun m => m.1) hhead)
  | cons s0 seen' =>
    have hQeq2 : m₀ :: Q' = s0 :: (seen' ++ ([QueueMessage.msg pk lk Sk] ++ left)) := by
      simpa using hQeq
    injection hQeq2 with hhead htail
    subst hhead
    refine ⟨seen' ++ left, ?_, ?_⟩
    · have hQ1 : Qd' = (m₀ :: seen') ++ left := hQ1eq
      simpa using hQ1
    · have htail2 : Q' = seen' ++ ([QueueMessage.msg pk lk Sk] ++ left) := htail
      rw [htail2]
      simp only [Queue.dequeue]
      exact dequeue_skip_seen (fun x hx => hseen _ (List.mem_cons.mpr (Or.inr hx)))



end DequeueSkipHead

