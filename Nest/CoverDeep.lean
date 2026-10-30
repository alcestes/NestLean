import Nest.SessionAdequacy

open Drainability.CannotAlwaysDrainInternalDeepSeen

/-!
# CoverDeep: cover machinery for `monitor_soundness`.

Covers (`has_cover`) from can-drain derivations, forced-step `GoU` existence,
one-message (`Tier0`) covers, the seen-evidence table (`SeenEvidence`), and
the deep-cover assembly (`deep_cover`, `can_enc_of_cover`): a monitorable,
deeply adequate, draining configuration admits a monitor fold. Feeds the
no-monitor-fold ⇒ drain-failure direction of the soundness proof.

All statements are proved here with `Drainability.Monitorable` / `Drainability.PruneStep`
explicitly qualified (the single definitions now live in `Nest.Drainability`).
-/

section CoverMonitorable

/-- Monitorability lifts through internal-choice branch targets: if every branch target is
   monitorable, so is the choice. -/
theorem Drainability.Monitorable.intC_of_branches
    {branches : List (Role × Lab × DataSort × SessionType)}
    (hall : ∀ x ∈ branches, Drainability.Monitorable x.2.2.2) :
    Drainability.Monitorable (SessionType.internalChoice branches) := by
  have hsub : {U : SessionType | Relation.ReflTransGen Drainability.PruneStep
      (SessionType.internalChoice branches) U} ⊆
      {SessionType.internalChoice branches} ∪
        ⋃ x ∈ (↑branches.toFinset : Set (Role × Lab × DataSort × SessionType)),
          {U : SessionType | Relation.ReflTransGen Drainability.PruneStep x.2.2.2 U} := by
    intro U hU
    rcases Drainability.PruneStep.head_intC_inv hU with rfl | ⟨x, hmem, hRTC⟩
    · exact Set.mem_union_left _ rfl
    · apply Set.mem_union_right
      apply Set.mem_biUnion (List.mem_toFinset.mpr hmem) hRTC
  apply Set.Finite.subset _ hsub
  refine Set.Finite.union (Set.finite_singleton _) ?_
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun x hx => ?_)
  exact hall x (List.mem_toFinset.mp hx)

/-- Monitorability lifts through external-choice branch targets: if every branch target is
   monitorable, so is the choice. -/
theorem Drainability.Monitorable.extC_of_branches {p : Role}
    {branches : List (Lab × DataSort × SessionType)}
    (hall : ∀ x ∈ branches, Drainability.Monitorable x.2.2) :
    Drainability.Monitorable (SessionType.externalChoice p branches) := by
  have hsub : {U : SessionType | Relation.ReflTransGen Drainability.PruneStep
      (SessionType.externalChoice p branches) U} ⊆
      {SessionType.externalChoice p branches} ∪
        ⋃ x ∈ (↑branches.toFinset : Set (Lab × DataSort × SessionType)),
          {U : SessionType | Relation.ReflTransGen Drainability.PruneStep x.2.2 U} := by
    intro U hU
    rcases Drainability.PruneStep.head_extC_inv hU with rfl | ⟨x, hmem, hRTC⟩
    · exact Set.mem_union_left _ rfl
    · apply Set.mem_union_right
      apply Set.mem_biUnion (List.mem_toFinset.mpr hmem) hRTC
  apply Set.Finite.subset _ hsub
  refine Set.Finite.union (Set.finite_singleton _) ?_
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun x hx => ?_)
  exact hall x (List.mem_toFinset.mp hx)

/-- `Monitorable` is preserved by `mon_tr_yes_base` steps. -/
theorem Drainability.Monitorable.of_base {T V : SessionType} {γ : ext_tag}
    (h : mon_tr_yes_base T γ V) (hFin : Drainability.Monitorable T) :
    Drainability.Monitorable V := by
  induction h with
  | intC _ hmem =>
    exact hFin.mono (Drainability.PruneStep.rtc_intC_mem hmem)
  | extC _ hmem =>
    exact hFin.mono (Drainability.PruneStep.rtc_extC_mem hmem)
  | tRec hsub ih =>
    exact ih (hFin.of_step Drainability.PruneStep.trec)

/-- `Monitorable` is preserved by `mon_tr_yes_exist` steps. -/
theorem Drainability.Monitorable.of_exist {T V : SessionType} {γ : ext_tag}
    (h : mon_tr_yes_exist T γ V) (hFin : Drainability.Monitorable T) :
    Drainability.Monitorable V := by
  induction h with
  | base hb =>
    exact Drainability.Monitorable.of_base hb hFin
  | @pfxInt branches kept q lab S T' hne hno hkept hall hNodup hkey hall_ih =>
    subst hkept
    apply Drainability.Monitorable.intC_of_branches
    intro x hx
    obtain ⟨r, l, s, T1⟩ := x
    obtain ⟨T0, hmemB⟩ := hkey r l s T1 hx
    exact hall_ih T0 T1 r l s hmemB hx (hFin.mono (Drainability.PruneStep.rtc_intC_mem hmemB))
  | @pfxExt p branches kept q lab S T' hne hneq hkept hall hNodup hkey hall_ih =>
    subst hkept
    apply Drainability.Monitorable.extC_of_branches
    intro x hx
    obtain ⟨l, s, T1⟩ := x
    obtain ⟨T0, hmemB⟩ := hkey l s T1 hx
    exact hall_ih T0 T1 l s hmemB hx (hFin.mono (Drainability.PruneStep.rtc_extC_mem hmemB))
  | unfold hsub ih =>
    exact ih (hFin.of_step Drainability.PruneStep.trec)

end CoverMonitorable
section DrainCover

-- Drain-side persistence machinery: `Has` from drain derivations, drain transfer
-- along `go_unfold_rel` steps, and the cover hypothesis.

-- Has-from-Can (proved, WF/NoDupl-only).
/-- `Has` pulls back through a self-substitution: if the unfolded body answers `Has`, so does the
   body. -/
theorem has_subst_self_imp_body' (p : Role) (lab : Lab) (S : DataSort)
    (X : String) (B : SessionType) :
    pruneFirstInputDeepHas p lab S (substSessionType B X (SessionType.tRec X B)) = true →
    pruneFirstInputDeepHas p lab S B = true := by
  intro hSub
  cases hB : pruneFirstInputDeepHas p lab S B with
  | true => rfl
  | false =>
    have hR : pruneFirstInputDeepHas p lab S (SessionType.tRec X B) = false := by
      simpa [pruneFirstInputDeepHas] using hB
    have hF := deep_has_subst_false p lab S X (SessionType.tRec X B) hR B hB
    rw [hSub] at hF
    simp at hF

/-- Draining a non-empty queue forces a `Has` hit at the head message (WF/NoDupl-only). -/
theorem has_of_canRec' (p : Role) (lab : Lab) (S : DataSort) :
    ∀ {T : SessionType} {Q : Queue} {Q' : Queue},
    T.NoDupl →
    Drainability.CanAlwaysDrainInternalDeepRec T Q →
    Q = QueueMessage.msg p lab S :: Q' →
    pruneFirstInputDeepHas p lab S T = true := by
  intro T Q Q' hND hCan hQeq
  induction hCan generalizing p lab S Q' with
  | drained_nil T =>
    simp at hQeq
  | intC_drain branches Q hfresh hall ih =>
    subst hQeq
    have hNoP : ∀ br ∈ branches, br.1 ≠ p := by
      intro br hmem
      obtain ⟨r', l', s', U'⟩ := br
      have hfr := hfresh r' l' s' U' hmem (QueueMessage.msg p lab S)
        (List.mem_cons.mpr (Or.inl rfl))
      simp at hfr
      exact Ne.symm hfr
    have hAllP : pruneAllNonP p branches = true :=
      prune_all_non_p_true_of_all_ne p branches hNoP
    have hne : branches ≠ [] := by
      cases hND with
      | internalChoice _ hne _ => exact hne
    obtain ⟨br0, hmem0⟩ := List.exists_mem_of_ne_nil _ hne
    have hND0 : br0.2.2.2.NoDupl := noDupl_of_mem_intBranches hND hmem0
    have hHas0 : pruneFirstInputDeepHas p lab S br0.2.2.2 = true :=
      ih br0 hmem0 p lab S hND0 rfl
    have hAny : pruneHasDeepIntAny p lab S branches = true := by
      obtain ⟨q0, l0, s0, U0⟩ := br0
      exact prune_has_deep_int_any_true_of_mem p lab S branches
        q0 l0 s0 U0 hHas0 hmem0
    simp only [pruneFirstInputDeepHas, hAllP, hAny, Bool.and_self]
  | extC_spec p0 branches Q habs x hmemB hsub ih =>
    subst hQeq
    have hneq : p0 ≠ p := by
      have h := habs (QueueMessage.msg p lab S) (List.mem_cons.mpr (Or.inl rfl))
      simp at h
      exact Ne.symm h
    have hbeq : ((p0 == p) = false) := beq_eq_false_iff_ne.mpr hneq
    obtain ⟨lab0, S0, T0⟩ := x
    have hND0 : T0.NoDupl := noDupl_of_mem_extBranches hND hmemB
    have hHas0 : pruneFirstInputDeepHas p lab S T0 = true :=
      ih p lab S hND0 rfl
    have hAny : pruneHasDeepExt p lab S branches = true :=
      prune_has_deep_ext_true_of_mem p lab S lab0 S0 T0 hHas0 branches hmemB
    simp [pruneFirstInputDeepHas, hbeq, hAny]
  | extC_deq p0 branches Q Q2 lab2 S2 T2 hmem hQ hsub ih =>
    subst hQeq
    obtain ⟨seen, left, hQeqQ, hQ2eq, hfree⟩ := queue_dequeue_some_iff hQ
    by_cases heq : p0 = p
    · subst heq
      have hseen : seen = [] := by
        cases seen with
        | nil => rfl
        | cons s rest =>
          have h : QueueMessage.msg p0 lab S :: Q' = s :: (rest ++ [QueueMessage.msg p0 lab2 S2] ++ left) := by
            simpa only [List.cons_append, List.nil_append, List.append_assoc] using hQeqQ
          simp only [List.cons.injEq] at h
          obtain ⟨hhead, _⟩ := h
          have hshead : s = QueueMessage.msg p0 lab S := hhead.symm
          have hmemS : s ∈ (s :: rest) := List.mem_cons.mpr (Or.inl rfl)
          have hne := hfree s hmemS
          rw [hshead] at hne
          simp at hne
      subst hseen
      simp only [List.nil_append, List.cons_append] at hQeqQ hQ2eq
      simp only [List.cons.injEq] at hQeqQ
      obtain ⟨hmsg, _⟩ := hQeqQ
      cases hmsg
      have hkey : ((lab2, S2, T2).1 == lab2 && (lab2, S2, T2).2.1 == S2) = true := by simp
      have hAnyTrue : (branches.any fun b => match b with
        | (l, S', _) => l == lab2 && S' == S2) = true := by
        rw [List.any_eq_true]
        exact ⟨(lab2, S2, T2), hmem, hkey⟩
      simp [pruneFirstInputDeepHas, hAnyTrue]
    · have hhead_ne : QueueMessage.msg p lab S ≠ QueueMessage.msg p0 lab2 S2 := by
        intro hcon
        have h1 : p = p0 := by cases hcon; rfl
        exact heq h1.symm
      have hseen_cons : ∃ seen', seen = QueueMessage.msg p lab S :: seen' := by
        cases seen with
        | nil =>
          simp only [List.nil_append, List.cons_append] at hQeqQ
          simp only [List.cons.injEq] at hQeqQ
          obtain ⟨hhead, _⟩ := hQeqQ
          exact absurd hhead hhead_ne
        | cons s rest =>
          have h : QueueMessage.msg p lab S :: Q' = s :: (rest ++ [QueueMessage.msg p0 lab2 S2] ++ left) := by
            simpa only [List.cons_append, List.nil_append, List.append_assoc] using hQeqQ
          simp only [List.cons.injEq] at h
          obtain ⟨hhead, _⟩ := h
          exact ⟨rest, hhead.symm ▸ rfl⟩
      obtain ⟨seen', hseen_eq⟩ := hseen_cons
      subst hseen_eq
      simp only [List.cons_append] at hQ2eq
      have hND2 : T2.NoDupl := noDupl_of_mem_extBranches hND hmem
      have hHas2 : pruneFirstInputDeepHas p lab S T2 = true :=
        ih p lab S hND2 hQ2eq
      have hAny : pruneHasDeepExt p lab S branches = true :=
        prune_has_deep_ext_true_of_mem p lab S lab2 S2 T2 hHas2 branches hmem
      have hbeqF : ((p0 == p) = false) := beq_eq_false_iff_ne.mpr heq
      simp [pruneFirstInputDeepHas, hbeqF, hAny]
  | trec_step X B Q hne hsub ih =>
    subst hQeq
    have hNDB : B.NoDupl := by
      cases hND with
      | tRec h => exact h
    have hNDsub : (substSessionType B X (SessionType.tRec X B)).NoDupl :=
      NoDupl_subst hNDB hND
    have hHasSub : pruneFirstInputDeepHas p lab S
        (substSessionType B X (SessionType.tRec X B)) = true :=
      ih p lab S hNDsub rfl
    have hHasB : pruneFirstInputDeepHas p lab S B = true :=
      has_subst_self_imp_body' p lab S X B hHasSub
    simpa [pruneFirstInputDeepHas] using hHasB

-- drainRelRec: GoU T U + CanRec T (msg :: Q') → CanRec U Q'.
/-- Drain transfer along a `go_unfold_rel` step: draining `T` at a queued message plus a GoU step to `U`
   yields drainability of `U` at the tail. -/
theorem drainRelRec (p : Role) (lab : Lab) (S : DataSort) :
    ∀ {n : Nat} {T U : SessionType} {Q Q' : Queue},
    T.WellFormed →
    go_unfold_rel p lab S n T U →
    Drainability.CanAlwaysDrainInternalDeepRec T Q →
    Q = QueueMessage.msg p lab S :: Q' →
    Drainability.CanAlwaysDrainInternalDeepRec U Q' := by
  intro n T U Q Q' hWF hGo hCan hQeq
  induction hGo generalizing Q Q' with
  | tEnd n =>
    subst hQeq
    cases hCan
  | tvar n X =>
    subst hQeq
    cases hCan
  | trec n X B U hsub ih =>
    subst hQeq
    cases hCan with
    | trec_step _ _ _ _ hsubCan =>
      have hWFsub : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
        SessionType.wellFormedUnfold hWF (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
      exact ih hWFsub hsubCan rfl
  | intC n branches kept hall hkey hNodupKept horder horder3 hfull hall_ih =>
    subst hQeq
    cases hCan with
    | intC_drain _ _ hfresh hallCan =>
      have hfresh' : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U' : SessionType),
          (r', l', s', U') ∈ kept → ∀ m ∈ Q', m.1 ≠ r' := by
        intro r' l' s' U' hmemK m hm
        obtain ⟨T0, hmemB, _⟩ := hkey r' l' s' U' hmemK
        have hfr := hfresh r' l' s' T0 hmemB m (List.mem_cons.mpr (Or.inr hm))
        exact hfr
      have hall' : ∀ x ∈ kept, Drainability.CanAlwaysDrainInternalDeepRec x.2.2.2 Q' := by
        intro x hx
        obtain ⟨r, l, s, T1⟩ := x
        obtain ⟨T0, hmemB, hHas0⟩ := hkey r l s T1 hx
        have hCan0 : Drainability.CanAlwaysDrainInternalDeepRec T0 (QueueMessage.msg p lab S :: Q') :=
          hallCan (r, l, s, T0) hmemB
        have hWF0 : T0.WellFormed := (Drainability.wf_of_mem_intBranches hmemB hWF)
        have hGo0 : go_unfold_rel p lab S n T0 T1 := hall T0 T1 r l s hmemB hx hHas0
        exact hall_ih T0 T1 r l s hmemB hx hHas0 hWF0 hCan0 rfl
      exact Drainability.CanAlwaysDrainInternalDeepRec.intC_drain kept Q' hfresh' hall'
  | extC_p n q branches hq hmem =>
    subst hQeq
    subst hq
    cases hCan with
    | extC_spec _ _ _ habs _ _ _ =>
      have hcon := habs (QueueMessage.msg q lab S) (List.mem_cons.mpr (Or.inl rfl))
      simp at hcon
    | extC_deq _ _ _ _ lab2 S2 T2 hmem2 hQ hsub =>
      obtain ⟨seen, left, hQeqQ, hQ2eq, hfree⟩ := queue_dequeue_some_iff hQ
      have hseen : seen = [] := by
        cases seen with
        | nil => rfl
        | cons s rest =>
          have h : QueueMessage.msg q lab S :: Q' = s :: (rest ++ [QueueMessage.msg q lab2 S2] ++ left) := by
            simpa only [List.cons_append, List.nil_append, List.append_assoc] using hQeqQ
          simp only [List.cons.injEq] at h
          obtain ⟨hhead, _⟩ := h
          have hshead : s = QueueMessage.msg q lab S := hhead.symm
          have hmemS : s ∈ (s :: rest) := List.mem_cons.mpr (Or.inl rfl)
          have hne := hfree s hmemS
          rw [hshead] at hne
          simp at hne
      subst hseen
      simp only [List.nil_append, List.cons_append] at hQeqQ hQ2eq
      simp only [List.cons.injEq] at hQeqQ
      obtain ⟨hmsg, hQeq2⟩ := hQeqQ
      cases hmsg
      have hTeq : T2 = _ := Drainability.ext_target_unique hWF.1 hmem2 hmem
      subst hTeq
      have heq : _ = Q' := hQ2eq.trans hQeq2.symm
      rw [heq] at hsub
      exact hsub
  | extC_p_miss n q branches hq hmiss =>
    subst hQeq
    subst hq
    cases hCan with
    | extC_spec _ _ _ habs _ _ _ =>
      have hcon := habs (QueueMessage.msg q lab S) (List.mem_cons.mpr (Or.inl rfl))
      simp at hcon
    | extC_deq _ _ _ _ lab2 S2 T2 hmem2 hQ hsub =>
      obtain ⟨seen, left, hQeqQ, hQ2eq, hfree⟩ := queue_dequeue_some_iff hQ
      have hseen : seen = [] := by
        cases seen with
        | nil => rfl
        | cons s rest =>
          have h : QueueMessage.msg q lab S :: Q' = s :: (rest ++ [QueueMessage.msg q lab2 S2] ++ left) := by
            simpa only [List.cons_append, List.nil_append, List.append_assoc] using hQeqQ
          simp only [List.cons.injEq] at h
          obtain ⟨hhead, _⟩ := h
          have hshead : s = QueueMessage.msg q lab S := hhead.symm
          have hmemS : s ∈ (s :: rest) := List.mem_cons.mpr (Or.inl rfl)
          have hne := hfree s hmemS
          rw [hshead] at hne
          simp at hne
      subst hseen
      simp only [List.nil_append, List.cons_append] at hQeqQ
      simp only [List.cons.injEq] at hQeqQ
      obtain ⟨hmsg, _⟩ := hQeqQ
      simp only [QueueMessage.msg.injEq] at hmsg
      obtain ⟨_, hlab, hS⟩ := hmsg
      have hcon := hmiss (lab2, S2, T2) hmem2
      have htrue : ((lab2, S2, T2).1 == lab2 && (lab2, S2, T2).2.1 == S2) = true := by simp
      rw [hlab, hS] at hcon
      rw [htrue] at hcon
      cases hcon
  | extC_q n q branches kept hq hall hkey hNodupKept horder horder3 hfull hall_ih =>
    subst hQeq
    cases hCan with
    | extC_spec _ _ _ habs x hmemB hsub =>
      obtain ⟨lab0, S0, T0⟩ := x
      have habs' : ∀ m ∈ Q', m.1 ≠ q := fun m hm =>
        habs m (List.mem_cons.mpr (Or.inr hm))
      have hND0 : T0.NoDupl := noDupl_of_mem_extBranches hWF.1 hmemB
      have hHas0 : pruneFirstInputDeepHas p lab S T0 = true :=
        has_of_canRec' p lab S hND0 hsub rfl
      obtain ⟨T1, hmemK⟩ := hfull lab0 S0 T0 hmemB hHas0
      have hWF0 : T0.WellFormed := Drainability.wf_of_mem_extBranches hmemB hWF
      have hCan1 : Drainability.CanAlwaysDrainInternalDeepRec T1 Q' :=
        hall_ih T0 T1 lab0 S0 hmemB hmemK hHas0 hWF0 hsub rfl
      exact Drainability.CanAlwaysDrainInternalDeepRec.extC_spec q kept Q' habs' (lab0, S0, T1) hmemK hCan1
    | extC_deq _ _ _ _ lab2 S2 T2 hmem2 hQ hsub =>
      obtain ⟨seen, left, hQeqQ, hQ2eq, hfree⟩ := queue_dequeue_some_iff hQ
      have hhead_ne : QueueMessage.msg p lab S ≠ QueueMessage.msg q lab2 S2 := by
        intro hcon
        have h1 : p = q := by cases hcon; rfl
        exact hq h1.symm
      have hseen_cons : ∃ seen', seen = QueueMessage.msg p lab S :: seen' := by
        cases seen with
        | nil =>
          simp only [List.nil_append, List.cons_append] at hQeqQ
          simp only [List.cons.injEq] at hQeqQ
          obtain ⟨hhead, _⟩ := hQeqQ
          exact absurd hhead hhead_ne
        | cons s rest =>
          have h : QueueMessage.msg p lab S :: Q' = s :: (rest ++ [QueueMessage.msg q lab2 S2] ++ left) := by
            simpa only [List.cons_append, List.nil_append, List.append_assoc] using hQeqQ
          simp only [List.cons.injEq] at h
          obtain ⟨hhead, _⟩ := h
          exact ⟨rest, hhead.symm ▸ rfl⟩
      obtain ⟨seen', hseen_eq⟩ := hseen_cons
      subst hseen_eq
      simp only [List.cons_append] at hQeqQ hQ2eq
      simp only [List.cons.injEq] at hQeqQ
      obtain ⟨_, hQeqQ'⟩ := hQeqQ
      -- hQeqQ' : Q' = seen' ++ [msg q lab2 S2] ++ left
      -- hQ2eq : Q2 = msg p lab S :: (seen' ++ left), hsub : Can T2 Q2
      have hND2 : T2.NoDupl := noDupl_of_mem_extBranches hWF.1 hmem2
      have hHas2 : pruneFirstInputDeepHas p lab S T2 = true :=
        has_of_canRec' p lab S hND2 hsub hQ2eq
      obtain ⟨T1, hmemK⟩ := hfull lab2 S2 T2 hmem2 hHas2
      have hWF2 : T2.WellFormed := Drainability.wf_of_mem_extBranches hmem2 hWF
      have hCanT1 : Drainability.CanAlwaysDrainInternalDeepRec T1 (seen' ++ left) :=
        hall_ih T2 T1 lab2 S2 hmem2 hmemK hHas2 hWF2 hsub hQ2eq
      have hfree' : ∀ m ∈ seen', m.1 ≠ q := by
        intro m hm
        have hmS : m ∈ QueueMessage.msg p lab S :: seen' := List.mem_cons.mpr (Or.inr hm)
        have h := hfree m hmS
        simpa using h
      have hQdeq : Q'.dequeue (QueueMessage.msg q lab2 S2) = some (seen' ++ left) := by
        rw [hQeqQ']
        have hgo := Drainability.dequeue_skip_seen (p := q) (lab := lab2) (S := S2)
          (rest := left) (acc := []) (seen := seen') hfree'
        simpa [Queue.dequeue] using hgo
      exact Drainability.CanAlwaysDrainInternalDeepRec.extC_deq q kept Q' (seen' ++ left)
        lab2 S2 T1 hmemK hQdeq hCanT1

-- Cover hypothesis for (T, Q): every enc-reachable split head has a GoU.
/-- Cover hypothesis for `(T, Q)`: every enc-reachable split head (at any queue split of `Q`) admits
   a `go_unfold_rel` step target. -/
def has_cover (T : SessionType) (Q : Queue) : Prop :=
  ∀ (pre Q0 : Queue) (V : SessionType)
    (p0 : Role) (lab0 : Lab) (S0 : DataSort) (Q0' : Queue),
    Q = pre ++ Q0 →
    monitor_fold_aux pre T V →
    Q0 = QueueMessage.msg p0 lab0 S0 :: Q0' →
    ∃ n U, go_unfold_rel p0 lab0 S0 n V U

end DrainCover

section ForcedGoU

/-- Every forced step is a `Drainability` prune step (forced steps are a sub-relation of prune steps). -/
theorem forced_is_prune {p : Role} {lab : Lab} {S : DataSort}
    {T U : SessionType} (h : forced_step p lab S T U) : Drainability.PruneStep T U := by
  cases h with
  | trec => exact Drainability.PruneStep.trec
  | extCQ _ hmem _ => exact Drainability.PruneStep.extC hmem
  | intC hmem _ => exact Drainability.PruneStep.intC hmem

/-- Forced-step reachability implies prune-step reachability (lifting `forced_is_prune` over
   reflexive-transitive closure). -/
theorem forced_rtc_imp_prune_rtc {p : Role} {lab : Lab} {S : DataSort}
    {T U : SessionType}
    (h : Relation.ReflTransGen (forced_step p lab S) T U) :
    Relation.ReflTransGen Drainability.PruneStep T U := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h1 h2 ih => exact ih.trans (Relation.ReflTransGen.single (forced_is_prune h2))

/-- GoU-existence from one-message prunability: a monitorable type with a `PrunableOneMsg` witness
   reaches a `go_unfold_rel` target along forced steps (same measure-descent argument as the classical
   GoU-existence proof, with the prune-successor measure replaced by the forced-successor measure). -/
theorem forced_GoU_exist (p : Role) (lab : Lab) (S : DataSort)
    {T₀ : SessionType} (hFin : Drainability.Monitorable T₀) (hOneMsg : PrunableOneMsg p lab S T₀) :
    ∀ (T : SessionType), Relation.ReflTransGen (forced_step p lab S) T₀ T → T.NoDupl →
    ∃ n V, go_unfold_rel p lab S n T V := by
  classical
  obtain ⟨s, hs⟩ := hFin.exists_finset_coe
  have hmemS : ∀ {U : SessionType}, Relation.ReflTransGen Drainability.PruneStep T₀ U → U ∈ s := by
    intro U h
    rw [← Finset.mem_coe, hs]
    exact h
  have hfinSucc : ∀ (T : SessionType), Relation.ReflTransGen (forced_step p lab S) T₀ T →
      {U : SessionType | Relation.ReflTransGen (forced_step p lab S) T U}.Finite :=
    fun T hT => (Finset.finite_toSet s).subset (fun U hU =>
      hmemS ((forced_rtc_imp_prune_rtc hT).trans (forced_rtc_imp_prune_rtc hU)))
  suffices h : ∀ (k : Nat) (T : SessionType),
      Relation.ReflTransGen (forced_step p lab S) T₀ T →
      Set.ncard {U : SessionType | Relation.ReflTransGen (forced_step p lab S) T U} ≤ k →
      T.NoDupl → ∃ n V, go_unfold_rel p lab S n T V by
    intro T hRTC hND
    exact h _ T hRTC (Nat.le_refl _) hND
  intro k T hRTC hle hND
  revert T hRTC hle hND
  induction k using Nat.strong_induction_on with
  | _ k ihK =>
    intro T hRTC hle hND
    have hstrict : ∀ {A B : SessionType},
        Relation.ReflTransGen (forced_step p lab S) T₀ A → forced_step p lab S A B →
        Set.ncard {U : SessionType | Relation.ReflTransGen (forced_step p lab S) B U} <
          Set.ncard {U : SessionType | Relation.ReflTransGen (forced_step p lab S) A U} := by
      intro A B hRA hStep
      have hsub : {U : SessionType | Relation.ReflTransGen (forced_step p lab S) B U} ⊆
          {U : SessionType | Relation.ReflTransGen (forced_step p lab S) A U} := by
        intro U hU
        exact (Relation.ReflTransGen.single hStep).trans hU
      have hne : {U : SessionType | Relation.ReflTransGen (forced_step p lab S) B U} ≠
          {U : SessionType | Relation.ReflTransGen (forced_step p lab S) A U} := by
        intro heq
        have hmemA : A ∈ ({U : SessionType | Relation.ReflTransGen (forced_step p lab S) B U} :
            Set SessionType) := by
          rw [heq]
          exact Relation.ReflTransGen.refl
        exact hOneMsg A B hRA hStep hmemA
      exact Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
        (hfinSucc A hRA)
    cases T with
    | tEnd => exact ⟨0, _, go_unfold_rel.tEnd 0⟩
    | tVar X => exact ⟨0, _, go_unfold_rel.tvar 0 X⟩
    | tRec X B =>
      have hRTCsub : Relation.ReflTransGen (forced_step p lab S) T₀
          (substSessionType B X (SessionType.tRec X B)) :=
        hRTC.trans (Relation.ReflTransGen.single forced_step.trec)
      have hlt : Set.ncard {U : SessionType |
          Relation.ReflTransGen (forced_step p lab S) (substSessionType B X (SessionType.tRec X B)) U} < k := by
        have h1 := hstrict hRTC forced_step.trec
        omega
      have hBND : B.NoDupl := by
        cases hND with
        | tRec h => exact h
      have hNDsub : (substSessionType B X (SessionType.tRec X B)).NoDupl :=
        NoDupl_subst hBND hND
      obtain ⟨m, U, hD⟩ := ihK _ hlt _ hRTCsub (Nat.le_refl _) hNDsub
      exact ⟨m + 1, U, go_unfold_rel.trec m X B U hD⟩
    | internalChoice branches =>
      have hNDkeys : (branches.map (fun x : Role × Lab × DataSort × SessionType =>
          (x.1, x.2.1))).Nodup := by
        cases hND with
        | internalChoice hnod _ _ => exact hnod
      have hNDb : ∀ x ∈ branches, x.2.2.2.NoDupl := by
        intro x hx
        cases hND with
        | internalChoice _ _ hbr => exact hbr _ hx
      have hkept : ∀ (bs : List (Role × Lab × DataSort × SessionType)),
          (∀ x ∈ bs, x ∈ branches) →
          (bs.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))).Nodup →
          ∃ (kept : List (Role × Lab × DataSort × SessionType)) (nB : Nat),
            (∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
              (r, l, s, T0) ∈ bs → (r, l, s, T1) ∈ kept →
              pruneFirstInputDeepHas p lab S T0 = true → go_unfold_rel p lab S nB T0 T1) ∧
            (∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
              (r, l, s, T1) ∈ kept → ∃ T0, (r, l, s, T0) ∈ bs ∧
                pruneFirstInputDeepHas p lab S T0 = true) ∧
            (∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
              (r, l, s, T0) ∈ bs → pruneFirstInputDeepHas p lab S T0 = true →
              ∃ T1, (r, l, s, T1) ∈ kept) ∧
            List.Sublist (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)))
              (bs.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) ∧
            List.Sublist (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
              (bs.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) := by
        intro bs
        induction bs with
        | nil =>
          intro _ _
          refine ⟨[], 0, ?_, ?_, ?_, ?_, ?_⟩
          · intro T0 T1 r l s hB hK hHasT0
            simp at hK
          · intro r l s T1 hK
            simp at hK
          · intro r l s T0 hB hHasT0
            simp at hB
          · simp only [List.map_nil]
            exact List.Sublist.refl _
          · simp only [List.map_nil]
            exact List.Sublist.refl _
        | cons hd tl ih =>
          intro hsubmem hNDbs
          obtain ⟨q0, l0, S0, U0⟩ := hd
          have hNDtl : (tl.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))).Nodup := by
            have h1 := hNDbs
            simp only [List.map_cons, List.nodup_cons] at h1
            exact h1.2
          have hFresh : (q0, l0) ∉ tl.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) := by
            have h1 := hNDbs
            simp only [List.map_cons, List.nodup_cons] at h1
            exact h1.1
          obtain ⟨kept_tl, n_tl, hhall_tl, hhkey_tl, hfull_tl, horder_tl, horder3_tl⟩ :=
            ih (fun x hx => hsubmem x (List.mem_cons.mpr (Or.inr hx))) hNDtl
          by_cases hH : pruneFirstInputDeepHas p lab S U0 = true
          · have hmem_hd : (q0, l0, S0, U0) ∈ branches :=
              hsubmem _ (List.mem_cons.mpr (Or.inl rfl))
            have hRTC0 : Relation.ReflTransGen (forced_step p lab S) T₀ U0 :=
              hRTC.trans (Relation.ReflTransGen.single (forced_step.intC hmem_hd hH))
            have hlt0 : Set.ncard {U : SessionType |
                Relation.ReflTransGen (forced_step p lab S) U0 U} < k := by
              have h1 : Set.ncard {U : SessionType |
                  Relation.ReflTransGen (forced_step p lab S) U0 U} <
                  Set.ncard {U : SessionType |
                    Relation.ReflTransGen (forced_step p lab S) (SessionType.internalChoice branches) U} :=
                hstrict hRTC (forced_step.intC hmem_hd hH)
              exact lt_of_lt_of_le h1 hle
            have hNDU0 : U0.NoDupl := hNDb _ hmem_hd
            obtain ⟨m_hd, Uhd, hDhd⟩ := ihK _ hlt0 _ hRTC0 (Nat.le_refl _) hNDU0
            refine ⟨(q0, l0, S0, Uhd) :: kept_tl, Nat.max m_hd n_tl, ?_, ?_, ?_, ?_, ?_⟩
            · intro T0 T1 r l s hB hK hHasT0
              simp only [List.mem_cons] at hK
              rcases hK with hK | hK
              · obtain ⟨rfl, rfl, rfl, rfl⟩ := hK
                simp only [List.mem_cons] at hB
                rcases hB with hB | hB
                · obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
                  exact go_unfold_rel.mono_le p lab S hDhd (Nat.le_max_left _ _)
                · exfalso
                  apply hFresh
                  exact List.mem_map.mpr ⟨(q0, l0, S0, T0), hB, rfl⟩
              · simp only [List.mem_cons] at hB
                rcases hB with hB | hB
                · obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
                  exfalso
                  apply hFresh
                  have hmemT : (q0, l0) ∈ kept_tl.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) :=
                    List.mem_map.mpr ⟨(q0, l0, S0, T1), hK, rfl⟩
                  exact List.Sublist.subset horder_tl hmemT
                · exact go_unfold_rel.mono_le p lab S
                    (hhall_tl _ _ _ _ _ hB hK hHasT0) (Nat.le_max_right _ _)
            · intro r l s T1 hK
              simp only [List.mem_cons] at hK
              rcases hK with hK | hK
              · obtain ⟨rfl, rfl, rfl, rfl⟩ := hK
                exact ⟨U0, List.mem_cons.mpr (Or.inl rfl), hH⟩
              · obtain ⟨T0, hmemT0, hHasT0⟩ := hhkey_tl _ _ _ _ hK
                exact ⟨T0, List.mem_cons.mpr (Or.inr hmemT0), hHasT0⟩
            · intro r l s T0 hB hHasT0
              simp only [List.mem_cons] at hB
              rcases hB with hB | hB
              · obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
                exact ⟨Uhd, List.mem_cons.mpr (Or.inl rfl)⟩
              · obtain ⟨T1, hmemK⟩ := hfull_tl r l s T0 hB hHasT0
                exact ⟨T1, List.mem_cons.mpr (Or.inr hmemK)⟩
            · simp only [List.map_cons]
              exact List.Sublist.cons_cons _ horder_tl
            · simp only [List.map_cons]
              exact List.Sublist.cons_cons _ horder3_tl
          · refine ⟨kept_tl, n_tl, ?_, ?_, ?_, ?_, ?_⟩
            · intro T0 T1 r l s hB hK hHasT0
              simp only [List.mem_cons] at hB
              rcases hB with hB | hB
              · obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
                exact absurd hHasT0 hH
              · exact hhall_tl _ _ _ _ _ hB hK hHasT0
            · intro r l s T1 hK
              obtain ⟨T0, hmemT0, hHasT0⟩ := hhkey_tl _ _ _ _ hK
              exact ⟨T0, List.mem_cons.mpr (Or.inr hmemT0), hHasT0⟩
            · intro r l s T0 hB hHasT0
              simp only [List.mem_cons] at hB
              rcases hB with hB | hB
              · obtain ⟨rfl, rfl, rfl, rfl⟩ := hB
                exact absurd hHasT0 hH
              · obtain ⟨T1, hmemK⟩ := hfull_tl r l s T0 hB hHasT0
                exact ⟨T1, hmemK⟩
            · simp only [List.map_cons]
              exact List.Sublist.cons _ horder_tl
            · simp only [List.map_cons]
              exact List.Sublist.cons _ horder3_tl
      obtain ⟨kept, nB, hhall, hhkey, hfull, horder, horder3⟩ := hkept branches (fun x hx => hx) hNDkeys
      have hnkept := List.Sublist.nodup horder hNDkeys
      exact ⟨nB + 1, SessionType.internalChoice kept,
        go_unfold_rel.intC nB branches kept hhall hhkey hnkept horder horder3 hfull⟩
    | externalChoice q branches =>
      have hNDkeys : (branches.map (fun x : Lab × DataSort × SessionType => x.1)).Nodup := by
        cases hND with
        | externalChoice hnod _ _ => exact hnod
      have hNDb : ∀ x ∈ branches, x.2.2.NoDupl := by
        intro x hx
        cases hND with
        | externalChoice _ _ hbr => exact hbr _ hx
      by_cases hbeq : (q == p) = true
      · have hqp : q = p := beq_iff_eq.mp hbeq
        by_cases hEx : ∃ x ∈ branches, ((x.1 == lab && x.2.1 == S) = true)
        · obtain ⟨x, hx, hkeyT⟩ := hEx
          obtain ⟨l, s, U⟩ := x
          have hkeys : l = lab ∧ s = S := by
            have h1 : ((l == lab) && (s == S)) = true := hkeyT
            simp at h1
            exact h1
          obtain ⟨rfl, rfl⟩ := hkeys
          exact ⟨0, U, go_unfold_rel.extC_p 0 q branches hqp hx⟩
        · have hmiss : ∀ x ∈ branches, ((x.1 == lab && x.2.1 == S) = false) := by
            intro x hx
            exact Bool.eq_false_of_ne_true (fun hT => hEx ⟨x, hx, hT⟩)
          exact ⟨0, SessionType.tEnd, go_unfold_rel.extC_p_miss 0 q branches hqp hmiss⟩
      · have hqp : q ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
        have hkept : ∀ (bs : List (Lab × DataSort × SessionType)),
            (∀ x ∈ bs, x ∈ branches) →
            (bs.map (fun x : Lab × DataSort × SessionType => x.1)).Nodup →
            ∃ (kept : List (Lab × DataSort × SessionType)) (nB : Nat),
              (∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
                (l, s, T0) ∈ bs → (l, s, T1) ∈ kept →
                pruneFirstInputDeepHas p lab S T0 = true → go_unfold_rel p lab S nB T0 T1) ∧
              (∀ (l : Lab) (s : DataSort) (T1 : SessionType),
                (l, s, T1) ∈ kept → ∃ T0, (l, s, T0) ∈ bs ∧
                  pruneFirstInputDeepHas p lab S T0 = true) ∧
              (∀ (l : Lab) (s : DataSort) (T0 : SessionType),
                (l, s, T0) ∈ bs → pruneFirstInputDeepHas p lab S T0 = true →
                ∃ T1, (l, s, T1) ∈ kept) ∧
              List.Sublist (kept.map (fun x : Lab × DataSort × SessionType => x.1))
                (bs.map (fun x : Lab × DataSort × SessionType => x.1)) ∧
              List.Sublist (kept.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
                (bs.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) := by
          intro bs
          induction bs with
          | nil =>
            intro _ _
            refine ⟨[], 0, ?_, ?_, ?_, ?_, ?_⟩
            · intro T0 T1 l s hB hK hHasT0
              simp at hK
            · intro l s T1 hK
              simp at hK
            · intro l s T0 hB hHasT0
              simp at hB
            · simp only [List.map_nil]
              exact List.Sublist.refl _
            · simp only [List.map_nil]
              exact List.Sublist.refl _
          | cons hd tl ih =>
            intro hsubmem hNDbs
            obtain ⟨l0, S0, U0⟩ := hd
            have hNDtl : (tl.map (fun x : Lab × DataSort × SessionType => x.1)).Nodup := by
              have h1 := hNDbs
              simp only [List.map_cons, List.nodup_cons] at h1
              exact h1.2
            have hFresh : l0 ∉ tl.map (fun x : Lab × DataSort × SessionType => x.1) := by
              have h1 := hNDbs
              simp only [List.map_cons, List.nodup_cons] at h1
              exact h1.1
            obtain ⟨kept_tl, n_tl, hhall_tl, hhkey_tl, hfull_tl, horder_tl, horder3_tl⟩ :=
              ih (fun x hx => hsubmem x (List.mem_cons.mpr (Or.inr hx))) hNDtl
            by_cases hH : pruneFirstInputDeepHas p lab S U0 = true
            · have hmem_hd : (l0, S0, U0) ∈ branches :=
                hsubmem _ (List.mem_cons.mpr (Or.inl rfl))
              have hRTC0 : Relation.ReflTransGen (forced_step p lab S) T₀ U0 :=
                hRTC.trans (Relation.ReflTransGen.single (forced_step.extCQ hqp hmem_hd hH))
              have hlt0 : Set.ncard {U : SessionType |
                  Relation.ReflTransGen (forced_step p lab S) U0 U} < k := by
                have h1 : Set.ncard {U : SessionType |
                    Relation.ReflTransGen (forced_step p lab S) U0 U} <
                    Set.ncard {U : SessionType |
                      Relation.ReflTransGen (forced_step p lab S) (SessionType.externalChoice q branches) U} :=
                  hstrict hRTC (forced_step.extCQ hqp hmem_hd hH)
                exact lt_of_lt_of_le h1 hle
              have hNDU0 : U0.NoDupl := hNDb _ hmem_hd
              obtain ⟨m_hd, Uhd, hDhd⟩ := ihK _ hlt0 _ hRTC0 (Nat.le_refl _) hNDU0
              refine ⟨(l0, S0, Uhd) :: kept_tl, Nat.max m_hd n_tl, ?_, ?_, ?_, ?_, ?_⟩
              · intro T0 T1 l s hB hK hHasT0
                simp only [List.mem_cons] at hK
                rcases hK with hK | hK
                · obtain ⟨rfl, rfl, rfl⟩ := hK
                  simp only [List.mem_cons] at hB
                  rcases hB with hB | hB
                  · obtain ⟨rfl, rfl, rfl⟩ := hB
                    exact go_unfold_rel.mono_le p lab S hDhd (Nat.le_max_left _ _)
                  · exfalso
                    apply hFresh
                    exact List.mem_map.mpr ⟨(l0, S0, T0), hB, rfl⟩
                · simp only [List.mem_cons] at hB
                  rcases hB with hB | hB
                  · obtain ⟨rfl, rfl, rfl⟩ := hB
                    exfalso
                    apply hFresh
                    have hmemT : l0 ∈ kept_tl.map (fun x : Lab × DataSort × SessionType => x.1) :=
                      List.mem_map.mpr ⟨(l0, S0, T1), hK, rfl⟩
                    exact List.Sublist.subset horder_tl hmemT
                  · exact go_unfold_rel.mono_le p lab S
                      (hhall_tl _ _ _ _ hB hK hHasT0) (Nat.le_max_right _ _)
              · intro l s T1 hK
                simp only [List.mem_cons] at hK
                rcases hK with hK | hK
                · obtain ⟨rfl, rfl, rfl⟩ := hK
                  exact ⟨U0, List.mem_cons.mpr (Or.inl rfl), hH⟩
                · obtain ⟨T0, hmemT0, hHasT0⟩ := hhkey_tl _ _ _ hK
                  exact ⟨T0, List.mem_cons.mpr (Or.inr hmemT0), hHasT0⟩
              · intro l s T0 hB hHasT0
                simp only [List.mem_cons] at hB
                rcases hB with hB | hB
                · obtain ⟨rfl, rfl, rfl⟩ := hB
                  exact ⟨Uhd, List.mem_cons.mpr (Or.inl rfl)⟩
                · obtain ⟨T1, hmemK⟩ := hfull_tl l s T0 hB hHasT0
                  exact ⟨T1, List.mem_cons.mpr (Or.inr hmemK)⟩
              · simp only [List.map_cons]
                exact List.Sublist.cons_cons _ horder_tl
              · simp only [List.map_cons]
                exact List.Sublist.cons_cons _ horder3_tl
            · refine ⟨kept_tl, n_tl, ?_, ?_, ?_, ?_, ?_⟩
              · intro T0 T1 l s hB hK hHasT0
                simp only [List.mem_cons] at hB
                rcases hB with hB | hB
                · obtain ⟨rfl, rfl, rfl⟩ := hB
                  exact absurd hHasT0 hH
                · exact hhall_tl _ _ _ _ hB hK hHasT0
              · intro l s T1 hK
                obtain ⟨T0, hmemT0, hHasT0⟩ := hhkey_tl _ _ _ hK
                exact ⟨T0, List.mem_cons.mpr (Or.inr hmemT0), hHasT0⟩
              · intro l s T0 hB hHasT0
                simp only [List.mem_cons] at hB
                rcases hB with hB | hB
                · obtain ⟨rfl, rfl, rfl⟩ := hB
                  exact absurd hHasT0 hH
                · obtain ⟨T1, hmemK⟩ := hfull_tl l s T0 hB hHasT0
                  exact ⟨T1, hmemK⟩
              · simp only [List.map_cons]
                exact List.Sublist.cons _ horder_tl
              · simp only [List.map_cons]
                exact List.Sublist.cons _ horder3_tl
        obtain ⟨kept, nB, hhall, hhkey, hfull, horder, horder3⟩ := hkept branches (fun x hx => hx) hNDkeys
        have hnkept := List.Sublist.nodup horder hNDkeys
        exact ⟨nB + 1, SessionType.externalChoice q kept,
          go_unfold_rel.extC_q nB q branches kept hqp hhall hhkey hnkept horder horder3 hfull⟩

end ForcedGoU



section Tier0Cover

/-- Cover implies a monitor fold: from `Can` plus per-split `GoU` coverage at
    every queue split, build an accepting monitor run. WF-only, by queue
    induction: the cons step reuses cover (GoU at `pre=[]`) + `Has`
    (`has_of_canRec'`) + `toMaximal` for the `Yes` step, `drainRelRec` for
    `Can` on the tail, and a pre-extension fragment (`Yes`-single + append)
    for cover of the tail. -/
theorem can_enc_of_cover : ∀ (Q : Queue) (T : SessionType),
    T.WellFormed →
    Drainability.CanAlwaysDrainInternalDeepRec T Q →
    has_cover T Q →
    ∃ M, monitor_fold (T, Q) M := by
  intro Q
  induction Q with
  | nil =>
    intro T hWF hCan hCov
    exact ⟨T, by simp [monitor_fold, monitor_fold_aux]⟩
  | cons hd tl ih =>
    intro T hWF hCan hCov
    obtain ⟨p0, lab0, S0⟩ := hd
    obtain ⟨nGo, Ugo, dGo⟩ := hCov [] (QueueMessage.msg p0 lab0 S0 :: tl) T
      p0 lab0 S0 tl rfl rfl rfl
    have hHasHd : pruneFirstInputDeepHas p0 lab0 S0 T = true :=
      has_of_canRec' p0 lab0 S0 hWF.1 hCan rfl
    obtain ⟨EGo, hMGo⟩ := go_unfold_rel.toMaximal p0 lab0 S0 dGo hHasHd hWF
    have hWFmid : Ugo.WellFormed := mon_tr_yes_preserves_wf ⟨EGo, hMGo⟩ hWF
    have hCanMid : Drainability.CanAlwaysDrainInternalDeepRec Ugo tl :=
      drainRelRec p0 lab0 S0 hWF dGo hCan rfl
    have hHdSingle : monitor_fold_aux [QueueMessage.msg p0 lab0 S0] T Ugo :=
      ⟨Ugo, ⟨EGo, hMGo⟩, rfl⟩
    have hCovMid : has_cover Ugo tl := by
      intro pre Q0 V p1 lab1 S1 Q0' hSuffix hEncPre hQ0eq
      have hSuffixFull : (QueueMessage.msg p0 lab0 S0 :: tl) =
          ([QueueMessage.msg p0 lab0 S0] ++ pre) ++ Q0 := by
        have h2 : ([QueueMessage.msg p0 lab0 S0] ++ pre) ++ Q0 =
            QueueMessage.msg p0 lab0 S0 :: (pre ++ Q0) := by
          simp only [List.cons_append, List.nil_append]
        rw [h2, hSuffix]
      have hEncFull : monitor_fold_aux ([QueueMessage.msg p0 lab0 S0] ++ pre) T V :=
        monitor_fold_aux_append_iff.mpr ⟨Ugo, hHdSingle, hEncPre⟩
      exact hCov ([QueueMessage.msg p0 lab0 S0] ++ pre) Q0 V p1 lab1 S1 Q0'
        hSuffixFull hEncFull hQ0eq
    obtain ⟨M', hFoldMid⟩ := ih Ugo hWFmid hCanMid hCovMid
    simp only [monitor_fold, monitor_fold_aux]
    exact ⟨M', Ugo, ⟨EGo, hMGo⟩, hFoldMid⟩

end Tier0Cover

section EvidenceTable

/-- Evidence table: every visited `tRec` carries its unfold adequacy at the
    current `seen`. `trec_seen` cuts discard body evidence locally; the table
    threads it globally so `enc` unfold steps stay closable. Grows by consing
    (`seen_ev_extend`); adequacy lifts by `deep_mono_grow`. -/
def SeenEvidence (seen : List SessionType) : Prop :=
  ∀ S ∈ seen, ∃ X B, S = SessionType.tRec X B ∧
    Prunable (S :: seen) (substSessionType B X S)

/-- The empty seen-list is trivially evidence (`SeenEvidence []`). -/
theorem seen_ev_empty : SeenEvidence [] := by
  intro S hmem
  exact False.elim (List.not_mem_nil hmem)

/-- Seen-evidence extends across an unfolded `tRec`: a prunable head joins a valid seen-list. -/
theorem seen_ev_extend : ∀ {seen : List SessionType} {X : String} {B : SessionType},
    SeenEvidence seen → Prunable seen (SessionType.tRec X B) →
    SeenEvidence (SessionType.tRec X B :: seen) := by
  intro seen X B hev hPrunable S hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with rfl | hmemOld
  · have hPrunableSub : Prunable (SessionType.tRec X B :: seen)
        (substSessionType B X (SessionType.tRec X B)) := by
      cases hPrunable with
      | trec_new s X B hnmem hPrunableSub hOneMsgAll => exact hPrunableSub
      | trec_seen s X B hmem hOneMsgAll =>
        obtain ⟨X0, B0, hEq, hEv⟩ := hev _ hmem
        simp only [SessionType.tRec.injEq] at hEq
        obtain ⟨rfl, rfl⟩ := hEq
        exact hEv
    exact ⟨X, B, rfl, deep_mono_grow (List.Sublist.cons _ (List.Sublist.refl _)) hPrunableSub⟩
  · obtain ⟨X0, B0, rfl, hEv⟩ := hev S hmemOld
    exact ⟨X0, B0, rfl,
      deep_mono_grow (List.Sublist.cons_cons _ ((List.Sublist.refl _).cons _)) hEv⟩

-- Base-fragment preservation: `mon_tr_yes_base` steps preserve `Deep` (at a grown
-- `seen`) with evidence threading. The `tRec` case closes both via `trec_new`
-- evidence and via the table at `trec_seen` cuts. Prefix (`pfxInt`/`pfxExt`)
-- steps are out of scope: fresh kept-choices need an `hOneMsgAll` no-return argument.
/-- Deep prunability is preserved by `mon_tr_yes_base` steps, extending the seen-list with evidence. -/
theorem deep_preserved_base : ∀ {T : SessionType} {γ : ext_tag} {T' : SessionType},
    mon_tr_yes_base T γ T' → ∀ (seen : List SessionType),
    SeenEvidence seen → Prunable seen T →
    ∃ seen', seen.Sublist seen' ∧ SeenEvidence seen' ∧ Prunable seen' T' := by
  intro T γ T' hb seen hev hPrunable
  induction hb generalizing seen with
  | intC huniq hmem =>
    cases hPrunable with
    | intC s branches hPrunableBranch hOneMsgAll =>
      exact ⟨seen, List.Sublist.refl _, hev, hPrunableBranch _ hmem⟩
  | extC huniq hmem =>
    cases hPrunable with
    | extC s p branches hPrunableBranch hOneMsgAll =>
      exact ⟨seen, List.Sublist.refl _, hev, hPrunableBranch _ hmem⟩
  | tRec hsub ih =>
    rename_i X B _ _
    have hev1 : SeenEvidence (SessionType.tRec X B :: seen) :=
      seen_ev_extend hev hPrunable
    cases hPrunable with
    | trec_new s _ _ hnmem hPrunableSub hOneMsgAll =>
      obtain ⟨seen'', g1, ev1, pr1⟩ := ih _ hev1 hPrunableSub
      exact ⟨seen'',
        List.Sublist.trans
          (List.Sublist.cons _ (List.Sublist.refl _)) g1, ev1, pr1⟩
    | trec_seen s _ _ hmem hOneMsgAll =>
      obtain ⟨X0, B0, hEq, hEvT⟩ := hev _ hmem
      simp only [SessionType.tRec.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      obtain ⟨seen'', g1, ev1, pr1⟩ := ih _ hev1 hEvT
      exact ⟨seen'',
        List.Sublist.trans
          (List.Sublist.cons _ (List.Sublist.refl _)) g1, ev1, pr1⟩

-- Prefix hall transport (kept-list join): join kept-target adequacy over a finite kept
-- list. `ih` is the full preservation statement in mem-full form (matching
-- the induction output for `pfx` halls), applied per entry at the concrete
-- accumulator (no choice needed); earlier targets lift by `deep_mono_grow`.
-- Covers the `hPrunableBranch` half of `pfxInt`/`pfxExt`; the `hOneMsgAll` half for fresh
-- kept-choices is closed by the lifting lemmas below.
/-- Kept-target adequacy over a finite internal-choice kept list: join the per-branch maximality
   hypotheses along membership. -/
theorem pfxInt_hall_join {branches : List (Role × Lab × DataSort × SessionType)}
    {kept : List (Role × Lab × DataSort × SessionType)}
    (seen : List SessionType)
    (hPrunableBranch : ∀ x ∈ branches, Prunable seen x.2.2.2)
    (hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
      (r, l, s, T1) ∈ kept → ∃ T0, (r, l, s, T0) ∈ branches)
    (ih : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
      (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
      ∀ (sAcc : List SessionType),
      SeenEvidence sAcc → Prunable sAcc T0 →
      ∃ sOut, sAcc.Sublist sOut ∧ SeenEvidence sOut ∧ Prunable sOut T1)
    (ks : List (Role × Lab × DataSort × SessionType))
    (hks : ∀ e ∈ ks, e ∈ kept)
    (seenA : List SessionType) (hle : seen.Sublist seenA)
    (evA : SeenEvidence seenA) :
    ∃ seenOut, seenA.Sublist seenOut ∧ SeenEvidence seenOut ∧
      ∀ e ∈ ks, Prunable seenOut e.2.2.2 := by
  induction ks generalizing seenA with
  | nil =>
    exact ⟨seenA, List.Sublist.refl _, evA,
      fun e hmem => False.elim (List.not_mem_nil hmem)⟩
  | cons hd tl ihList =>
    obtain ⟨r0, l0, s0, U0⟩ := hd
    have hmemK : (r0, l0, s0, U0) ∈ kept := hks _ (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨T0, hmemB⟩ := hkey r0 l0 s0 U0 hmemK
    have hPrunableT0 : Prunable seenA T0 :=
      deep_mono_grow hle (hPrunableBranch _ hmemB)
    obtain ⟨seenB, gAB, evB, prB⟩ := ih T0 U0 r0 l0 s0 hmemB hmemK seenA evA hPrunableT0
    have hksTl : ∀ e ∈ tl, e ∈ kept :=
      fun e hm => hks e (List.mem_cons.mpr (Or.inr hm))
    obtain ⟨seenC, gBC, evC, hallTl⟩ :=
      ihList hksTl seenB (List.Sublist.trans hle gAB) evB
    have prB' : Prunable seenC U0 := deep_mono_grow gBC prB
    refine ⟨seenC, List.Sublist.trans gAB gBC, evC, fun e hm => ?_⟩
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hmTl
    · exact prB'
    · exact hallTl _ hmTl

/-- Kept-target adequacy over a finite external-choice kept list: join the per-branch maximality
   hypotheses along membership. -/
theorem pfxExt_hall_join {branches : List (Lab × DataSort × SessionType)}
    {kept : List (Lab × DataSort × SessionType)}
    (seen : List SessionType)
    (hPrunableBranch : ∀ x ∈ branches, Prunable seen x.2.2)
    (hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈ kept → ∃ T0, (l, s, T0) ∈ branches)
    (ih : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
      ∀ (sAcc : List SessionType),
      SeenEvidence sAcc → Prunable sAcc T0 →
      ∃ sOut, sAcc.Sublist sOut ∧ SeenEvidence sOut ∧ Prunable sOut T1)
    (ks : List (Lab × DataSort × SessionType))
    (hks : ∀ e ∈ ks, e ∈ kept)
    (seenA : List SessionType) (hle : seen.Sublist seenA)
    (evA : SeenEvidence seenA) :
    ∃ seenOut, seenA.Sublist seenOut ∧ SeenEvidence seenOut ∧
      ∀ e ∈ ks, Prunable seenOut e.2.2 := by
  induction ks generalizing seenA with
  | nil =>
    exact ⟨seenA, List.Sublist.refl _, evA,
      fun e hmem => False.elim (List.not_mem_nil hmem)⟩
  | cons hd tl ihList =>
    obtain ⟨l0, s0, U0⟩ := hd
    have hmemK : (l0, s0, U0) ∈ kept := hks _ (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨T0, hmemB⟩ := hkey l0 s0 U0 hmemK
    have hPrunableT0 : Prunable seenA T0 :=
      deep_mono_grow hle (hPrunableBranch _ hmemB)
    obtain ⟨seenB, gAB, evB, prB⟩ := ih T0 U0 l0 s0 hmemB hmemK seenA evA hPrunableT0
    have hksTl : ∀ e ∈ tl, e ∈ kept :=
      fun e hm => hks e (List.mem_cons.mpr (Or.inr hm))
    obtain ⟨seenC, gBC, evC, hallTl⟩ :=
      ihList hksTl seenB (List.Sublist.trans hle gAB) evB
    have prB' : Prunable seenC U0 := deep_mono_grow gBC prB
    refine ⟨seenC, List.Sublist.trans gAB gBC, evC, fun e hm => ?_⟩
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hmTl
    · exact prB'
    · exact hallTl _ hmTl


-- Full preservation (core lemma): `mon_tr_yes_exist` steps preserve `Deep` (at a
-- grown `seen`) with evidence threading. `base` delegates to
-- `deep_preserved_base`; `unfold` mirrors its `tRec` case via the table;
-- `pfx` runs the hPrunableBranch joins plus the lifting lemmas for `hOneMsgAll`.
/-- Deep prunability is preserved by existential yes-transitions (`mon_tr_yes_exist`), threading
   evidence and seen-lists. -/
theorem deep_preserved_exist :
    ∀ {T : SessionType} {γ : ext_tag} {T' : SessionType},
    mon_tr_yes_exist T γ T' → ∀ (seen : List SessionType),
    SeenEvidence seen → Prunable seen T →
    ∃ seenOut, seen.Sublist seenOut ∧ SeenEvidence seenOut ∧
      Prunable seenOut T' := by
  intro T γ T' hEnc seen hev hPrunable
  induction hEnc generalizing seen with
  | base hb =>
    exact deep_preserved_base hb seen hev hPrunable
  | pfxInt hne hno hkept hallEnc hNodupKept hkey ih =>
    rename_i _ kept _ _ _ _
    subst hkept
    cases hPrunable with
    | intC s _ hPrunableBranch _ =>
      obtain ⟨seenB, gAB, evB, hPrunableBranch⟩ :=
        pfxInt_hall_join seen hPrunableBranch hkey ih kept (fun e hm => hm)
          seen (List.Sublist.refl _) hev
      have hOneMsgAll : ∀ (p0 : Role) (lab0 : Lab) (S0 : DataSort),
          ExposedFrom (SessionType.internalChoice kept) p0 lab0 S0 →
          PrunableOneMsg p0 lab0 S0 (SessionType.internalChoice kept) := by
        intro p0 lab0 S0 _
        exact prunable_one_msg_intC_of_succ kept p0 lab0 S0
          (fun x hmemK hHas =>
            deep_has_acyclic (hPrunableBranch _ hmemK) _ _ _
              (has_to_exposed _ _ _ _ hHas))
      exact ⟨seenB, gAB, evB, Prunable.intC seenB kept hPrunableBranch hOneMsgAll⟩
  | pfxExt hne hneq hkept hallEnc hNodupKept hkey ih =>
    rename_i pOwn _ kept _ _ _ _
    subst hkept
    cases hPrunable with
    | extC s _ _ hPrunableBranch _ =>
      obtain ⟨seenB, gAB, evB, hPrunableBranch⟩ :=
        pfxExt_hall_join seen hPrunableBranch hkey ih kept (fun e hm => hm)
          seen (List.Sublist.refl _) hev
      have hOneMsgAll : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
          ExposedFrom (SessionType.externalChoice pOwn kept) pm lab0 S0 →
          PrunableOneMsg pm lab0 S0 (SessionType.externalChoice pOwn kept) := by
        intro pm lab0 S0 _
        by_cases heq : pOwn = pm
        · subst heq
          exact prunable_one_msg_extC_owner _ _ _ _
        · exact prunable_one_msg_extC_of_succ _ kept _ _ _ heq
            (fun x hmemK hHas =>
              deep_has_acyclic (hPrunableBranch _ hmemK) _ _ _
                (has_to_exposed _ _ _ _ hHas))
      exact ⟨seenB, gAB, evB, Prunable.extC seenB pOwn kept hPrunableBranch hOneMsgAll⟩
  | unfold hsub ih =>
    rename_i X B _ _
    have hev1 : SeenEvidence (SessionType.tRec X B :: seen) :=
      seen_ev_extend hev hPrunable
    cases hPrunable with
    | trec_new s _ _ hnmem hPrunableSub hOneMsgAll =>
      obtain ⟨seen'', g1, ev1, pr1⟩ := ih _ hev1 hPrunableSub
      exact ⟨seen'',
        List.Sublist.trans
          (List.Sublist.cons _ (List.Sublist.refl _)) g1, ev1, pr1⟩
    | trec_seen s _ _ hmem hOneMsgAll =>
      obtain ⟨X0, B0, hEq, hEvT⟩ := hev _ hmem
      simp only [SessionType.tRec.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      obtain ⟨seen'', g1, ev1, pr1⟩ := ih _ hev1 hEvT
      exact ⟨seen'',
        List.Sublist.trans
          (List.Sublist.cons _ (List.Sublist.refl _)) g1, ev1, pr1⟩

end EvidenceTable

section CoverFromDeep

-- Cover from Deep (final assembly): a well-formed monitorable deeply
-- adequate type that can drain `Q` covers `Q` (every enc-reachable split head
-- has a `GoU`). Queue induction mirroring `can_enc_of_cover`, producing
-- cover instead of consuming it: the head `GoU` comes from Deep (bridge +
-- `forced_GoU_exist`), then `drainRelRec` (pinned by uniqueness) threads
-- `Can` to the tail for the IH.
/-- Cover from deep adequacy: a well-formed monitorable deeply-prunable type that can drain `Q`
   covers every enc-reachable split of `Q` with a `GoU`. -/
theorem deep_cover : ∀ (Q : Queue) (T : SessionType),
    T.WellFormed → Drainability.Monitorable T →
    ∀ (seen : List SessionType),
    SeenEvidence seen → Prunable seen T →
    Drainability.CanAlwaysDrainInternalDeepRec T Q → has_cover T Q := by
  intro Q
  induction Q with
  | nil =>
    intro _ _ _ _ _ _ _ pre Q0 _ _ _ _ _ hEq _ hHead
    have hQ0 : Q0 = [] := by
      cases pre with
      | nil => simpa using hEq.symm
      | cons _ _ => simp at hEq
    rw [hQ0] at hHead
    simp at hHead
  | cons hd tl ih =>
    intro T hWF hMon seen hev hPrunable hCan pre Q0 V p0 lab0 S0 Q0' hEq hEnc hHead
    obtain ⟨p0h, lab0h, S0h⟩ := hd
    have hHasHd : pruneFirstInputDeepHas p0h lab0h S0h T = true :=
      has_of_canRec' p0h lab0h S0h hWF.1 hCan rfl
    obtain ⟨nGo, Ugo, dGo⟩ := forced_GoU_exist p0h lab0h S0h hMon
      (deep_has_acyclic hPrunable _ _ _ (has_to_exposed _ _ _ _ hHasHd))
      T Relation.ReflTransGen.refl hWF.1
    cases pre with
    | nil =>
      simp only [List.nil_append] at hEq
      simp only [monitor_fold_aux] at hEnc
      subst hEnc
      rw [← hEq] at hHead
      simp only [List.cons.injEq] at hHead
      obtain ⟨hHd, -⟩ := hHead
      simp only [QueueMessage.msg.injEq] at hHd
      obtain ⟨rfl, rfl, rfl⟩ := hHd
      exact ⟨nGo, Ugo, dGo⟩
    | cons ph pt =>
      simp only [List.cons_append] at hEq
      simp only [List.cons.injEq] at hEq
      obtain ⟨hHdPh, hTl⟩ := hEq
      subst hHdPh
      simp only [monitor_fold_aux] at hEnc
      obtain ⟨Tmid, hYesHd, hRest⟩ := hEnc
      have hYesHdC := hYesHd
      obtain ⟨hEhd, _⟩ := hYesHdC
      obtain ⟨EGo, hMGo⟩ := go_unfold_rel.toMaximal p0h lab0h S0h dGo hHasHd hWF
      have hEqU : Ugo = Tmid := mon_tr_yes_target_unique hWF ⟨EGo, hMGo⟩ hYesHd
      have hWFmid : Tmid.WellFormed := mon_tr_yes_preserves_wf hYesHd hWF
      have hMonMid : Drainability.Monitorable Tmid :=
        Drainability.Monitorable.of_exist hEhd hMon
      obtain ⟨seen', _, ev', pr2⟩ := deep_preserved_exist hEhd seen hev hPrunable
      have hCanMid : Drainability.CanAlwaysDrainInternalDeepRec Tmid tl := by
        have hD : Drainability.CanAlwaysDrainInternalDeepRec Ugo tl :=
          drainRelRec p0h lab0h S0h hWF dGo hCan rfl
        rw [hEqU] at hD
        exact hD
      have hCovMid : has_cover Tmid tl :=
        ih Tmid hWFmid hMonMid seen' ev' pr2 hCanMid
      exact hCovMid pt Q0 V p0 lab0 S0 Q0' hTl hRest hHead
end CoverFromDeep
