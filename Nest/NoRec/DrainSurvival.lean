import Nest.SessionUtils
import Nest.MonitorToolkit
import Nest.StuckWitness
import Nest.NoRec.PruneFunctions
import Nest.NoRec.NoRecEncoder
import Nest.SessionAdequacy
import Nest.NoRec.DrainCore
import Nest.NoRec.PrunePreservation

/-!
# DrainSurvival: drain survival, monitor-yes correspondence, cannot-prepend.

Drain survival under pruning (`drain_survives_*`), survival key/preservation lemmas,
monitor-yes correspondence (`mon_yes_prune_deep_mp/mpr`, vacuous preservation), and
`cannot_prepend_*` transport. Feeds `DrainAccept` and `DeepComplement`.
-/

section DrainSurvival

/-- Auxiliary for `drain_survives_pruning_norec`, concluding the unpacked form
    (definedness flag plus deepness of the pruned type) to avoid `Option`
    unpacking at call sites. Outer strong induction on `sizeOf T`; each
    case analyzes the drain's first step. -/
theorem drain_survives_pruning_aux_norec (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (n : Nat) (T : SessionType) (Q' : Queue), sizeOf T ≤ n → T.NoRec →
    T.WellFormed →
    CanAlwaysDrainInternalDeep T (QueueMessage.msg p lab S :: Q') →
    pruneFirstInputHas p lab S T = true ∧
      CanAlwaysDrainInternalDeep (pruneFirstInputGo p lab S T) Q' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T Q' hsize hNR hWF hR
    obtain ⟨Tn, ρ, hTr, hall⟩ := hR
    cases ρ with
    | nil =>
      have heq := overTrTrace_nil_eq hTr
      have hQ : ([] : Queue) = QueueMessage.msg p lab S :: Q' :=
        congrArg Prod.snd heq
      simp at hQ
    | cons α ρ' =>
      cases hTr with
      | step hStep hTail =>
        have hTrOrig : over_trans_trace (T, QueueMessage.msg p lab S :: Q')
            (α :: ρ') (Tn, []) :=
          over_trans_trace.step hStep hTail
        cases T with
        | tEnd =>
          cases hStep with
          | dequeue hEq _ _ => cases hEq
          | specInp hEq _ _ => cases hEq
          | sendFresh hEq _ _ => cases hEq
          | tauUnfold hU => exact False.elim (Unfold1.absurd_of_NoRec hNR hU)
        | tVar X =>
          have hCl : SessionType.IsClosed (SessionType.tVar X) := hWF.2.1
          simp [SessionType.IsClosed, SessionType.fv] at hCl
        | tRec X B => cases hNR
        | internalChoice branches =>
          cases hStep with
          | dequeue hEq _ _ => cases hEq
          | specInp hEq _ _ => cases hEq
          | tauUnfold hU => exact False.elim (Unfold1.absurd_of_NoRec hNR hU)
          | @sendFresh _ T' _ q lab' S' _ hEq hST hFresh =>
            cases hEq
            cases hST with
            | intC hmem =>
              -- No branch sends from `p` (freshness vs head message).
              have hNoP : ∀ br ∈ branches, br.1 ≠ p := by
                intro br hmemB
                obtain ⟨r', l', s', U'⟩ := br
                have hfr := hFresh _ _ _ _ hmemB _
                  (List.mem_cons.mpr (Or.inl rfl))
                intro heq
                have heq2 : r' = p := heq
                rw [heq2] at hfr
                exact hfr rfl
              have hqpF : q ≠ p := hNoP _ hmem
              -- Suffix-Deep of the fired target (queue kept).
              have hStep1 : over_trans (SessionType.internalChoice branches,
                  QueueMessage.msg p lab S :: Q')
                  (st_label.out q lab' S')
                  (T', QueueMessage.msg p lab S :: Q') :=
                over_trans.sendFresh rfl (st_trans.intC hmem) hFresh
              have h1 : over_trans_trace (SessionType.internalChoice branches,
                  QueueMessage.msg p lab S :: Q') [st_label.out q lab' S']
                  (T', QueueMessage.msg p lab S :: Q') :=
                over_trans_trace.step hStep1 (over_trans_trace.refl _)
              have hC1 : CanAlwaysDrainInternalDeep T'
                  (QueueMessage.msg p lab S :: Q') :=
                CanAlwaysDrainInternalDeep.suffix hall h1 hTail rfl
              have hNR1 : T'.NoRec := over_trans_preserves_norec hStep1 hNR
              have hWF1 : T'.WellFormed := over_trans_preserves_wf hStep1 hWF
              have hsize1 : sizeOf T' ≤ n :=
                le_trans (le_of_lt (over_trans_session_shrink_norec hStep1 hNR)) hsize
              have hltT' : sizeOf T' < n := by
                have hsh : sizeOf T' <
                    sizeOf (SessionType.internalChoice branches) := by
                  simpa using over_trans_session_shrink_norec hStep1 hNR
                omega
              obtain ⟨hHasT', hDT'⟩ := ih (sizeOf T') hltT' T' Q'
                (Nat.le_refl _) hNR1 hWF1 hC1
              -- Pruned send step (same key, freshness over the tail).
              have hFreshW : ∀ (r' : Role) (l' : Lab) (s' : DataSort)
                  (U' : SessionType),
                  (r', l', s', U') ∈ pruneGoInt p lab S branches →
                  ∀ m ∈ Q', m.1 ≠ r' := by
                intro r' l' s' U' hmemP m hm
                obtain h | h := prune_go_int_mem p lab S branches
                  (r', l', s', U') hmemP
                · obtain ⟨q2, l2, S2, U2, hmemU, hpq, heq⟩ := h
                  cases heq
                  exact absurd hpq (hNoP _ hmemU)
                · obtain ⟨q2, l2, S2, U2, hmemU, hqp2, heq⟩ := h
                  cases heq
                  exact hFresh _ _ _ _ hmemU _
                    (List.mem_cons.mpr (Or.inr hm))
              -- Head closures for the prepend (all branches via IH).
              have hHeadInt : ∀ (branches2 :
                  List (Role × Lab × DataSort × SessionType)),
                  SessionType.internalChoice
                    (pruneGoInt p lab S branches) =
                    SessionType.internalChoice branches2 → branches2 ≠ [] →
                  ∀ (br : Role × Lab × DataSort × SessionType),
                    br ∈ branches2 →
                    CanAlwaysDrainInternalDeepCore br.2.2.2 Q' := by
                intro branches2 hEq hneB br hmemB
                cases hEq
                obtain h | h := prune_go_int_mem p lab S branches br hmemB
                · obtain ⟨q2, l2, S2, U2, hmemU, hpq, heq⟩ := h
                  cases heq
                  exact absurd hpq (hNoP _ hmemU)
                · obtain ⟨q2, l2, S2, U2, hmemU, hqp2, heq⟩ := h
                  cases heq
                  have hCoreU : CanAlwaysDrainInternalDeepCore U2
                      (QueueMessage.msg p lab S :: Q') := by
                    have hHead := hall (SessionType.internalChoice branches)
                      (QueueMessage.msg p lab S :: Q') [] _
                      (over_trans_trace.refl _) hTrOrig rfl
                    obtain ⟨hIntC, -⟩ := hHead
                    exact hIntC branches rfl
                      (List.ne_nil_of_mem hmemU) _ hmemU
                  have hDU : CanAlwaysDrainInternalDeep U2
                      (QueueMessage.msg p lab S :: Q') := hCoreU.toDeep
                  have hltU : sizeOf U2 < n := by
                    have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice
                      hmemU
                    omega
                  have hNRU : U2.NoRec :=
                    noRec_of_mem_intBranches hNR hmemU
                  have hWFU : U2.WellFormed :=
                    wf_of_mem_intBranches_early hmemU hWF
                  obtain ⟨-, hDUpruned⟩ := ih (sizeOf U2) hltU U2 Q'
                    (Nat.le_refl _) hNRU hWFU hDU
                  exact hDUpruned.toCore
              have hHeadExt : ∀ (q : Role)
                  (branches2 : List (Lab × DataSort × SessionType)),
                  SessionType.internalChoice
                    (pruneGoInt p lab S branches) =
                    SessionType.externalChoice q branches2 →
                    branches2 ≠ [] →
                  NoDequeueFrom (SessionType.internalChoice
                    (pruneGoInt p lab S branches)) Q' →
                  ∃ (br : Lab × DataSort × SessionType),
                    br ∈ branches2 ∧
                    CanAlwaysDrainInternalDeepCore br.2.2 Q' := by
                intro q branches2 hEq hneB hnd
                cases hEq
              have hNDp : (SessionType.internalChoice
                  (pruneGoInt p lab S branches)).NoDupl := by
                cases hWF.1 with
                | internalChoice h_nodup h_ne h_branches =>
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
                    · obtain ⟨q2, l2, S2, U2, hmemU, hpq, heq⟩ := h
                      cases heq
                      exact absurd hpq (hNoP _ hmemU)
                    · obtain ⟨q2, l2, S2, U2, hmemU, hqp2, heq⟩ := h
                      cases heq
                      have hltU : sizeOf U2 < n := by
                        have h1 :=
                          sizeOf_SessionType_lt_sizeOf_internalChoice hmemU
                        omega
                      exact prune_first_input_go_preserves_no_dupl p lab S n U2
                        (le_of_lt hltU)
                        (h_branches _ hmemU)
              refine ⟨?_, ?_⟩
              · simp only [pruneFirstInputHas]
                exact prune_has_int_true_of_mem p lab S q lab' S' T' hqpF
                  hHasT' branches hmem
              · have hGoEq : pruneFirstInputGo p lab S
                    (SessionType.internalChoice branches)
                    = SessionType.internalChoice
                      (pruneGoInt p lab S branches) := rfl
                rw [hGoEq]
                exact deep_prepend_send_at_intC hNDp
                  (prune_go_int_map_mem p lab S branches
                    (q, lab', S', T') hmem hqpF) hFreshW hDT'
                  hHeadInt hHeadExt
        | externalChoice q branches =>
        by_cases hbeq : (q == p) = true
        · -- Same owner: first step forced to head-removal.
          have hqp : q = p := beq_iff_eq.mp hbeq
          subst q
          cases hStep with
          | @dequeue _ T' _ Qd' _ lab' S' _ hEq hmem hQd =>
            cases hEq
            obtain ⟨seenD, leftD, hQeqD, hseenD⟩ :=
              dequeue_oldest_of_some hQd
            have hOldD : oldest_from p (QueueMessage.msg p lab S :: Q')
                (QueueMessage.msg p lab' S') :=
              ⟨seenD, leftD, by simpa using hQeqD, rfl, hseenD⟩
            have hOldH : oldest_from p (QueueMessage.msg p lab S :: Q')
                (QueueMessage.msg p lab S) :=
              ⟨[], Q', rfl, rfl,
                fun _ hm => False.elim (List.not_mem_nil hm)⟩
            have hEqK := oldest_from_unique hOldD hOldH
            rw [QueueMessage.msg.injEq] at hEqK
            obtain ⟨-, hlabEq, hSEq⟩ := hEqK
            have hMsgEq : QueueMessage.msg p lab' S' =
                QueueMessage.msg p lab S := by
              rw [hlabEq, hSEq]
            have hmem' : (lab, S, T') ∈ branches := by
              simpa [hlabEq, hSEq] using hmem
            rw [hMsgEq] at hQd
            have hQdH : Queue.dequeue (QueueMessage.msg p lab S :: Q')
                (QueueMessage.msg p lab S) = some Q' :=
              Queue.dequeue_head_hit
            have hQdEq : Qd' = Q' :=
              (Option.some_inj.mp (hQdH.symm.trans hQd)).symm
            subst Qd'
            have h1 : over_trans_trace (SessionType.externalChoice p branches,
                QueueMessage.msg p lab S :: Q') [st_label.inp p lab S]
                (T', Q') :=
              over_trans_trace.step (over_trans.dequeue rfl hmem' hQd)
                (over_trans_trace.refl _)
            have hC1 : CanAlwaysDrainInternalDeep T' Q' :=
              CanAlwaysDrainInternalDeep.suffix hall h1 hTail
                (by simp [hlabEq, hSEq])
            have hHasT : pruneFirstInputHas p lab S
                (SessionType.externalChoice p branches) = true := by
              have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
              simp only [pruneFirstInputHas, hif, ite_true]
              rw [List.any_eq_true]
              exact ⟨(lab, S, T'), hmem', by simp⟩
            have hGoEq : pruneFirstInputGo p lab S
                (SessionType.externalChoice p branches) = T' := by
              have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
              simp only [pruneFirstInputGo, hif, ite_true]
              refine match hF : branches.find? (fun b => match b with
                  | (l, S', _) => l == lab && S' == S) with
                | none => ?_
                | some v => ?_
              · have hcon := (List.find?_eq_none.mp hF) _ hmem'
                simp at hcon
              · obtain ⟨l, S', U⟩ := v
                obtain ⟨hmemV, hpredV⟩ := find?_some_mem hF
                have hkeys : l = lab ∧ S' = S := by
                  have h1 : ((l == lab) && (S' == S)) = true := by
                    simpa using hpredV
                  simp at h1
                  exact h1
                obtain ⟨rfl, rfl⟩ := hkeys
                have hND : (SessionType.externalChoice p branches).NoDupl :=
                  hWF.1
                have hVU : U = T' := ext_target_unique_norec hND hmemV hmem'
                simpa [hF] using hVU
            refine ⟨hHasT, ?_⟩
            rw [hGoEq]
            exact hC1
          | @specInp _ _ _ p' _ _ _ hEq hmem hAbs =>
            cases hEq
            have hmem0 : QueueMessage.msg p lab S ∈
                (QueueMessage.msg p lab S :: Q') :=
              List.mem_cons.mpr (Or.inl rfl)
            exact (hAbs _ hmem0 rfl).elim
          | sendFresh hEq _ _ => cases hEq
          | tauUnfold hU => exact False.elim (Unfold1.absurd_of_NoRec hNR hU)
        · have hqp : q ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
          have hGoEq : pruneFirstInputGo p lab S
              (SessionType.externalChoice q branches) =
              SessionType.externalChoice q
                (pruneGoExt p lab S branches) := by
            simp only [pruneFirstInputGo, ite_eq_right hbeq]
          have hNDp : (SessionType.externalChoice q
              (pruneGoExt p lab S branches)).NoDupl := by
            have hGoND := prune_first_input_go_preserves_no_dupl p lab S n
              (SessionType.externalChoice q branches) hsize hWF.1
            rw [hGoEq] at hGoND
            exact hGoND
          have hHeadInt : ∀ (branches2 :
              List (Role × Lab × DataSort × SessionType)),
              SessionType.externalChoice q
                (pruneGoExt p lab S branches) =
                SessionType.internalChoice branches2 → branches2 ≠ [] →
              ∀ (br : Role × Lab × DataSort × SessionType),
                br ∈ branches2 →
                CanAlwaysDrainInternalDeepCore br.2.2.2 Q' := by
            intro branches2 hEq hneB br hmemB
            cases hEq
          have hHeadExt : ∀ (q2 : Role)
              (branches2 : List (Lab × DataSort × SessionType)),
              SessionType.externalChoice q
                (pruneGoExt p lab S branches) =
                SessionType.externalChoice q2 branches2 → branches2 ≠ [] →
              NoDequeueFrom (SessionType.externalChoice q
                (pruneGoExt p lab S branches)) Q' →
              ∃ (br : Lab × DataSort × SessionType),
                br ∈ branches2 ∧
                CanAlwaysDrainInternalDeepCore br.2.2 Q' := by
            intro q2 branches2 hEq hneB hnd
            cases hEq
            have hndOrig : NoDequeueFrom
                (SessionType.externalChoice q branches)
                (QueueMessage.msg p lab S :: Q') := by
              intro hcon
              obtain ⟨T0, Q0, r0, lab0, S0, hST0, hQd0⟩ := hcon
              cases hST0 with
              | extC hmem0 =>
                have hne0 : (QueueMessage.msg p lab S).1 ≠
                    (QueueMessage.msg q lab0 S0).1 := by
                  simpa using Ne.symm hqp
                obtain ⟨Q0'', _, hQ0Tail⟩ :=
                  dequeue_skip_head hne0 hQd0
                have hmemP : (lab0, S0,
                    pruneFirstInputGo p lab S T0) ∈
                    pruneGoExt p lab S branches :=
                  prune_go_ext_map_mem p lab S branches (lab0, S0, T0)
                    hmem0
                exact hnd ⟨_, _, _, _, _, st_trans.extC hmemP, hQ0Tail⟩
            have hHead := hall (SessionType.externalChoice q branches)
              (QueueMessage.msg p lab S :: Q') [] _
              (over_trans_trace.refl _) hTrOrig rfl
            obtain ⟨-, hExt, -⟩ := hHead
            have hneBOrig : branches ≠ [] := by
              cases hWF.1 with
              | externalChoice _ h_ne _ => exact h_ne
            obtain ⟨br0, hmem0, hCore0⟩ :=
              hExt q branches rfl hneBOrig hndOrig
            obtain ⟨l0, S0, U0⟩ := br0
            have hDU0 : CanAlwaysDrainInternalDeep U0
                (QueueMessage.msg p lab S :: Q') := hCore0.toDeep
            have hltU0 : sizeOf U0 < n := by
              have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice (p := q)
                hmem0
              omega
            have hNRU0 : U0.NoRec :=
              noRec_of_mem_extBranches hNR hmem0
            have hWFU0 : U0.WellFormed :=
              wf_of_mem_extBranches_early hmem0 hWF
            obtain ⟨-, hDUpruned0⟩ := ih (sizeOf U0) hltU0 U0 Q'
              (Nat.le_refl _) hNRU0 hWFU0 hDU0
            exact ⟨(l0, S0, pruneFirstInputGo p lab S U0),
              prune_go_ext_map_mem p lab S branches (l0, S0, U0) hmem0,
              hDUpruned0.toCore⟩
          cases hStep with
          | @dequeue _ T' _ Qd' _ lab' S' _ hEq hmem hQd =>
            rw [SessionType.externalChoice.injEq] at hEq
            obtain ⟨rfl, rfl⟩ := hEq
            have hST : st_trans (SessionType.externalChoice q branches)
                (st_label.inp q lab' S') T' := st_trans.extC hmem
            cases hST with
            | extC hmem =>
              have hne : (QueueMessage.msg p lab S).1 ≠
                  (QueueMessage.msg q lab' S').1 := by
                simpa using Ne.symm hqp
              obtain ⟨Q'', hQdEq, hQdTail⟩ :=
                dequeue_skip_head hne hQd
              subst Qd'
              have hStep1 : over_trans
                  (SessionType.externalChoice q branches,
                    QueueMessage.msg p lab S :: Q')
                  (st_label.inp q lab' S')
                  (T', QueueMessage.msg p lab S :: Q'') :=
                over_trans.dequeue rfl hmem hQd
              have h1 : over_trans_trace
                  (SessionType.externalChoice q branches,
                    QueueMessage.msg p lab S :: Q')
                  [st_label.inp q lab' S']
                  (T', QueueMessage.msg p lab S :: Q'') :=
                over_trans_trace.step hStep1 (over_trans_trace.refl _)
              have hC1 : CanAlwaysDrainInternalDeep T'
                  (QueueMessage.msg p lab S :: Q'') :=
                CanAlwaysDrainInternalDeep.suffix hall h1 hTail rfl
              have hNR1 : T'.NoRec :=
                over_trans_preserves_norec hStep1 hNR
              have hWF1 : T'.WellFormed :=
                over_trans_preserves_wf hStep1 hWF
              have hltT' : sizeOf T' < n := by
                have hsh : sizeOf T' <
                    sizeOf (SessionType.externalChoice q branches) := by
                  simpa using over_trans_session_shrink_norec hStep1 hNR
                omega
              obtain ⟨hHasT', hDT'⟩ := ih (sizeOf T') hltT' T' Q''
                (Nat.le_refl _) hNR1 hWF1 hC1
              have hHasT : pruneFirstInputHas p lab S
                  (SessionType.externalChoice q branches) = true := by
                simp only [pruneFirstInputHas, ite_eq_right hbeq]
                exact prune_has_ext_true_of_mem p lab S lab' S' T'
                  hHasT' branches hmem
              have hmemW : (lab', S', pruneFirstInputGo p lab S T') ∈
                  pruneGoExt p lab S branches :=
                prune_go_ext_map_mem p lab S branches
                  (lab', S', T') hmem
              refine ⟨hHasT, ?_⟩
              rw [hGoEq]
              exact deep_prepend_dequeue_at_extC hNDp hmemW hQdTail hDT'
                hHeadInt hHeadExt
          | @specInp _ T' _ _ lab' S' _ hEq hmem hAbs =>
            cases hEq with
            | refl =>
              have hAbsTail : ∀ m ∈ Q', m.1 ≠ q := fun m hm =>
                hAbs m (List.mem_cons.mpr (Or.inr hm))
              have hStep1 : over_trans
                  (SessionType.externalChoice q branches,
                    QueueMessage.msg p lab S :: Q')
                  (st_label.inp q lab' S')
                  (T', QueueMessage.msg p lab S :: Q') :=
                over_trans.specInp rfl hmem hAbs
              have h1 : over_trans_trace
                  (SessionType.externalChoice q branches,
                    QueueMessage.msg p lab S :: Q')
                  [st_label.inp q lab' S']
                  (T', QueueMessage.msg p lab S :: Q') :=
                over_trans_trace.step hStep1 (over_trans_trace.refl _)
              have hC1 : CanAlwaysDrainInternalDeep T'
                  (QueueMessage.msg p lab S :: Q') :=
                CanAlwaysDrainInternalDeep.suffix hall h1 hTail rfl
              have hNR1 : T'.NoRec :=
                over_trans_preserves_norec hStep1 hNR
              have hWF1 : T'.WellFormed :=
                over_trans_preserves_wf hStep1 hWF
              have hltT' : sizeOf T' < n := by
                have hsh : sizeOf T' <
                    sizeOf (SessionType.externalChoice q branches) := by
                  simpa using over_trans_session_shrink_norec hStep1 hNR
                omega
              obtain ⟨hHasT', hDT'⟩ := ih (sizeOf T') hltT' T' Q'
                (Nat.le_refl _) hNR1 hWF1 hC1
              have hHasT : pruneFirstInputHas p lab S
                  (SessionType.externalChoice q branches) = true := by
                simp only [pruneFirstInputHas, ite_eq_right hbeq]
                exact prune_has_ext_true_of_mem p lab S lab' S' T'
                  hHasT' branches hmem
              have hmemW : (lab', S', pruneFirstInputGo p lab S T') ∈
                  pruneGoExt p lab S branches :=
                prune_go_ext_map_mem p lab S branches
                  (lab', S', T') hmem
              refine ⟨hHasT, ?_⟩
              rw [hGoEq]
              exact deep_prepend_spec_at_extC hNDp hmemW hAbsTail hDT'
                hHeadInt hHeadExt
          | sendFresh hEq _ _ => cases hEq
          | tauUnfold hU => exact False.elim (Unfold1.absurd_of_NoRec hNR hU)



/-- `tRec`-unfold algebra for the vacuous drain aux: under vacuousness the
    unfolding is the body (`subst_noop`), so `Go (f+1)` at the `tRec` head
    is `Go f` at the body and `Has`-true transfers from `trec_yes`. The
    fuel-IH input `ihB` (conclusion of the aux at `B`, fuel `f`) is taken
    as a premise; clause-instantiation (`Deep (tRec)` to `Deep B`) and the
    fuel-IH application itself live in the aux caller. -/
theorem drain_survives_tRec_vacuous (p : Role) (lab : Lab) (S : DataSort)
    (f : Nat) (X : String) (B : SessionType) (Q' : Queue)
    (hVac : (SessionType.tRec X B).VacuousRec)
    (hAd : PruneAdequate p lab S (f + 1) (SessionType.tRec X B))
    (ihB : pruneFirstInputDeepHas p lab S B = true ∧
      CanAlwaysDrainInternalDeep (pruneFirstInputDeepGo p lab S f B) Q') :
    pruneFirstInputDeepHas p lab S (SessionType.tRec X B) = true ∧
      CanAlwaysDrainInternalDeep
        (pruneFirstInputDeepGo p lab S (f + 1) (SessionType.tRec X B)) Q' := by
  cases hAd with
  | @trec_yes _ _ _ hHas _ =>
    cases hVac with
    | trec hfree _ =>
      have hSubEq : substSessionType B X (SessionType.tRec X B) = B :=
        subst_noop B X _ hfree
      have hGoEq : pruneFirstInputDeepGo p lab S (f + 1)
          (SessionType.tRec X B) = pruneFirstInputDeepGo p lab S f B := by
        simp only [pruneFirstInputDeepGo, hHas, ite_true, hSubEq]
      refine ⟨hHas, ?_⟩
      rw [hGoEq]
      exact ihB.2
  | @trec_vac _ _ _ hfree _ =>
    cases hVac with
    | trec hfree' _ =>
      have hSubEq : substSessionType B X (SessionType.tRec X B) = B :=
        subst_noop B X _ hfree
      have hHasT : pruneFirstInputDeepHas p lab S (SessionType.tRec X B) = true :=
        ihB.1
      have hGoEq : pruneFirstInputDeepGo p lab S (f + 1)
          (SessionType.tRec X B) = pruneFirstInputDeepGo p lab S f B := by
        simp only [pruneFirstInputDeepGo, hHasT, ite_true, hSubEq]
      refine ⟨hHasT, ?_⟩
      rw [hGoEq]
      exact ihB.2



/-- Auxiliary for the vacuous drain port: same unpacked conclusion as
    `drain_survives_deep_pruning_aux_norec`, with `NoRec` replaced by
    `VacuousRec + WellFormed + BalancedW + PruneAdequate` (no `HasE`:
    `Has`-bool conclusions are proved, never assumed). Nested
    fuel-outer/size-inner induction (mirroring `mon_yes_prune_deep_mp`):
    choice cases recurse at the same fuel via the size IH (branch targets are
    strict subterms; adequacy/validity thread through member inversions);
    the `tRec` case unfolds via the `Deep` `tRec` clause,
    deletes the binder by vacuousness (`subst_noop`), and descends through
    the fuel IH, closing with `drain_survives_tRec_vacuous`. -/
theorem drain_survives_deep_pruning_aux_vacuous (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (fuel : Nat) (n : Nat) (T : SessionType) (Q' : Queue),
      sizeOf T ≤ n → T.VacuousRec → T.WellFormed →
      PruneAdequate p lab S fuel T →
      CanAlwaysDrainInternalDeep T (QueueMessage.msg p lab S :: Q') →
      pruneFirstInputDeepHas p lab S T = true ∧
        CanAlwaysDrainInternalDeep (pruneFirstInputDeepGo p lab S fuel T) Q' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihF =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihN =>
      intro T Q' hsize hVac hWF hAd hR
      obtain ⟨Tn, ρ, hTr, hall⟩ := hR
      cases ρ with
      | nil =>
        have heq := overTrTrace_nil_eq hTr
        have hQ : ([] : Queue) = QueueMessage.msg p lab S :: Q' :=
          congrArg Prod.snd heq
        simp at hQ
      | cons α ρ' =>
        cases hTr with
        | step hStep hTail =>
          have hTrOrig : over_trans_trace (T, QueueMessage.msg p lab S :: Q')
              (α :: ρ') (Tn, []) :=
            over_trans_trace.step hStep hTail
          cases T with
          | tEnd =>
            cases hStep with
            | dequeue hEq _ _ => cases hEq
            | specInp hEq _ _ => cases hEq
            | sendFresh hEq _ _ => cases hEq
            | tauUnfold hU => cases hU
          | tVar X =>
            have hCl : SessionType.IsClosed (SessionType.tVar X) := hWF.2.1
            simp [SessionType.IsClosed, SessionType.fv] at hCl
          | tRec X B =>
            cases hAd with
            | @trec_yes f _ _ hHas hsub =>
              cases hVac with
              | trec hfree hVacB =>
                have hSubEq : substSessionType B X (SessionType.tRec X B) = B :=
                  subst_noop B X _ hfree
                have hsubB : PruneAdequate p lab S f B := by
                  rw [←hSubEq]
                  exact hsub
                have hTrec := (hall (SessionType.tRec X B)
                  (QueueMessage.msg p lab S :: Q') [] _ (over_trans_trace.refl _)
                  hTrOrig (by simp)).2.2
                have hCoreB := hTrec X B rfl
                have hDB : CanAlwaysDrainInternalDeep B
                    (QueueMessage.msg p lab S :: Q') := hCoreB.toDeep
                have hWFB : B.WellFormed := by
                  have hWsub : (substSessionType B X
                      (SessionType.tRec X B)).WellFormed :=
                    SessionType.wellFormedUnfold hWF
                      (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
                  rwa [hSubEq] at hWsub
                obtain ⟨hHasB, hDT'⟩ := ihF f (by omega) (sizeOf B) B Q'
                  (Nat.le_refl _) hVacB hWFB hsubB hDB
                exact drain_survives_tRec_vacuous p lab S f X B Q'
                  (SessionType.VacuousRec.trec hfree hVacB)
                  (PruneAdequate.trec_yes hHas hsub) ⟨hHasB, hDT'⟩
            | @trec_vac f _ _ hfree hsub =>
              cases hVac with
              | trec hfree' hVacB =>
                have hSubEq : substSessionType B X (SessionType.tRec X B) = B :=
                  subst_noop B X _ hfree
                have hsubB : PruneAdequate p lab S f B := hsub
                have hTrec := (hall (SessionType.tRec X B)
                  (QueueMessage.msg p lab S :: Q') [] _ (over_trans_trace.refl _)
                  hTrOrig (by simp)).2.2
                have hCoreB := hTrec X B rfl
                have hDB : CanAlwaysDrainInternalDeep B
                    (QueueMessage.msg p lab S :: Q') := hCoreB.toDeep
                have hWFB : B.WellFormed := by
                  have hWsub : (substSessionType B X
                      (SessionType.tRec X B)).WellFormed :=
                    SessionType.wellFormedUnfold hWF
                      (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
                  rwa [hSubEq] at hWsub
                obtain ⟨hHasB, hDT'⟩ := ihF f (by omega) (sizeOf B) B Q'
                  (Nat.le_refl _) hVacB hWFB hsubB hDB
                exact drain_survives_tRec_vacuous p lab S f X B Q'
                  (SessionType.VacuousRec.trec hfree hVacB)
                  (PruneAdequate.trec_vac hfree hsub) ⟨hHasB, hDT'⟩
          | internalChoice branches =>
            cases hAd with
            | intC hallAd =>
              cases hStep with
              | dequeue hEq _ _ => cases hEq
              | specInp hEq _ _ => cases hEq
              | @sendFresh _ T' _ q lab' S' _ hEq hST hFresh =>
                cases hEq
                cases hST with
                | intC hmem =>
                  -- No branch sends from `p` (freshness vs head message).
                  have hNoP : ∀ br ∈ branches, br.1 ≠ p := by
                    intro br hmemB
                    obtain ⟨r', l', s', U'⟩ := br
                    have hfr := hFresh _ _ _ _ hmemB _
                      (List.mem_cons.mpr (Or.inl rfl))
                    intro heq
                    have heq2 : r' = p := heq
                    rw [heq2] at hfr
                    exact hfr rfl
                  have hqpF : q ≠ p := hNoP _ hmem
                  -- Suffix-Deep of the fired target (queue kept).
                  have hStep1 : over_trans (SessionType.internalChoice branches,
                      QueueMessage.msg p lab S :: Q')
                      (st_label.out q lab' S')
                      (T', QueueMessage.msg p lab S :: Q') :=
                    over_trans.sendFresh rfl (st_trans.intC hmem) hFresh
                  have h1 : over_trans_trace (SessionType.internalChoice branches,
                      QueueMessage.msg p lab S :: Q') [st_label.out q lab' S']
                      (T', QueueMessage.msg p lab S :: Q') :=
                    over_trans_trace.step hStep1 (over_trans_trace.refl _)
                  have hC1 : CanAlwaysDrainInternalDeep T'
                      (QueueMessage.msg p lab S :: Q') :=
                    CanAlwaysDrainInternalDeep.suffix hall h1 hTail rfl
                  have hVac1 : T'.VacuousRec :=
                    SessionType.VacuousRec.of_internalChoice hVac hmem
                  have hWF1 : T'.WellFormed :=
                    over_trans_preserves_wf hStep1 hWF
                  have hAdT' : PruneAdequate p lab S fuel T' := hallAd _ hmem
                  have hltT' : sizeOf T' < n := by
                    have hsh : sizeOf T' <
                        sizeOf (SessionType.internalChoice branches) :=
                      sizeOf_SessionType_lt_sizeOf_internalChoice hmem
                    omega
                  obtain ⟨hHasT', hDT'⟩ := ihN (sizeOf T') hltT' T' Q'
                    (Nat.le_refl _) hVac1 hWF1 hAdT' hC1
                  -- The fired branch reaches, so the filtered list is nonempty.
                  have hmemF : (q, lab', S',
                      pruneFirstInputDeepGo p lab S fuel T') ∈
                      pruneGoDeepInt p lab S fuel branches :=
                    prune_go_deep_int_map_mem p lab S fuel branches (q, lab', S', T')
                      hmem hHasT'
                  have hne : pruneGoDeepInt p lab S fuel branches ≠ [] :=
                    List.ne_nil_of_mem hmemF
                  have hGoEq : pruneFirstInputDeepGo p lab S fuel
                      (SessionType.internalChoice branches)
                      = SessionType.internalChoice
                        (pruneGoDeepInt p lab S fuel branches) := by
                    simp only [pruneFirstInputDeepGo]
                  -- Pruned send step (same key, freshness over the tail).
                  have hFreshW : ∀ (r' : Role) (l' : Lab) (s' : DataSort)
                      (U' : SessionType),
                      (r', l', s', U') ∈ pruneGoDeepInt p lab S fuel branches →
                      ∀ m ∈ Q', m.1 ≠ r' := by
                    intro r' l' s' U' hmemP m hm
                    obtain ⟨q2, l2, S2, U2, hmemU, _, heq⟩ :=
                      prune_go_deep_int_mem p lab S fuel branches
                        (r', l', s', U') hmemP
                    cases heq
                    exact hFresh _ _ _ _ hmemU _
                      (List.mem_cons.mpr (Or.inr hm))
                  -- Head closures for the prepend (kept branches via IH).
                  have hHeadInt : ∀ (branches2 :
                      List (Role × Lab × DataSort × SessionType)),
                      SessionType.internalChoice
                        (pruneGoDeepInt p lab S fuel branches) =
                        SessionType.internalChoice branches2 → branches2 ≠ [] →
                      ∀ (br : Role × Lab × DataSort × SessionType),
                        br ∈ branches2 →
                        CanAlwaysDrainInternalDeepCore br.2.2.2 Q' := by
                    intro branches2 hEq hneB br hmemB
                    cases hEq
                    obtain ⟨q2, l2, S2, U2, hmemU, _, heq⟩ :=
                      prune_go_deep_int_mem p lab S fuel branches br hmemB
                    cases heq
                    have hCoreU : CanAlwaysDrainInternalDeepCore U2
                        (QueueMessage.msg p lab S :: Q') := by
                      have hHead := hall (SessionType.internalChoice branches)
                        (QueueMessage.msg p lab S :: Q') [] _
                        (over_trans_trace.refl _) hTrOrig rfl
                      obtain ⟨hIntC, -⟩ := hHead
                      exact hIntC branches rfl
                        (List.ne_nil_of_mem hmemU) _ hmemU
                    have hDU : CanAlwaysDrainInternalDeep U2
                        (QueueMessage.msg p lab S :: Q') := hCoreU.toDeep
                    have hltU : sizeOf U2 < n := by
                      have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice
                        hmemU
                      omega
                    have hVacU : U2.VacuousRec :=
                      SessionType.VacuousRec.of_internalChoice hVac hmemU
                    have hWFU : U2.WellFormed :=
                      wf_of_mem_intBranches_early hmemU hWF
                    have hAdU : PruneAdequate p lab S fuel U2 :=
                      hallAd _ hmemU
                    obtain ⟨-, hDUpruned⟩ := ihN (sizeOf U2) hltU U2 Q'
                      (Nat.le_refl _) hVacU hWFU hAdU hDU
                    exact hDUpruned.toCore
                  have hHeadExt : ∀ (q : Role)
                      (branches2 : List (Lab × DataSort × SessionType)),
                      SessionType.internalChoice
                        (pruneGoDeepInt p lab S fuel branches) =
                        SessionType.externalChoice q branches2 →
                        branches2 ≠ [] →
                      NoDequeueFrom (SessionType.internalChoice
                        (pruneGoDeepInt p lab S fuel branches)) Q' →
                      ∃ (br : Lab × DataSort × SessionType),
                        br ∈ branches2 ∧
                        CanAlwaysDrainInternalDeepCore br.2.2 Q' := by
                    intro q branches2 hEq hneB hnd
                    cases hEq
                  have hNDp : (SessionType.internalChoice
                      (pruneGoDeepInt p lab S fuel branches)).NoDupl := by
                    have hGoND := prune_first_input_deep_go_preserves_no_dupl
                      p lab S fuel n (SessionType.internalChoice branches) hsize
                      hWF.1
                    rw [hGoEq] at hGoND
                    exact hGoND
                  refine ⟨?_, ?_⟩
                  · -- Has: all branch senders differ (freshness) and the
                    -- fired target reaches.
                    have hAllP : pruneAllNonP p branches = true :=
                      prune_all_non_p_true_of_all_ne p branches hNoP
                    have hAny : pruneHasDeepIntAny p lab S branches = true :=
                      prune_has_deep_int_any_true_of_mem p lab S branches _ _ _ _
                        hHasT' hmem
                    simp [pruneFirstInputDeepHas, hAllP, hAny]
                  · rw [hGoEq]
                    exact deep_prepend_send_at_intC hNDp hmemF hFreshW hDT'
                      hHeadInt hHeadExt
              | tauUnfold hU => cases hU
          | externalChoice q branches =>
            cases hAd with
            | extC hallAd =>
              by_cases hbeq : (q == p) = true
              · -- Same owner: first step forced to head-removal.
                have hqp : q = p := beq_iff_eq.mp hbeq
                subst q
                cases hStep with
                | @dequeue _ T' _ Qd' _ lab' S' _ hEq hmem hQd =>
                  injection hEq with hpeq hbeq'
                  subst hpeq
                  subst hbeq'
                  obtain ⟨seenD, leftD, hQeqD, hseenD⟩ :=
                    dequeue_oldest_of_some hQd
                  have hOldD : oldest_from p (QueueMessage.msg p lab S :: Q')
                      (QueueMessage.msg p lab' S') :=
                    ⟨seenD, leftD, by simpa using hQeqD, rfl, hseenD⟩
                  have hOldH : oldest_from p (QueueMessage.msg p lab S :: Q')
                      (QueueMessage.msg p lab S) :=
                    ⟨[], Q', rfl, rfl,
                      fun _ hm => False.elim (List.not_mem_nil hm)⟩
                  have hEqK := oldest_from_unique hOldD hOldH
                  rw [QueueMessage.msg.injEq] at hEqK
                  obtain ⟨-, hlabEq, hSEq⟩ := hEqK
                  have hMsgEq : QueueMessage.msg p lab' S' =
                      QueueMessage.msg p lab S := by
                    rw [hlabEq, hSEq]
                  have hmem' : (lab, S, T') ∈ branches := by
                    simpa [hlabEq, hSEq] using hmem
                  rw [hMsgEq] at hQd
                  have hQdH : Queue.dequeue (QueueMessage.msg p lab S :: Q')
                      (QueueMessage.msg p lab S) = some Q' :=
                    Queue.dequeue_head_hit
                  have hQdEq : Qd' = Q' :=
                    (Option.some_inj.mp (hQdH.symm.trans hQd)).symm
                  subst Qd'
                  have h1 : over_trans_trace (SessionType.externalChoice p branches,
                      QueueMessage.msg p lab S :: Q') [st_label.inp p lab S]
                      (T', Q') :=
                    over_trans_trace.step (over_trans.dequeue rfl hmem' hQd)
                      (over_trans_trace.refl _)
                  have hC1 : CanAlwaysDrainInternalDeep T' Q' :=
                    CanAlwaysDrainInternalDeep.suffix hall h1 hTail
                      (by simp [hlabEq, hSEq])
                  have hHasT : pruneFirstInputDeepHas p lab S
                      (SessionType.externalChoice p branches) = true := by
                    have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
                    simp only [pruneFirstInputDeepHas, hif, ite_true]
                    rw [List.any_eq_true]
                    exact ⟨(lab, S, T'), hmem', by simp⟩
                  have hGoEq : pruneFirstInputDeepGo p lab S fuel
                      (SessionType.externalChoice p branches) = T' := by
                    have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
                    simp only [pruneFirstInputDeepGo, hif, ite_true]
                    refine match hF : branches.find? (fun b => match b with
                        | (l, S', _) => l == lab && S' == S) with
                      | none => ?_
                      | some v => ?_
                    · have hcon := (List.find?_eq_none.mp hF) _ hmem'
                      simp at hcon
                    · obtain ⟨l, S', U⟩ := v
                      obtain ⟨hmemV, hpredV⟩ := find?_some_mem hF
                      have hkeys : l = lab ∧ S' = S := by
                        have h1 : ((l == lab) && (S' == S)) = true := by
                          simpa using hpredV
                        simp at h1
                        exact h1
                      obtain ⟨rfl, rfl⟩ := hkeys
                      have hND : (SessionType.externalChoice p branches).NoDupl :=
                        hWF.1
                      have hVU : U = T' := ext_target_unique_norec hND hmemV hmem'
                      simpa [hF] using hVU
                  refine ⟨hHasT, ?_⟩
                  rw [hGoEq]
                  exact hC1
                | @specInp _ _ _ p' _ _ _ hEq hmem hAbs =>
                  injection hEq with hpeq hbeq'
                  subst hpeq
                  subst hbeq'
                  have hmem0 : QueueMessage.msg p lab S ∈
                    (QueueMessage.msg p lab S :: Q') :=
                    List.mem_cons.mpr (Or.inl rfl)
                  exact (hAbs _ hmem0 rfl).elim
                | sendFresh hEq _ _ => cases hEq
                | tauUnfold hU => cases hU
              · -- Different owner: replay the `q` step on the tail.
                have hqp : q ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
                have hHeadInt : ∀ (branches2 :
                    List (Role × Lab × DataSort × SessionType)),
                    SessionType.externalChoice q
                      (pruneGoDeepExt p lab S fuel branches) =
                      SessionType.internalChoice branches2 → branches2 ≠ [] →
                    ∀ (br : Role × Lab × DataSort × SessionType),
                      br ∈ branches2 →
                      CanAlwaysDrainInternalDeepCore br.2.2.2 Q' := by
                  intro branches2 hEq hneB br hmemB
                  cases hEq
                cases hStep with
                | @dequeue _ T' _ Qd' _ lab' S' _ hEq hmem hQd =>
                  injection hEq with hpeq hbeq'
                  subst hpeq
                  subst hbeq'
                  have hne : (QueueMessage.msg p lab S).1 ≠
                      (QueueMessage.msg q lab' S').1 := by
                    simpa using Ne.symm hqp
                  obtain ⟨Q'', hQdEq, hQdTail⟩ :=
                    dequeue_skip_head hne hQd
                  subst Qd'
                  have hStep1 : over_trans
                      (SessionType.externalChoice q branches,
                        QueueMessage.msg p lab S :: Q')
                      (st_label.inp q lab' S')
                      (T', QueueMessage.msg p lab S :: Q'') :=
                    over_trans.dequeue rfl hmem hQd
                  have h1 : over_trans_trace
                      (SessionType.externalChoice q branches,
                        QueueMessage.msg p lab S :: Q')
                      [st_label.inp q lab' S']
                      (T', QueueMessage.msg p lab S :: Q'') :=
                    over_trans_trace.step hStep1 (over_trans_trace.refl _)
                  have hC1 : CanAlwaysDrainInternalDeep T'
                      (QueueMessage.msg p lab S :: Q'') :=
                    CanAlwaysDrainInternalDeep.suffix hall h1 hTail rfl
                  have hVac1 : T'.VacuousRec :=
                    SessionType.VacuousRec.of_externalChoice hVac hmem
                  have hWF1 : T'.WellFormed :=
                    over_trans_preserves_wf hStep1 hWF
                  have hAdT' : PruneAdequate p lab S fuel T' := hallAd _ hmem
                  have hltT' : sizeOf T' < n := by
                    have hsh : sizeOf T' <
                        sizeOf (SessionType.externalChoice q branches) :=
                      sizeOf_SessionType_lt_sizeOf_externalChoice hmem
                    omega
                  obtain ⟨hHasT', hDT'⟩ := ihN (sizeOf T') hltT' T' Q''
                    (Nat.le_refl _) hVac1 hWF1 hAdT' hC1
                  have hmemF : (lab', S',
                      pruneFirstInputDeepGo p lab S fuel T') ∈
                      pruneGoDeepExt p lab S fuel branches :=
                    prune_go_deep_ext_map_mem p lab S fuel branches (lab', S', T')
                      hmem hHasT'
                  have hneF : pruneGoDeepExt p lab S fuel branches ≠ [] :=
                    List.ne_nil_of_mem hmemF
                  have hGoEq : pruneFirstInputDeepGo p lab S fuel
                      (SessionType.externalChoice q branches) =
                      SessionType.externalChoice q
                        (pruneGoDeepExt p lab S fuel branches) := by
                    simp only [pruneFirstInputDeepGo, ite_eq_right hbeq]
                  have hNDp : (SessionType.externalChoice q
                      (pruneGoDeepExt p lab S fuel branches)).NoDupl := by
                    have hGoND := prune_first_input_deep_go_preserves_no_dupl
                      p lab S fuel n (SessionType.externalChoice q branches) hsize
                      hWF.1
                    rw [hGoEq] at hGoND
                    exact hGoND
                  have hHasT : pruneFirstInputDeepHas p lab S
                      (SessionType.externalChoice q branches) = true := by
                    simp only [pruneFirstInputDeepHas, ite_eq_right hbeq]
                    exact prune_has_deep_ext_true_of_mem p lab S lab' S' T'
                      hHasT' branches hmem
                  have hSTW : st_trans (SessionType.externalChoice q
                      (pruneGoDeepExt p lab S fuel branches))
                      (st_label.inp q lab' S')
                      (pruneFirstInputDeepGo p lab S fuel T') :=
                    st_trans.extC hmemF
                  -- The fired dequeue contradicts any no-dequeue hypothesis.
                  have hHeadExt : ∀ (q2 : Role)
                      (branches2 : List (Lab × DataSort × SessionType)),
                      SessionType.externalChoice q
                        (pruneGoDeepExt p lab S fuel branches) =
                        SessionType.externalChoice q2 branches2 →
                        branches2 ≠ [] →
                      NoDequeueFrom (SessionType.externalChoice q
                        (pruneGoDeepExt p lab S fuel branches)) Q' →
                      ∃ (br : Lab × DataSort × SessionType),
                        br ∈ branches2 ∧
                        CanAlwaysDrainInternalDeepCore br.2.2 Q' := by
                    intro q2 branches2 hEq hneB hnd
                    exact False.elim
                      (hnd ⟨_, _, _, _, _, hSTW, hQdTail⟩)
                  refine ⟨hHasT, ?_⟩
                  rw [hGoEq]
                  exact deep_prepend_dequeue_at_extC hNDp hmemF hQdTail hDT'
                    hHeadInt hHeadExt
                | tauUnfold hU => cases hU
                | @specInp _ T' _ _ lab' S' _ hEq hmem hAbs =>
                  injection hEq with hpeq hbeq'
                  subst hpeq
                  subst hbeq'
                  have hAbsTail : ∀ m ∈ Q', m.1 ≠ q := fun m hm =>
                    hAbs m (List.mem_cons.mpr (Or.inr hm))
                  have hStep1 : over_trans
                      (SessionType.externalChoice q branches,
                        QueueMessage.msg p lab S :: Q')
                      (st_label.inp q lab' S')
                      (T', QueueMessage.msg p lab S :: Q') :=
                    over_trans.specInp rfl hmem hAbs
                  have h1 : over_trans_trace
                      (SessionType.externalChoice q branches,
                        QueueMessage.msg p lab S :: Q')
                      [st_label.inp q lab' S']
                      (T', QueueMessage.msg p lab S :: Q') :=
                    over_trans_trace.step hStep1 (over_trans_trace.refl _)
                  have hC1 : CanAlwaysDrainInternalDeep T'
                      (QueueMessage.msg p lab S :: Q') :=
                    CanAlwaysDrainInternalDeep.suffix hall h1 hTail rfl
                  have hVac1 : T'.VacuousRec :=
                    SessionType.VacuousRec.of_externalChoice hVac hmem
                  have hWF1 : T'.WellFormed :=
                    over_trans_preserves_wf hStep1 hWF
                  have hAdT' : PruneAdequate p lab S fuel T' := hallAd _ hmem
                  have hltT' : sizeOf T' < n := by
                    have hsh : sizeOf T' <
                        sizeOf (SessionType.externalChoice q branches) :=
                      sizeOf_SessionType_lt_sizeOf_externalChoice hmem
                    omega
                  obtain ⟨hHasT', hDT'⟩ := ihN (sizeOf T') hltT' T' Q'
                    (Nat.le_refl _) hVac1 hWF1 hAdT' hC1
                  have hmemF : (lab', S',
                      pruneFirstInputDeepGo p lab S fuel T') ∈
                      pruneGoDeepExt p lab S fuel branches :=
                    prune_go_deep_ext_map_mem p lab S fuel branches (lab', S', T')
                      hmem hHasT'
                  have hneF : pruneGoDeepExt p lab S fuel branches ≠ [] :=
                    List.ne_nil_of_mem hmemF
                  have hGoEq : pruneFirstInputDeepGo p lab S fuel
                      (SessionType.externalChoice q branches) =
                      SessionType.externalChoice q
                        (pruneGoDeepExt p lab S fuel branches) := by
                    simp only [pruneFirstInputDeepGo, ite_eq_right hbeq]
                  have hNDp : (SessionType.externalChoice q
                      (pruneGoDeepExt p lab S fuel branches)).NoDupl := by
                    have hGoND := prune_first_input_deep_go_preserves_no_dupl
                      p lab S fuel n (SessionType.externalChoice q branches) hsize
                      hWF.1
                    rw [hGoEq] at hGoND
                    exact hGoND
                  have hHasT : pruneFirstInputDeepHas p lab S
                      (SessionType.externalChoice q branches) = true := by
                    simp only [pruneFirstInputDeepHas, ite_eq_right hbeq]
                    exact prune_has_deep_ext_true_of_mem p lab S lab' S' T'
                      hHasT' branches hmem
                  -- Absence at the head yields a kept witness via the drain.
                  have hHeadExt : ∀ (q2 : Role)
                      (branches2 : List (Lab × DataSort × SessionType)),
                      SessionType.externalChoice q
                        (pruneGoDeepExt p lab S fuel branches) =
                        SessionType.externalChoice q2 branches2 →
                        branches2 ≠ [] →
                      NoDequeueFrom (SessionType.externalChoice q
                        (pruneGoDeepExt p lab S fuel branches)) Q' →
                      ∃ (br : Lab × DataSort × SessionType),
                        br ∈ branches2 ∧
                        CanAlwaysDrainInternalDeepCore br.2.2 Q' := by
                    intro q2 branches2 hEq hneB hnd
                    cases hEq
                    have hndOrig : NoDequeueFrom
                        (SessionType.externalChoice q branches)
                        (QueueMessage.msg p lab S :: Q') :=
                      absence_imp_noDequeueFrom rfl hAbs
                    have hHead := hall
                      (SessionType.externalChoice q branches)
                      (QueueMessage.msg p lab S :: Q') [] _
                      (over_trans_trace.refl _) hTrOrig rfl
                    obtain ⟨-, hExt, -⟩ := hHead
                    have hneBOrig : branches ≠ [] := by
                      cases hWF.1 with
                      | externalChoice _ h_ne _ => exact h_ne
                    obtain ⟨br0, hmem0, hCore0⟩ :=
                      hExt q branches rfl hneBOrig hndOrig
                    obtain ⟨l0, S0, U0⟩ := br0
                    have hDU0 : CanAlwaysDrainInternalDeep U0
                        (QueueMessage.msg p lab S :: Q') := hCore0.toDeep
                    have hltU0 : sizeOf U0 < n := by
                      have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice
                        (p := q) hmem0
                      omega
                    have hVacU0 : U0.VacuousRec :=
                      SessionType.VacuousRec.of_externalChoice hVac hmem0
                    have hWFU0 : U0.WellFormed :=
                      wf_of_mem_extBranches_early hmem0 hWF
                    have hAdU0 : PruneAdequate p lab S fuel U0 :=
                      hallAd _ hmem0
                    obtain ⟨hHasU0, hDUpruned0⟩ := ihN (sizeOf U0) hltU0 U0
                      Q' (Nat.le_refl _) hVacU0 hWFU0 hAdU0 hDU0
                    exact ⟨(l0, S0, pruneFirstInputDeepGo p lab S fuel U0),
                      prune_go_deep_ext_map_mem p lab S fuel branches (l0, S0, U0)
                        hmem0 hHasU0,
                      hDUpruned0.toCore⟩
                  refine ⟨hHasT, ?_⟩
                  rw [hGoEq]
                  exact deep_prepend_spec_at_extC hNDp hmemF hAbsTail hDT'
                    hHeadInt hHeadExt
                | sendFresh hEq _ _ => cases hEq



/-- Label-`Nodup` strengthens to label/sort-pair `Nodup` on external
    branches (equal pairs have equal labels). -/
private theorem extPair_nodup_of_label_nodup
    (branches : List (Lab × DataSort × SessionType))
    (h : (List.map (fun x : Lab × DataSort × SessionType => x.1)
      branches).Nodup) :
    (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      branches).Nodup := by
  induction branches with
  | nil => exact List.nodup_nil
  | cons hd tl ih =>
    obtain ⟨l, S', U⟩ := hd
    simp only [List.map_cons] at h ⊢
    rw [List.nodup_cons] at h ⊢
    obtain ⟨hHead, hTail⟩ := h
    refine ⟨?_, ih hTail⟩
    intro hcon
    apply hHead
    obtain ⟨x, hmemX, hEq⟩ := List.mem_map.mp hcon
    apply List.mem_map.mpr
    exact ⟨x, hmemX, congrArg Prod.fst hEq⟩



end DrainSurvival

section SurvivalKeys

/-- Deep-filtered internal branches keep a sublist of the
    `(role, label, sort)` triple keys. -/
private theorem prune_go_deep_int_keys3_sublist (p : Role) (lab : Lab)
    (S : DataSort) (fuel : Nat)
    (branches : List (Role × Lab × DataSort × SessionType)) :
    List.Sublist
      (List.map
        (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
        (pruneGoDeepInt p lab S fuel branches))
      (List.map
        (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
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


/-- Existential monitor derivations reach under adequacy: any `mon_tr_yes_exist`
    derivation for `recv p` forces `DeepHas`, given fuel adequacy (which rules
    out `Has`-false `tRec` heads, so adequacy everywhere implies `Has`-true
    along the `tRec` spine), well-formedness, and weakened balancedness.
    Strong induction on `sizeOf` (branch targets shrink); `tRec` closes by
    adequacy inversion (`trec_yes` supplies `Has`-true directly); coverage
    uses the IH at smaller size with adequacy from `hall` inversion. -/
private theorem enc_exist_imp_deep_has_adequate (p : Role) (lab : Lab) (S : DataSort)
    (fuel : Nat) :
    ∀ (n : Nat) (T : SessionType), sizeOf T ≤ n →
    PruneAdequate p lab S fuel T → T.WellFormed → T.VacuousRec →
    ∀ (T1 : SessionType), mon_tr_yes_exist T (ext_tag.recv p lab S) T1 →
    pruneFirstInputDeepHas p lab S T = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hsize hAd hWF hVac T1 hE
    cases T with
    | tEnd =>
      cases hE with
      | base hb => cases hb
    | tVar X =>
      have hCl : SessionType.IsClosed (SessionType.tVar X) := hWF.2.1
      simp [SessionType.IsClosed, SessionType.fv] at hCl
    | tRec X B =>
      cases hAd with
      | trec_yes hHas _ => exact hHas
      | @trec_vac f _ _ hfree hsub =>
        have hSu : substSessionType B X (SessionType.tRec X B) = B :=
          subst_noop B X _ hfree
        have hE' : mon_tr_yes_exist B (ext_tag.recv p lab S) T1 := by
          have h := mon_tr_yes_exist_trec_inv hE
          rwa [hSu] at h
        have hWFB : B.WellFormed :=
          SessionType.WellFormed.of_tRecBody hWF hfree
        have hVacB : B.VacuousRec := by
          cases hVac with
          | trec _ h => exact h
        have hlt : sizeOf B < n := by
          have h1 : sizeOf B < sizeOf (SessionType.tRec X B) := by simp
          omega
        have hsubB : PruneAdequate p lab S (f + 1) B :=
          PruneAdequate.mono (Nat.le_succ f) hsub
        exact ih (sizeOf B) hlt B (Nat.le_refl _) hsubB hWFB hVacB T1 hE'
    | internalChoice branches =>
      cases hE with
      | base hb => cases hb
      | @pfxInt _ kept _ _ _ _ hne hno hkept hall hNodupKept hkey =>
        have hAllP : pruneAllNonP p branches = true :=
          prune_all_non_p_true_of_all_ne p branches (fun br hm => by
            obtain ⟨p', l', s', T0⟩ := br
            exact Ne.symm (hno p' l' s' T0 hm))
        obtain ⟨brK, hmemK⟩ := List.exists_mem_of_ne_nil kept hne.2
        obtain ⟨r, l, s, V'⟩ := brK
        obtain ⟨T0, hmem0⟩ := hkey r l s V' hmemK
        have hSub : mon_tr_yes_exist T0 (ext_tag.recv p lab S) V' :=
          hall T0 V' r l s hmem0 hmemK
        have hlt : sizeOf T0 < n := by
          have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice hmem0
          omega
        have hAd0 : PruneAdequate p lab S fuel T0 := by
          cases hAd with
          | intC hall_ad => exact hall_ad _ hmem0
        have hWFU : T0.WellFormed := wf_of_mem_intBranches_early hmem0 hWF
        have hVacU : T0.VacuousRec :=
          SessionType.VacuousRec.of_internalChoice hVac hmem0
        have hHasT0 : pruneFirstInputDeepHas p lab S T0 = true :=
          ih (sizeOf T0) hlt T0 (Nat.le_refl _) hAd0 hWFU hVacU V' hSub
        have hAny : pruneHasDeepIntAny p lab S branches = true :=
          prune_has_deep_int_any_true_of_mem p lab S branches _ _ _ _
            hHasT0 hmem0
        simp [pruneFirstInputDeepHas, hAllP, hAny]
    | externalChoice q branches =>
      by_cases hbeq : (q == p) = true
      · have hqp : q = p := beq_iff_eq.mp hbeq
        subst q
        cases hE with
        | base hb =>
          cases hb with
          | extC _ hmem =>
            have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
            simp only [pruneFirstInputDeepHas, hif, ite_true]
            rw [List.any_eq_true]
            exact ⟨_, hmem, by simp⟩
        | pfxExt hne hneq hkept hall hNodupKept hkey =>
          exact absurd rfl hneq
      · have hqp : q ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
        cases hE with
        | base hb =>
          cases hb with
          | extC _ _ =>
            simp at hbeq
        | @pfxExt _ _ kept _ _ _ _ hne hneq hkept hall hNodupKept hkey =>
          obtain ⟨brK, hmemK⟩ := List.exists_mem_of_ne_nil kept hne.2
          obtain ⟨l, s, V'⟩ := brK
          obtain ⟨T0, hmem0⟩ := hkey l s V' hmemK
          have hSub : mon_tr_yes_exist T0 (ext_tag.recv p lab S) V' :=
            hall T0 V' l s hmem0 hmemK
          have hlt : sizeOf T0 < n := by
            have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice (p := q)
              hmem0
            omega
          have hAd0 : PruneAdequate p lab S fuel T0 := by
            cases hAd with
            | extC hall_ad => exact hall_ad _ hmem0
          have hWFU : T0.WellFormed := wf_of_mem_extBranches_early hmem0 hWF
          have hVacU : T0.VacuousRec :=
            SessionType.VacuousRec.of_externalChoice hVac hmem0
          have hHasT0 : pruneFirstInputDeepHas p lab S T0 = true :=
            ih (sizeOf T0) hlt T0 (Nat.le_refl _) hAd0 hWFU hVacU V' hSub
          simp only [pruneFirstInputDeepHas, ite_eq_right hbeq]
          exact prune_has_deep_ext_true_of_mem p lab S _ _ _ hHasT0 _ hmem0



end SurvivalKeys

section MonitorYes

/-- Deep-filtered external branches keep a sublist of the
    `(label, sort)` pair keys. -/
private theorem prune_go_deep_ext_keys2_sublist (p : Role) (lab : Lab)
    (S : DataSort)
    (branches : List (Lab × DataSort × SessionType)) :
    List.Sublist
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        (pruneGoDeepExt p lab S fuel branches))
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
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


/-- Forward direction (adequate, balanced): deep prune computes a monitor
    yes-transition. Nested inductions: fuel outer (`trec_yes` consumes one
    fuel on unfolding, via `wellFormedUnfold`, `IsBalancedW_subst`,
    forward-`Has`, and `mon_tr_yes_unfold_lift`), size inner (branch targets
    shrink, adequacy from `hall` inversion); coverage uses the position
    lemma (`enc_exist_imp_deep_has_adequate`). -/
theorem mon_yes_prune_deep_mp (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (fuel : Nat), ∀ (n : Nat) (T T' : SessionType) (hVacT : T.VacuousRec),
    sizeOf T ≤ n → PruneAdequate p lab S fuel T → T.WellFormed →
    pruneFirstInputDeep T (QueueMessage.msg p lab S) fuel = some T' →
    mon_tr_yes T (ext_tag.recv p lab S) T' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihF =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihN =>
      intro T T' hVacT hsize hAd hWF hP
      cases T with
      | tEnd =>
        simp [pruneFirstInputDeep, pruneFirstInputDeepHas] at hP
      | tVar X =>
        have hCl : SessionType.IsClosed (SessionType.tVar X) := hWF.2.1
        simp [SessionType.IsClosed, SessionType.fv] at hCl
      | tRec X B =>
        have hHasT : pruneFirstInputDeepHas p lab S (SessionType.tRec X B) = true := by
          cases hB : pruneFirstInputDeepHas p lab S (SessionType.tRec X B) with
          | true => exact rfl
          | false =>
            simp [pruneFirstInputDeep, hB] at hP
        cases hAd with
        | @trec_yes f _ _ hHas hsub =>
          have hPV : pruneFirstInputDeep (SessionType.tRec X B)
              (QueueMessage.msg p lab S) (f + 1) =
              some (pruneFirstInputDeepGo p lab S (f + 1) (SessionType.tRec X B)) := by
            simp [pruneFirstInputDeep, hHasT]
          have hGoEq : pruneFirstInputDeepGo p lab S (f + 1) (SessionType.tRec X B) =
              pruneFirstInputDeepGo p lab S f
                (substSessionType B X (SessionType.tRec X B)) := by
            simp only [pruneFirstInputDeepGo, hHas, ite_true]
          have hTEq : pruneFirstInputDeepGo p lab S f
              (substSessionType B X (SessionType.tRec X B)) = T' := by
            have h1 : pruneFirstInputDeepGo p lab S (f + 1) (SessionType.tRec X B) = T' :=
              Option.some_inj.mp (hPV.symm.trans hP)
            rwa [hGoEq] at h1
          have hVacSub : (substSessionType B X (SessionType.tRec X B)).VacuousRec := by
            cases hVacT with
            | trec hfree hVacB =>
              rw [subst_noop B X _ hfree]
              exact hVacB
          have hWFsub : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
            SessionType.wellFormedUnfold hWF
              (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
          have hHasB : pruneFirstInputDeepHas p lab S B = true := by
            simpa [pruneFirstInputDeepHas] using hHasT
          have hHasSub : pruneFirstInputDeepHas p lab S
              (substSessionType B X (SessionType.tRec X B)) = true :=
            deep_has_subst_forward p lab S B (X := X)
              (R := SessionType.tRec X B) hHasB
          have hPsub : pruneFirstInputDeep (substSessionType B X (SessionType.tRec X B))
              (QueueMessage.msg p lab S) f = some T' := by
            simp [pruneFirstInputDeep, hHasSub, hTEq]
          have hYes : mon_tr_yes (substSessionType B X (SessionType.tRec X B))
              (ext_tag.recv p lab S) T' :=
            ihF f (Nat.lt_succ_self f) (sizeOf _) _ _ hVacSub (Nat.le_refl _) hsub
              hWFsub hPsub
          exact mon_tr_yes_unfold_lift
            (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _)) hYes
          | @trec_vac f _ _ hfree hsub =>
            have hSubEq : substSessionType B X (SessionType.tRec X B) = B :=
              subst_noop B X _ hfree
            have hPV : pruneFirstInputDeep (SessionType.tRec X B)
                (QueueMessage.msg p lab S) (f + 1) =
                some (pruneFirstInputDeepGo p lab S (f + 1) (SessionType.tRec X B)) := by
              simp [pruneFirstInputDeep, hHasT]
            have hGoEq : pruneFirstInputDeepGo p lab S (f + 1) (SessionType.tRec X B) =
                pruneFirstInputDeepGo p lab S f
                  (substSessionType B X (SessionType.tRec X B)) := by
              simp only [pruneFirstInputDeepGo, hHasT, ite_true]
            have hTEq : pruneFirstInputDeepGo p lab S f
                (substSessionType B X (SessionType.tRec X B)) = T' := by
              have h1 : pruneFirstInputDeepGo p lab S (f + 1) (SessionType.tRec X B) = T' :=
                Option.some_inj.mp (hPV.symm.trans hP)
              rwa [hGoEq] at h1
            have hVacSub : (substSessionType B X (SessionType.tRec X B)).VacuousRec := by
              cases hVacT with
              | trec hfree hVacB =>
                rw [subst_noop B X _ hfree]
                exact hVacB
            have hWFsub : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
              SessionType.wellFormedUnfold hWF
                (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
            have hHasB : pruneFirstInputDeepHas p lab S B = true := by
              simpa [pruneFirstInputDeepHas] using hHasT
            have hHasSub : pruneFirstInputDeepHas p lab S
                (substSessionType B X (SessionType.tRec X B)) = true :=
              deep_has_subst_forward p lab S B (X := X)
                (R := SessionType.tRec X B) hHasB
            have hPsub : pruneFirstInputDeep (substSessionType B X (SessionType.tRec X B))
                (QueueMessage.msg p lab S) f = some T' := by
              simp [pruneFirstInputDeep, hHasSub, hTEq]
            have hsub' : PruneAdequate p lab S f
                (substSessionType B X (SessionType.tRec X B)) := by
              rwa [← hSubEq] at hsub
            have hYes : mon_tr_yes (substSessionType B X (SessionType.tRec X B))
                (ext_tag.recv p lab S) T' :=
              ihF f (Nat.lt_succ_self f) (sizeOf _) _ _ hVacSub (Nat.le_refl _) hsub'
                hWFsub hPsub
            exact mon_tr_yes_unfold_lift
              (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _)) hYes
      | internalChoice branches =>
        have hHas : pruneFirstInputDeepHas p lab S
            (SessionType.internalChoice branches) = true := by
          cases hB : pruneFirstInputDeepHas p lab S
              (SessionType.internalChoice branches) with
          | true => exact rfl
          | false =>
            simp [pruneFirstInputDeep, hB] at hP
        have hPV : pruneFirstInputDeep (SessionType.internalChoice branches)
            (QueueMessage.msg p lab S) fuel =
            some (pruneFirstInputDeepGo p lab S fuel
              (SessionType.internalChoice branches)) := by
          simp [pruneFirstInputDeep, hHas]
        simp only [pruneFirstInputDeepHas] at hHas
        simp at hHas
        obtain ⟨hAllB, hAnyB⟩ := hHas
        have hAll : ∀ br ∈ branches, br.1 ≠ p :=
          prune_all_non_p_all_ne p branches hAllB
        obtain ⟨q0, l0, S0, U0, hmemW, hHasW⟩ :=
          prune_has_deep_int_any_exists p lab S branches hAnyB
        have hmemF : (q0, l0, S0, pruneFirstInputDeepGo p lab S fuel U0) ∈
            pruneGoDeepInt p lab S fuel branches :=
          prune_go_deep_int_map_mem p lab S fuel branches (q0, l0, S0, U0) hmemW hHasW
        have hneF : pruneGoDeepInt p lab S fuel branches ≠ [] :=
          List.ne_nil_of_mem hmemF
        have hGoEq : pruneFirstInputDeepGo p lab S fuel
            (SessionType.internalChoice branches) =
            SessionType.internalChoice (pruneGoDeepInt p lab S fuel branches) := by
          simp only [pruneFirstInputDeepGo]
        have hTEq : pruneFirstInputDeepGo p lab S fuel
            (SessionType.internalChoice branches) = T' :=
          Option.some_inj.mp (hPV.symm.trans hP)
        subst T'
        rw [hGoEq]
        have hneB : branches ≠ [] := by
          cases hWF.1 with
          | internalChoice _ h_ne _ => exact h_ne
        have hNDpair : (List.map
            (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
            branches).Nodup := by
          cases hWF.1 with
          | internalChoice h_nodup _ _ => exact h_nodup
        have hNDtriple : (List.map
            (fun x : Role × Lab × DataSort × SessionType =>
              (x.1, x.2.1, x.2.2.1)) branches).Nodup :=
          hWF.1.triple_nodup_of_internalChoice
        have hNodupKept : (List.map
            (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
            (pruneGoDeepInt p lab S fuel branches)).Nodup :=
          (prune_go_deep_int_keys_sublist p lab S fuel branches).nodup hNDpair
        -- Per-pair alignment: kept entries resolve to same-key sources.
        have hPair : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab)
            (s : DataSort), (r, l, s, T0) ∈ branches →
            (r, l, s, T1) ∈ pruneGoDeepInt p lab S fuel branches →
            ∃ U2, (r, l, s, U2) ∈ branches ∧ T0 = U2 ∧
              T1 = pruneFirstInputDeepGo p lab S fuel U2 ∧
              pruneFirstInputDeepHas p lab S U2 = true := by
          intro T0 T1 r l s hmemS hmemK
          obtain ⟨q2, l2, S2, U2, hmemU, hHasU, heq⟩ :=
            prune_go_deep_int_mem p lab S fuel branches (r, l, s, T1) hmemK
          have hr : r = q2 := congrArg (fun b :
            Role × Lab × DataSort × SessionType => b.1) heq
          have hl : l = l2 := congrArg (fun b :
            Role × Lab × DataSort × SessionType => b.2.1) heq
          have hs : s = S2 := congrArg (fun b :
            Role × Lab × DataSort × SessionType => b.2.2.1) heq
          subst hr
          subst hl
          subst hs
          have hTU : T0 = U2 := int_target_unique_norec hWF.1 hmemS hmemU
          have hT1 : T1 = pruneFirstInputDeepGo p lab S fuel U2 :=
            congrArg (fun b :
              Role × Lab × DataSort × SessionType => b.2.2.2) heq
          exact ⟨U2, hmemU, hTU, hT1, hHasU⟩
        -- Per-source-branch yes-transitions via the IH.
        have hBranch : ∀ (T0 : SessionType) (r : Role) (l : Lab)
            (s : DataSort), (r, l, s, T0) ∈ branches →
            pruneFirstInputDeepHas p lab S T0 = true →
            mon_tr_yes T0 (ext_tag.recv p lab S)
              (pruneFirstInputDeepGo p lab S fuel T0) := by
          intro T0 r l s hmemS hHasU
          have hltU : sizeOf T0 < n := by
            have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice hmemS
            omega
          have hAdU : PruneAdequate p lab S fuel T0 := by
            cases hAd with
            | intC hall_ad => exact hall_ad _ hmemS
          have hWFU : T0.WellFormed := wf_of_mem_intBranches_early hmemS hWF
          have hVacU : T0.VacuousRec :=
            SessionType.VacuousRec.of_internalChoice hVacT hmemS
          have hPrU : pruneFirstInputDeep T0 (QueueMessage.msg p lab S) fuel =
              some (pruneFirstInputDeepGo p lab S fuel T0) := by
            simp [pruneFirstInputDeep, hHasU]
          exact ihN (sizeOf T0) hltU T0 _ hVacU (Nat.le_refl _) hAdU hWFU hPrU
        have hHall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab)
            (s : DataSort), (r, l, s, T0) ∈ branches →
            (r, l, s, T1) ∈ pruneGoDeepInt p lab S fuel branches →
            mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1 := by
          intro T0 T1 r l s hmemS hmemK
          obtain ⟨U2, hmemU, hTU, hT1, hHasU⟩ :=
            hPair T0 T1 r l s hmemS hmemK
          rw [hTU, hT1]
          exact (hBranch U2 r l s hmemU hHasU).1
        have hHallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab)
            (s : DataSort) (hmemB : (r, l, s, T0) ∈ branches)
            (hmemK : (r, l, s, T1) ∈ pruneGoDeepInt p lab S fuel branches)
            (hsub : mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1),
            mon_tr_yes_max_deriv hsub := by
          intro T0 T1 r l s hmemS hmemK hsub
          obtain ⟨U2, hmemU, hTU, hT1, hHasU⟩ :=
            hPair T0 T1 r l s hmemS hmemK
          subst U2
          subst T1
          exact (hBranch T0 r l s hmemU hHasU).2
        have hcover : ∀ (r : Role) (l : Lab) (s : DataSort)
            (T0 : SessionType), (r, l, s, T0) ∈ branches →
            (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1) →
            ∃ T1, (r, l, s, T1) ∈ pruneGoDeepInt p lab S fuel branches := by
          intro r l s T0 hmemS hAcc
          obtain ⟨T1, hE⟩ := hAcc
          have hAdU : PruneAdequate p lab S fuel T0 := by
            cases hAd with
            | intC hall_ad => exact hall_ad _ hmemS
          have hWFU : T0.WellFormed := wf_of_mem_intBranches_early hmemS hWF
          have hVacU : T0.VacuousRec :=
            SessionType.VacuousRec.of_internalChoice hVacT hmemS
          have hHasU : pruneFirstInputDeepHas p lab S T0 = true :=
            enc_exist_imp_deep_has_adequate p lab S fuel (sizeOf T0) T0
              (Nat.le_refl _) hAdU hWFU hVacU T1 hE
          exact ⟨_, prune_go_deep_int_map_mem p lab S fuel branches (r, l, s, T0)
            hmemS hHasU⟩
        have horder : List.Sublist
            (List.map (fun x : Role × Lab × DataSort × SessionType =>
              (x.1, x.2.1, x.2.2.1)) (pruneGoDeepInt p lab S fuel branches))
            (List.map (fun x : Role × Lab × DataSort × SessionType =>
              (x.1, x.2.1, x.2.2.1)) branches) :=
          prune_go_deep_int_keys3_sublist p lab S fuel branches
        have hkey : ∀ (r : Role) (l : Lab) (s : DataSort)
            (T1 : SessionType),
            (r, l, s, T1) ∈ pruneGoDeepInt p lab S fuel branches →
            ∃ T0, (r, l, s, T0) ∈ branches := by
          intro r l s T1 hmemK
          obtain ⟨q2, l2, S2, U2, hmemU, _, heq⟩ :=
            prune_go_deep_int_mem p lab S fuel branches (r, l, s, T1) hmemK
          have hr : r = q2 := congrArg (fun b :
            Role × Lab × DataSort × SessionType => b.1) heq
          have hl : l = l2 := congrArg (fun b :
            Role × Lab × DataSort × SessionType => b.2.1) heq
          have hs : s = S2 := congrArg (fun b :
            Role × Lab × DataSort × SessionType => b.2.2.1) heq
          subst hr
          subst hl
          subst hs
          exact ⟨U2, hmemU⟩
        have hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort)
            (T0 : SessionType), (p', lab', S', T0) ∈ branches → p ≠ p' := by
          intro p' lab' S' T0 hm
          exact Ne.symm (hAll _ hm)
        have hE : mon_tr_yes_exist (SessionType.internalChoice branches)
            (ext_tag.recv p lab S)
            (SessionType.internalChoice
              (pruneGoDeepInt p lab S fuel branches)) :=
          mon_tr_yes_exist.pfxInt ⟨hneB, hneF⟩ hno rfl hHall
            hNodupKept hkey
        exact ⟨hE, mon_tr_yes_max_deriv.pfxInt (hne := ⟨hneB, hneF⟩)
          (hno := hno) (hkept := rfl) (hall := hHall)
          (hNodupKept := hNodupKept) (hkey := hkey) hHallMax hcover horder⟩
      | externalChoice q branches =>
        by_cases hbeq : (q == p) = true
        · -- Same owner: direct offer = base rule.
          have hqp : q = p := beq_iff_eq.mp hbeq
          subst q
          have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
          simp only [pruneFirstInputDeep, pruneFirstInputDeepHas, hif,
            ite_true] at hP
          simp only [pruneFirstInputDeepGo, hif, ite_true] at hP
          by_cases hAny : branches.any (fun b => match b with
              | (l, S', _) => l == lab && S' == S) = true
          · rw [ite_eq_left hAny] at hP
            refine match hF : branches.find? (fun b => match b with
                | (l, S', _) => l == lab && S' == S) with
            | none => ?_
            | some v => ?_
            · rw [List.any_eq_true] at hAny
              obtain ⟨v, hmemV, hpredV⟩ := hAny
              exact ((List.find?_eq_none.mp hF) _ hmemV hpredV).elim
            · obtain ⟨l, S', U⟩ := v
              obtain ⟨hmemV, hpredV⟩ := find?_some_mem hF
              have hkeys : l = lab ∧ S' = S := by
                have h1 : ((l == lab) && (S' == S)) = true := by
                  simpa using hpredV
                simp at h1
                exact h1
              obtain ⟨hlEq, hSEq⟩ := hkeys
              subst l
              subst S'
              simp only [hF] at hP
              have hVU : U = T' := Option.some_inj.mp hP
              rw [←hVU]
              have hNDlabel : (List.map
                  (fun x : Lab × DataSort × SessionType => x.1)
                  branches).Nodup := by
                cases hWF.1 with
                | externalChoice h_nodup _ _ => exact h_nodup
              have hNDpair :=
                extPair_nodup_of_label_nodup branches hNDlabel
              have hb : mon_tr_yes_base (SessionType.externalChoice p branches)
                  (ext_tag.recv p lab S) U :=
                mon_tr_yes_base.extC hNDpair hmemV
              exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩
          · rw [ite_eq_right hAny] at hP
            cases hP
        · -- Different owner: prefix rule over kept branches.
          have hqp : q ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
          have hHas : pruneFirstInputDeepHas p lab S
              (SessionType.externalChoice q branches) = true := by
            cases hB : pruneFirstInputDeepHas p lab S
                (SessionType.externalChoice q branches) with
            | true => exact rfl
            | false =>
              simp [pruneFirstInputDeep, hB] at hP
          have hPV : pruneFirstInputDeep (SessionType.externalChoice q
              branches) (QueueMessage.msg p lab S) fuel =
              some (pruneFirstInputDeepGo p lab S fuel
                (SessionType.externalChoice q branches)) := by
            simp [pruneFirstInputDeep, hHas]
          have hTEq : pruneFirstInputDeepGo p lab S fuel
              (SessionType.externalChoice q branches) = T' :=
            Option.some_inj.mp (hPV.symm.trans hP)
          subst T'
          simp only [pruneFirstInputDeepHas, ite_eq_right hbeq] at hHas
          obtain ⟨l0, s0, U0, hmemW, hHasW⟩ :=
            prune_has_deep_ext_exists p lab S branches hHas
          have hmemF : (l0, s0, pruneFirstInputDeepGo p lab S fuel U0) ∈
              pruneGoDeepExt p lab S fuel branches :=
            prune_go_deep_ext_map_mem p lab S fuel branches (l0, s0, U0) hmemW hHasW
          have hneF : pruneGoDeepExt p lab S fuel branches ≠ [] :=
            List.ne_nil_of_mem hmemF
          have hGoEq : pruneFirstInputDeepGo p lab S fuel
              (SessionType.externalChoice q branches) =
              SessionType.externalChoice q
                (pruneGoDeepExt p lab S fuel branches) := by
            simp only [pruneFirstInputDeepGo, ite_eq_right hbeq]
          rw [hGoEq]
          have hneB : branches ≠ [] := by
            cases hWF.1 with
            | externalChoice _ h_ne _ => exact h_ne
          have hNDlabel : (List.map
              (fun x : Lab × DataSort × SessionType => x.1)
              branches).Nodup := by
            cases hWF.1 with
            | externalChoice h_nodup _ _ => exact h_nodup
          have hNodupKept : (List.map
              (fun x : Lab × DataSort × SessionType => x.1)
              (pruneGoDeepExt p lab S fuel branches)).Nodup :=
            (prune_go_deep_ext_keys_sublist p lab S fuel branches).nodup hNDlabel
          -- Per-pair alignment: kept entries resolve to same-key sources.
          have hPair : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
              (l, s, T0) ∈ branches →
              (l, s, T1) ∈ pruneGoDeepExt p lab S fuel branches →
              ∃ U2, (l, s, U2) ∈ branches ∧ T0 = U2 ∧
                T1 = pruneFirstInputDeepGo p lab S fuel U2 ∧
                pruneFirstInputDeepHas p lab S U2 = true := by
            intro T0 T1 l s hmemS hmemK
            obtain ⟨l2, S2, U2, hmemU, hHasU, heq⟩ :=
              prune_go_deep_ext_mem p lab S fuel branches (l, s, T1) hmemK
            have hl : l = l2 := congrArg (fun b :
              Lab × DataSort × SessionType => b.1) heq
            have hs : s = S2 := congrArg (fun b :
              Lab × DataSort × SessionType => b.2.1) heq
            subst hl
            subst hs
            have hTU : T0 = U2 := ext_target_unique_norec hWF.1 hmemS hmemU
            have hT1 : T1 = pruneFirstInputDeepGo p lab S fuel U2 :=
              congrArg (fun b :
              Lab × DataSort × SessionType => b.2.2) heq
            exact ⟨U2, hmemU, hTU, hT1, hHasU⟩
          -- Per-source-branch yes-transitions via the IH.
          have hBranch : ∀ (T0 : SessionType) (l : Lab) (s : DataSort),
              (l, s, T0) ∈ branches →
              pruneFirstInputDeepHas p lab S T0 = true →
              mon_tr_yes T0 (ext_tag.recv p lab S)
                (pruneFirstInputDeepGo p lab S fuel T0) := by
            intro T0 l s hmemS hHasU
            have hltU : sizeOf T0 < n := by
              have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice (p := q)
                hmemS
              omega
            have hAdU : PruneAdequate p lab S fuel T0 := by
              cases hAd with
              | extC hall_ad => exact hall_ad _ hmemS
            have hWFU : T0.WellFormed :=
              wf_of_mem_extBranches_early hmemS hWF
            have hVacU : T0.VacuousRec :=
              SessionType.VacuousRec.of_externalChoice hVacT hmemS
            have hPrU : pruneFirstInputDeep T0 (QueueMessage.msg p lab S) fuel =
                some (pruneFirstInputDeepGo p lab S fuel T0) := by
              simp [pruneFirstInputDeep, hHasU]
            exact ihN (sizeOf T0) hltU T0 _ hVacU (Nat.le_refl _) hAdU hWFU hPrU
          have hHall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
              (l, s, T0) ∈ branches →
              (l, s, T1) ∈ pruneGoDeepExt p lab S fuel branches →
              mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1 := by
            intro T0 T1 l s hmemS hmemK
            obtain ⟨U2, hmemU, hTU, hT1, hHasU⟩ :=
              hPair T0 T1 l s hmemS hmemK
            rw [hTU, hT1]
            exact (hBranch U2 l s hmemU hHasU).1
          have hHallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
              (hmemB : (l, s, T0) ∈ branches)
              (hmemK : (l, s, T1) ∈ pruneGoDeepExt p lab S fuel branches)
              (hsub : mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1),
              mon_tr_yes_max_deriv hsub := by
            intro T0 T1 l s hmemS hmemK hsub
            obtain ⟨U2, hmemU, hTU, hT1, hHasU⟩ :=
              hPair T0 T1 l s hmemS hmemK
            subst U2
            subst T1
            exact (hBranch T0 l s hmemU hHasU).2
          have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
              (l, s, T0) ∈ branches →
              (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1) →
              ∃ T1, (l, s, T1) ∈ pruneGoDeepExt p lab S fuel branches := by
            intro l s T0 hmemS hAcc
            obtain ⟨T1, hE⟩ := hAcc
            have hAdU : PruneAdequate p lab S fuel T0 := by
              cases hAd with
              | extC hall_ad => exact hall_ad _ hmemS
            have hWFU : T0.WellFormed := wf_of_mem_extBranches_early hmemS hWF
            have hVacU : T0.VacuousRec :=
              SessionType.VacuousRec.of_externalChoice hVacT hmemS
            have hHasU : pruneFirstInputDeepHas p lab S T0 = true :=
              enc_exist_imp_deep_has_adequate p lab S fuel (sizeOf T0) T0
                (Nat.le_refl _) hAdU hWFU hVacU T1 hE
            exact ⟨_, prune_go_deep_ext_map_mem p lab S fuel branches (l, s, T0)
              hmemS hHasU⟩
          have horder : List.Sublist
              (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
                (pruneGoDeepExt p lab S fuel branches))
              (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
                branches) :=
            prune_go_deep_ext_keys2_sublist p lab S branches
          have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
              (l, s, T1) ∈ pruneGoDeepExt p lab S fuel branches →
              ∃ T0, (l, s, T0) ∈ branches := by
            intro l s T1 hmemK
            obtain ⟨l2, S2, U2, hmemU, _, heq⟩ :=
              prune_go_deep_ext_mem p lab S fuel branches (l, s, T1) hmemK
            have hl : l = l2 := congrArg (fun b :
              Lab × DataSort × SessionType => b.1) heq
            have hs : s = S2 := congrArg (fun b :
              Lab × DataSort × SessionType => b.2.1) heq
            subst hl
            subst hs
            exact ⟨U2, hmemU⟩
          have hneq : p ≠ q := Ne.symm hqp
          have hE : mon_tr_yes_exist (SessionType.externalChoice q branches)
              (ext_tag.recv p lab S)
              (SessionType.externalChoice q
                (pruneGoDeepExt p lab S fuel branches)) :=
            mon_tr_yes_exist.pfxExt ⟨hneB, hneF⟩ hneq rfl hHall
              hNodupKept hkey
          exact ⟨hE, mon_tr_yes_max_deriv.pfxExt (hne := ⟨hneB, hneF⟩)
            (hneq := hneq) (hkept := rfl) (hall := hHall)
            (hNodupKept := hNodupKept) (hkey := hkey) hHallMax hcover
            horder⟩


/-- Backward direction (adequate, balanced): a monitor yes-transition is
    computed by deep prune. No induction needed: the position lemma
    (`enc_exist_imp_deep_has_adequate`) gives definedness, `mp` gives a
    yes-transition to the pruned target, and `mon_tr_yes_target_unique`
    identifies it with the given one. -/
theorem mon_yes_prune_deep_mpr (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (fuel : Nat) (T T' : SessionType) (hVacT : T.VacuousRec),
    T.WellFormed → PruneAdequate p lab S fuel T →
    mon_tr_yes T (ext_tag.recv p lab S) T' →
    pruneFirstInputDeep T (QueueMessage.msg p lab S) fuel = some T' := by
  intro fuel T T' hVacT hWF hAd hYes
  have hE : mon_tr_yes_exist T (ext_tag.recv p lab S) T' := hYes.1
  have hHasT : pruneFirstInputDeepHas p lab S T = true :=
    enc_exist_imp_deep_has_adequate p lab S fuel (sizeOf T) T (Nat.le_refl _) hAd
      hWF hVacT _ hE
  have hPV : pruneFirstInputDeep T (QueueMessage.msg p lab S) fuel =
      some (pruneFirstInputDeepGo p lab S fuel T) := by
    simp [pruneFirstInputDeep, hHasT]
  have hMP : mon_tr_yes T (ext_tag.recv p lab S)
      (pruneFirstInputDeepGo p lab S fuel T) :=
    mon_yes_prune_deep_mp p lab S fuel (sizeOf T) T _ hVacT (Nat.le_refl _) hAd
      hWF hPV
  have hUq : pruneFirstInputDeepGo p lab S fuel T = T' :=
    mon_tr_yes_target_unique hWF hMP hYes
  rw [hPV, hUq]


/-- Deep-prune transformation preserves vacuous recursion. Nested
    inductions (fuel outer, size inner — the `mp` pattern): `tRec`
    unfolds with fuel descent (`trec_yes` supplies the smaller-fuel
    adequate subst; vacuousness makes it `subst_noop`, so the count
    drops); choice arms map branch targets (adequacy + vacuousness from
    inversions); the same-owner `extC` arm returns a branch target
    verbatim. No `WellFormed` needed (nothing inspects closedness). -/
theorem prune_first_input_deep_go_preserves_vacuous_rec (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (fuel : Nat) (n : Nat) (T : SessionType),
    sizeOf T ≤ n → PruneAdequate p lab S fuel T → T.VacuousRec →
    (pruneFirstInputDeepGo p lab S fuel T).VacuousRec := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihF =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihN =>
      intro T hsize hAd hVac
      cases T with
      | tEnd =>
        simp only [pruneFirstInputDeepGo]
        exact SessionType.VacuousRec.end
      | tVar X =>
        simp only [pruneFirstInputDeepGo]
        exact SessionType.VacuousRec.tvar X
      | tRec X B =>
        cases hAd with
        | @trec_yes f _ _ hHas hsub =>
          have hGoEq : pruneFirstInputDeepGo p lab S (f + 1)
              (SessionType.tRec X B) =
              pruneFirstInputDeepGo p lab S f
                (substSessionType B X (SessionType.tRec X B)) := by
            simp only [pruneFirstInputDeepGo, hHas, ite_true]
          rw [hGoEq]
          have hfree : X ∉ B.fv := by
            cases hVac with
            | trec hfree _ => exact hfree
          have hVacB : B.VacuousRec := by
            cases hVac with
            | trec _ hVacB => exact hVacB
          have hVacSub : (substSessionType B X
              (SessionType.tRec X B)).VacuousRec := by
            rw [subst_noop B X _ hfree]
            exact hVacB
          exact ihF f (Nat.lt_succ_self f) (sizeOf _) _
            (Nat.le_refl _) hsub hVacSub
        | @trec_vac f _ _ hfree hsub =>
          have hSubEq : substSessionType B X (SessionType.tRec X B) = B :=
            subst_noop B X _ hfree
          have hGoEq : pruneFirstInputDeepGo p lab S (f + 1)
              (SessionType.tRec X B) =
              pruneFirstInputDeepGo p lab S f B := by
            by_cases hHasT : pruneFirstInputDeepHas p lab S
                (SessionType.tRec X B) = true
            · simp only [pruneFirstInputDeepGo, hHasT, ite_true, hSubEq]
            · simp only [pruneFirstInputDeepGo]
              rw [ite_eq_right hHasT, ite_eq_right hfree]
          rw [hGoEq]
          have hVacB : B.VacuousRec := by
            cases hVac with
            | trec _ hVacB => exact hVacB
          exact ihF f (Nat.lt_succ_self f) (sizeOf _) _
            (Nat.le_refl _) hsub hVacB
      | internalChoice branches =>
        simp only [pruneFirstInputDeepGo]
        cases hF : pruneGoDeepInt p lab S fuel branches with
        | nil =>
          simp only [hF]
          exact SessionType.VacuousRec.end
        | cons hd tl =>
          simp only [hF]
          apply SessionType.VacuousRec.internalChoice
          intro x hmem
          have hmem' : x ∈ pruneGoDeepInt p lab S fuel branches := by
            rw [hF]
            exact hmem
          obtain ⟨q, l, S', U, hmemU, _, rfl⟩ :=
            prune_go_deep_int_mem p lab S fuel branches x hmem'
          have hltU : sizeOf U < n := by
            have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice hmemU
            omega
          have hAdU : PruneAdequate p lab S fuel U := by
            cases hAd with
            | intC hall_ad => exact hall_ad _ hmemU
          have hVacU : U.VacuousRec :=
            SessionType.VacuousRec.of_internalChoice hVac hmemU
          exact ihN (sizeOf U) hltU U (Nat.le_refl _) hAdU hVacU
      | externalChoice q branches =>
        by_cases hbeq : (q == p) = true
        · have hqp : q = p := beq_iff_eq.mp hbeq
          subst q
          simp only [pruneFirstInputDeepGo, hbeq, ite_true]
          refine match hF : branches.find? (fun b => match b with
              | (l, S', _) => l == lab && S' == S) with
          | none => ?_
          | some v => ?_
          · simp only [hF]
            exact SessionType.VacuousRec.end
          · obtain ⟨l, S', U⟩ := v
            obtain ⟨hmemU, -⟩ := find?_some_mem hF
            simp only [hF]
            exact SessionType.VacuousRec.of_externalChoice hVac hmemU
        · have hqp : q ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
          simp only [pruneFirstInputDeepGo, hbeq]
          cases hF : pruneGoDeepExt p lab S fuel branches with
          | nil =>
            simp only [hF]
            exact SessionType.VacuousRec.end
          | cons hd tl =>
            simp only [hF]
            apply SessionType.VacuousRec.externalChoice
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
            have hAdU : PruneAdequate p lab S fuel U := by
              cases hAd with
              | extC hall_ad => exact hall_ad _ hmemU
            have hVacU : U.VacuousRec :=
              SessionType.VacuousRec.of_externalChoice hVac hmemU
            exact ihN (sizeOf U) hltU U (Nat.le_refl _) hAdU hVacU


/-- Prepend a dequeue step onto a `Cannot` witness at an `extC` head:
    head closures are vacuous-or-refuted (intC by clash, `extC`
    absence refuted by the dequeued message); prefix dequeues
    coincide. -/
theorem cannot_prepend_dequeue_at_extC {p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Q Q1 : Queue}
    {T1 : SessionType} {labW : Lab} {SW : DataSort}
    (hND : (SessionType.externalChoice p branches).NoDupl)
    (hmemW : (labW, SW, T1) ∈ branches)
    (hQdW : Q.dequeue (QueueMessage.msg p labW SW) = some Q1)
    (hTailC : CannotAlwaysDrainInternalDeep T1 Q1) :
    CannotAlwaysDrainInternalDeep (SessionType.externalChoice p branches) Q := by
  obtain ⟨Tn, Qn, ρ', hTr, hne, hend, hallT⟩ := hTailC
  have hpmem : QueueMessage.msg p labW SW ∈ Q := by
    obtain ⟨seenW, leftW, hQeqW, -, -⟩ := queue_dequeue_some_iff hQdW
    rw [hQeqW]
    simp
  have hm1 : (QueueMessage.msg p labW SW).1 = p := rfl
  refine ⟨Tn, Qn, st_label.inp p labW SW :: ρ',
    over_trans_trace.step (over_trans.dequeue rfl hmemW hQdW) hTr, hne, hend, ?_⟩
  intro Ti Qi σ1 σ2 g1 g2 geq
  cases σ1 with
  | nil =>
    have hST := overTrTrace_nil_eq g1
    cases hST
    refine ⟨?_, ?_⟩
    · intro branches2 hEq hneB hfire
      cases hEq
    · intro q branches2 hEq hneB habs br hmem
      cases hEq
      exact (habs _ hpmem rfl).elim
  | cons α σ1' =>
    cases g1 with
    | step hS hT2 =>
      obtain ⟨T', Q', lab, S, hEqA, hEqS, hST, hQd⟩ :=
        extC_step_is_dequeue hpmem hm1 hS
      subst hEqS
      rw [List.cons_append] at geq
      cases geq
      cases hEqA
      cases hST with
      | extC hmem =>
        have hT : T1 = T' := ext_target_unique_norec hND hmemW hmem
        have hQ : Q1 = Q' :=
          Option.some_inj.mp (hQdW.symm.trans hQd)
        subst hT
        subst hQ
        exact hallT Ti Qi σ1' σ2 hT2 g2 rfl



end MonitorYes

section CannotPrepend

/-- Prepend a spec step onto a `Cannot` witness at an `extC` head:
    prefix specs coincide; all branches are bad. -/
theorem cannot_prepend_spec_at_extC {p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Q : Queue}
    {T1 : SessionType} {labW : Lab} {SW : DataSort}
    (hND : (SessionType.externalChoice p branches).NoDupl)
    (hmemW : (labW, SW, T1) ∈ branches)
    (hAbsW : ∀ m ∈ Q, m.1 ≠ p)
    (hTailC : CannotAlwaysDrainInternalDeep T1 Q)
    (hAllBad : ∀ (br : Lab × DataSort × SessionType), br ∈ branches →
      CannotAlwaysDrainInternalDeepCore br.2.2 Q) :
    CannotAlwaysDrainInternalDeep (SessionType.externalChoice p branches) Q := by
  obtain ⟨Tn, Qn, ρ', hTr, hne, hend, hallT⟩ := hTailC
  refine ⟨Tn, Qn, st_label.inp p labW SW :: ρ',
    over_trans_trace.step (over_trans.specInp rfl hmemW hAbsW) hTr, hne, hend, ?_⟩
  intro Ti Qi σ1 σ2 g1 g2 geq
  cases σ1 with
  | nil =>
    have hST := overTrTrace_nil_eq g1
    cases hST
    refine ⟨?_, ?_⟩
    · intro branches2 hEq hneB hfire
      cases hEq
    · intro q branches2 hEq hneB habs br hmem
      cases hEq
      exact hAllBad br hmem
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


/-- Prepend a send step onto a `Cannot` witness at an `intC` head:
    prefix sends coincide; the chosen branch is bad. -/
theorem cannot_prepend_send_at_intC
    {branches : List (Role × Lab × DataSort × SessionType)} {Q : Queue}
    {T1 : SessionType} {p0 : Role} {lp0 : Lab} {Sp0 : DataSort}
    (hND : (SessionType.internalChoice branches).NoDupl)
    (hmemW : (p0, lp0, Sp0, T1) ∈ branches)
    (hFreshW : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
      (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r')
    (hTailC : CannotAlwaysDrainInternalDeep T1 Q)
    (hCoreB : CannotAlwaysDrainInternalDeepCore T1 Q) :
    CannotAlwaysDrainInternalDeep (SessionType.internalChoice branches) Q := by
  obtain ⟨Tn, Qn, ρ', hTr, hne, hend, hallT⟩ := hTailC
  have hSend : over_trans (SessionType.internalChoice branches, Q)
      (st_label.out p0 lp0 Sp0) (T1, Q) :=
    over_trans.sendFresh rfl (st_trans.intC hmemW) hFreshW
  refine ⟨Tn, Qn, st_label.out p0 lp0 Sp0 :: ρ',
    over_trans_trace.step hSend hTr, hne, hend, ?_⟩
  intro Ti Qi σ1 σ2 g1 g2 geq
  cases σ1 with
  | nil =>
    have hST := overTrTrace_nil_eq g1
    cases hST
    refine ⟨?_, ?_⟩
    · intro branches2 hEq hneB hfire
      cases hEq
      exact ⟨(p0, lp0, Sp0, T1), hmemW, hCoreB⟩
    · intro q branches2 hEq hneB habs br hmem
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

end CannotPrepend

