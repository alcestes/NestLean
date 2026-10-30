import Nest.SessionUtils
import Nest.MonitorToolkit

/-!
# DequeueCorrespondence: dequeue correspondence in both directions.

Full queue absorption (`habs_full`: dequeues preserve fold endpoints along
`UnfoldStar` chains) plus the dequeue reflection pair
(`mon_dequeue_network_dequeue`, `network_dequeue_mon_dequeue`): a network
`τ_dequeue` is matched by the instrumented network and vice versa, preserving
consistent instrumentation. Feeds `monitor_soundness` with both dequeue
directions discharged.
-/

section MonitorSoundDequeue

/-- `dequeue.go` inversion: a successful dequeue splits the remaining
    list at the matched message (skipped prefix is sender-foreign,
    result is prefix ++ rest). By induction on `left`, generalizing
    the `seen` accumulator. -/
theorem dequeue_go_split (seen left : Queue) (msg : QueueMessage) (Q' : Queue)
    (h : Queue.dequeue.go seen left msg = some Q') :
    ∃ sk rest, left = sk ++ [msg] ++ rest ∧ Q' = seen ++ sk ++ rest ∧
      ∀ m ∈ sk, m.1 ≠ msg.1 := by
  induction left generalizing seen with
  | nil =>
    simp [Queue.dequeue.go] at h
  | cons m left' ih =>
    simp only [Queue.dequeue.go] at h
    by_cases hmm : m = msg
    · rw [hmm] at h
      rw [ite_eq_left rfl] at h
      obtain rfl := Option.some_inj.mp h
      exact ⟨[], left', by simp [hmm], by simp, fun m hm => by simp at hm⟩
    · simp only [ite_eq_right hmm] at h
      by_cases h1 : m.1 = msg.1
      · simp only [ite_eq_left h1] at h
        cases h
      · simp only [ite_eq_right h1] at h
        obtain ⟨sk, rest, hleft, hQ', hfresh⟩ := ih _ h
        refine ⟨m :: sk, rest, by simp [hleft], by simp [hQ', List.append_assoc], ?_⟩
        intro m' hm'
        simp only [List.mem_cons] at hm'
        rcases hm' with rfl | hm''
        · exact h1
        · exact hfresh _ hm''

/-- Dequeue (top-level) splits at the matched message. -/
theorem dequeue_split {Q : Queue} {msg : QueueMessage} {Q' : Queue}
    (h : Q.dequeue msg = some Q') :
    ∃ seen left, Q = seen ++ [msg] ++ left ∧ Q' = seen ++ left ∧
      ∀ m ∈ seen, m.1 ≠ msg.1 := by
  obtain ⟨sk, rest, hleft, hQ', hfresh⟩ := dequeue_go_split [] Q msg Q' h
  exact ⟨sk, rest, by simpa using hleft, by simpa using hQ', hfresh⟩

/-- Dequeue-scan key backpropagation: a maximal receive-sequence over a
    `p`-fresh tail that ends accepting `(lab, S)` at `p` yields a
    `(lab, S)`-branch in `K`. Induction on the tail; on-role base steps
    are impossible by freshness, off-role steps delegate with
    well-formedness preserved. -/
theorem dequeue_scan_key_backprop {K : List (Lab × DataSort × SessionType)}
    {rest : Queue} {U1' U2' : SessionType}
    {p : Role} {lab : Lab} {S : DataSort}
    (hKWF : (SessionType.externalChoice p K).WellFormed)
    (hfresh : ∀ m ∈ rest, m.1 ≠ p)
    (hSeq : mon_yes_seq (SessionType.externalChoice p K)
      (rest.map fun m => match m with
        | QueueMessage.msg p lab S => ext_tag.recv p lab S) U1')
    (hGam : mon_tr_yes U1' (ext_tag.recv p lab S) U2') :
    ∃ T2', (lab, S, T2') ∈ K := by
  induction rest generalizing K U1' U2' with
  | nil =>
    cases hSeq with
    | refl =>
      rcases hGam with ⟨hE, _⟩
      cases hE with
      | base hb =>
        cases hb with
        | extC _ hmem => exact ⟨_, hmem⟩
      | pfxExt _ hneq _ _ _ _ => exact absurd rfl hneq
  | cons m rest ih =>
    rcases m with ⟨q_i, l_i, s_i⟩
    have hqi : q_i ≠ p := hfresh _ (List.mem_cons.mpr (Or.inl rfl))
    have hfresh' : ∀ m ∈ rest, m.1 ≠ p := by
      intro m hm
      exact hfresh m (List.mem_cons.mpr (Or.inr hm))
    simp only [List.map_cons] at hSeq
    cases hSeq with
    | step hYi hTi =>
      have hYi' := hYi
      rcases hYi with ⟨hE, _⟩
      cases hE with
      | base hb =>
        cases hb with
        | extC _ _ => exact absurd rfl hqi
      | pfxExt _ _ hkept _ _ hkey =>
        subst hkept
        obtain hX1WF := mon_tr_yes_preserves_wf hYi' hKWF
        obtain ⟨T2', hmemK1⟩ := ih hX1WF hfresh' hTi hGam
        rcases hkey lab S T2' hmemK1 with ⟨T0, hmemK⟩
        exact ⟨T0, hmemK⟩

end MonitorSoundDequeue

section MonitorSoundAbsorb

/-- Absorption transfer across a dequeue scan at head-normal types
    (WellFormed-only): if `seen ++ [msg] ++ left` (with `seen`
    `p`-fresh) absorbs from `T` to `M`, and the session fires
    `inp p lab S` to `T'`, then `seen ++ left` absorbs from `T'`.
    Prefix induction with maximal-derivation splitting and hall
    rebuilding; the nil case is banked head absorption. -/
theorem absorb_transfer_headnormal {seen : Queue} {T T' M : SessionType}
    {p : Role} {lab : Lab} {S : DataSort} {left : Queue}
    (hWF : T.WellFormed)
    (hNF : IsHeadNF T)
    (hfresh : ∀ m ∈ seen, m.1 ≠ p)
    (hST : st_trans T (st_label.inp p lab S) T')
    (hEnc : monitor_fold (T, seen ++ [QueueMessage.msg p lab S] ++ left) M) :
    monitor_fold (T', seen ++ left) M := by
  induction seen generalizing T T' M left hWF hNF hST with
  | nil => exact dequeue_head_preserves_absorption hWF hEnc hST
  | cons m0 rest ih =>
    rcases m0 with ⟨q0, l0, s0⟩
    have hq0 : q0 ≠ p := hfresh _ (List.mem_cons.mpr (Or.inl rfl))
    have hfresh' : ∀ m ∈ rest, m.1 ≠ p := by
      intro m hm
      exact hfresh m (List.mem_cons.mpr (Or.inr hm))
    have hSeqFull : mon_yes_seq T
        ((ext_tag.recv q0 l0 s0) ::
          ((rest.map fun m => match m with
            | QueueMessage.msg p lab S => ext_tag.recv p lab S) ++
          (ext_tag.recv p lab S) ::
          (left.map fun m => match m with
            | QueueMessage.msg p lab S => ext_tag.recv p lab S))) M := by
      have h := monitor_fold_aux_to_mon_yes_seq hEnc
      simpa [List.map_append] using h
    obtain ⟨W, hY0seq, hTailW⟩ := mon_yes_seq_split
      (ρ1 := [ext_tag.recv q0 l0 s0])
      (ρ2 := (rest.map fun m => match m with
        | QueueMessage.msg p lab S => ext_tag.recv p lab S) ++
      (ext_tag.recv p lab S) ::
      (left.map fun m => match m with
        | QueueMessage.msg p lab S => ext_tag.recv p lab S)) hSeqFull
    cases hY0seq with
    | step hY0 hRest =>
      cases hRest with
      | refl =>
        have hY0' := hY0
        cases hST with
        | extC hmemST =>
          rcases hY0 with ⟨hE0, hM0⟩
          cases hM0 with
          | base =>
            rename_i hb
            cases hb with
            | extC _ _ => exact absurd rfl hq0
          | @pfxExt _ _ kept _ _ _ _ _ _ hkept hall _ _ hallMax _ _ =>
            subst hkept
            have hTailW2 : mon_yes_seq (SessionType.externalChoice p kept)
                ((rest.map fun m => match m with
                  | QueueMessage.msg p lab S => ext_tag.recv p lab S) ++
                (ext_tag.recv p lab S) ::
                (left.map fun m => match m with
                  | QueueMessage.msg p lab S => ext_tag.recv p lab S)) M := by
              simpa [List.map_append] using hTailW
            obtain ⟨U1', hSeqRest, hTailGam⟩ := mon_yes_seq_split
              (ρ1 := rest.map fun m => match m with
                | QueueMessage.msg p lab S => ext_tag.recv p lab S)
              (ρ2 := (ext_tag.recv p lab S) ::
              (left.map fun m => match m with
                | QueueMessage.msg p lab S => ext_tag.recv p lab S)) hTailW2
            cases hTailGam with
            | step hGam hTailLeft =>
              have hWWF : (SessionType.externalChoice p kept).WellFormed :=
                mon_tr_yes_preserves_wf hY0' hWF
              rcases dequeue_scan_key_backprop hWWF
                hfresh' hSeqRest hGam with ⟨Wstar, hmemK⟩
              have hsubE := hall T' Wstar lab S hmemST hmemK
              have hsubM := hallMax T' Wstar lab S hmemST hmemK hsubE
              have hSTW : st_trans (SessionType.externalChoice p kept)
                  (st_label.inp p lab S) Wstar := st_trans.extC hmemK
              have hYW' : mon_tr_yes T' (ext_tag.recv q0 l0 s0) Wstar := ⟨hsubE, hsubM⟩
              have hEncW : monitor_fold ((SessionType.externalChoice p kept),
                  rest ++ [QueueMessage.msg p lab S] ++ left) M := by
                have h : mon_yes_seq (SessionType.externalChoice p kept)
                    ((rest ++ [QueueMessage.msg p lab S] ++ left).map fun m =>
                      match m with
                      | QueueMessage.msg p lab S => ext_tag.recv p lab S) M := by
                  simpa [List.map_append] using hTailW2
                exact mon_yes_seq_to_monitor_fold_aux h
              have hTail : monitor_fold (Wstar, rest ++ left) M :=
                ih hWWF trivial hfresh' hSTW hEncW
              have hTailSeq : mon_yes_seq Wstar
                  ((rest ++ left).map fun m => match m with
                    | QueueMessage.msg p lab S => ext_tag.recv p lab S) M :=
                monitor_fold_aux_to_mon_yes_seq hTail
              have hGoalSeq : mon_yes_seq T'
                  (([QueueMessage.msg q0 l0 s0] ++ rest ++ left).map fun m =>
                    match m with
                    | QueueMessage.msg p lab S => ext_tag.recv p lab S) M := by
                have hStep : mon_yes_seq T'
                    ((ext_tag.recv q0 l0 s0) ::
                      ((rest ++ left).map fun m => match m with
                        | QueueMessage.msg p lab S => ext_tag.recv p lab S)) M :=
                  mon_yes_seq.step hYW' hTailSeq
                simpa [List.map_append] using hStep
              exact mon_yes_seq_to_monitor_fold_aux hGoalSeq
        | tRec _ => exact False.elim hNF

/-- Maximality recovers across one unfold: a maximal derivation at a
    `tRec` head yields a maximal derivation for the same target at the
    unfolding (base cases re-wrap; prefix arms are impossible by head
    shape). -/
theorem maxRecover_unfold {X : String} {B : SessionType} {γ : ext_tag} {V : SessionType}
    (hE : mon_tr_yes_exist (SessionType.tRec X B) γ V)
    (hM : mon_tr_yes_max_deriv hE) :
    ∃ Esub : mon_tr_yes_exist (substSessionType B X (SessionType.tRec X B)) γ V,
      mon_tr_yes_max_deriv Esub := by
  cases hE with
  | unfold Esub =>
    cases hM with
    | unfold hMsub => exact ⟨Esub, hMsub⟩
    | @base _ _ _ hb =>
      cases hb with
      | tRec hbsub => exact ⟨mon_tr_yes_exist.base hbsub, @mon_tr_yes_max_deriv.base _ _ _ hbsub⟩
  | base hb =>
    cases hb with
    | tRec hbsub => exact ⟨mon_tr_yes_exist.base hbsub, @mon_tr_yes_max_deriv.base _ _ _ hbsub⟩

/-- Full absorption, Prop form: UnfoldStar induction. Base (head-normal
    endpoint): queue split plus banked transfer. Step (`tRec` head):
    `st_trans` inversion plus chain re-heading; well-formedness threads
    through substitution preservation. -/
theorem habs_full_aux {T U : SessionType} (hStar : UnfoldStar T U) (hNFU : IsHeadNF U)
    {Q Q' : Queue} {T' : SessionType} {p : Role} {lab : Lab} {S : DataSort} {M : SessionType}
    (hWF : T.WellFormed) (hEnc : monitor_fold (T, Q) M)
    (hSQ : sq_trans (T, Q) (sq_action.dequeue p lab S) (T', Q')) :
    monitor_fold (T', Q') M := by
  revert hNFU hWF hEnc hSQ
  induction hStar with
  | refl =>
    intro hNFU hWF hEnc hSQ
    cases hSQ with
    | dequeue hST hQ =>
      obtain ⟨seen, left, hQeq, hQ'eq, hfresh⟩ := dequeue_split hQ
      have hfresh' : ∀ m ∈ seen, m.1 ≠ p := fun m hm => hfresh m hm
      rw [hQeq] at hEnc
      have hEnc' : monitor_fold (T', seen ++ left) M :=
        absorb_transfer_headnormal hWF hNFU hfresh' hST hEnc
      rw [hQ'eq]
      exact hEnc'
  | step h1 h2 ih =>
    intro hNFU hWF hEnc hSQ
    cases h1 with
    | @tRec X B =>
      cases hSQ with
      | dequeue hST hQ =>
        cases hST with
        | tRec hSub =>
          cases Q with
          | nil =>
            have hQnone : (none : Option Queue) = some Q' := hQ
            cases hQnone
          | cons m1 rest =>
            rcases m1 with ⟨p1, lab1, S1⟩
            simp only [monitor_fold, monitor_fold_aux] at hEnc
            obtain ⟨Tmid1, E1, hTail⟩ := hEnc
            obtain ⟨hE1, hM1⟩ := E1
            obtain ⟨Esub, hMsub⟩ := maxRecover_unfold hE1 hM1
            have hEnc1 : monitor_fold
                (substSessionType B X (SessionType.tRec X B),
                  (QueueMessage.msg p1 lab1 S1) :: rest) M :=
              ⟨Tmid1, ⟨Esub, hMsub⟩, hTail⟩
            obtain ⟨hND, hCl, hCo⟩ := hWF
            have hNDB : SessionType.NoDupl B := by
              cases hND with
              | tRec hB => exact hB
            have hND1 : SessionType.NoDupl
                (substSessionType B X (SessionType.tRec X B)) :=
              NoDupl_subst hNDB hND
            have hClB : (B.fv.filter fun x => x != X) = [] := by
              simpa [SessionType.IsClosed, SessionType.fv] using hCl
            have hCl1 : (substSessionType B X (SessionType.tRec X B)).IsClosed := by
              unfold SessionType.IsClosed
              rw [fv_subst_aux _ _ _ hCl]
              exact hClB
            have hCo1 : (substSessionType B X (SessionType.tRec X B)).Contractive := by
              have hCoR := hCo
              cases hCo with
              | tRec hCoB _ => exact IsContractive_subst hCoB hCoR hCl
            have hWF1 : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
              ⟨hND1, hCl1, hCo1⟩
            have hSQ1 : sq_trans (substSessionType B X (SessionType.tRec X B),
                (QueueMessage.msg p1 lab1 S1) :: rest)
                (sq_action.dequeue p lab S) (T', Q') :=
              sq_trans.dequeue hSub hQ
            exact ih hNFU hWF1 hEnc1 hSQ1

/-- Full absorption, Option form: choose the fold witness, transfer along
    the star, and re-choose by endpoint uniqueness. -/
theorem habs_full {T T' : SessionType} {Q Q' : Queue} {p : Role}
    {lab : Lab} {S : DataSort} {M : SessionType}
    (hWF : T.WellFormed) (hVal : monitor_fold_val_partial (T, Q) = some M)
    (hSQ : sq_trans (T, Q) (sq_action.dequeue p lab S) (T', Q')) :
    monitor_fold_val_partial (T', Q') = some M := by
  obtain ⟨U, hStar, hNFU⟩ := unfoldStar_normal_exists T hWF.2.2 hWF.2.1
  have hEnc : monitor_fold (T, Q) M := monitor_fold_val_partial_eq_of_some hVal
  have hEnc' : monitor_fold (T', Q') M := habs_full_aux hStar hNFU hWF hEnc hSQ
  have hWF' : T'.WellFormed := SessionType.wellFormedPreserved _ _ _ hWF
    (by cases hSQ with | dequeue hST hQ => exact hST)
  unfold monitor_fold_val_partial
  by_cases hex : ∃ T'', monitor_fold (T', Q') T''
  · rw [dite_eq_left hex]
    have hUq : hex.choose = M :=
      monitor_fold_aux_value_unique _ _ _ _ hWF' hex.choose_spec hEnc'
    rw [hUq]
  · rw [dite_eq_right hex]
    exact False.elim (hex ⟨M, hEnc'⟩)

end MonitorSoundAbsorb

section MonitorSoundDequeue

/-- Monitored dequeue steps invert to session-level witnesses: `lift` and
    `comm` arms clash by label; `dequeue` arms re-instrument the target
    via full absorption. -/
theorem invert_mon_dequeue_new {N : Network} {MN MN' : MonitoredNetwork}
    {ℓ : mon_net_label}
    (hCons : consistentInstrumentation N = some MN)
    (h : mon_net_trans MN ℓ MN')
    (hWFN : N.WellFormed) :
    ∀ (r p : Role) (lab : Lab) (S : DataSort),
      ℓ = mon_net_label.τ_dequeue r p lab S →
      ∃ (stq stq' : SessionTypeWithQueue),
        sq_trans stq (sq_action.dequeue p lab S) stq' ∧
        (r, stq) ∈ N ∧ MN' = consistentInstrumentation (Network.replace N r stq') := by
  intro r p lab S hEq
  match h with
  | @mon_net_trans.lift MN rl mt mt' ℓ' h_tr hmem =>
    cases h_tr with
    | good_send hSQ hYes => simp [mon_net_label.ofmon_label] at hEq
    | good_recv hSQ hYes => simp [mon_net_label.ofmon_label] at hEq
    | badOut hSQ hMon => simp [mon_net_label.ofmon_label] at hEq
    | badIn hMon => simp [mon_net_label.ofmon_label] at hEq
    | @dequeue stq stq' M p0 lab0 S0 h_sq =>
      simp [mon_net_label.ofmon_label] at hEq
      rcases hEq with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨hmemN, hVal⟩ := consistentInstrumentation_inv_mem hmem hCons
      obtain ⟨T, Q⟩ := stq
      obtain ⟨T', Q'⟩ := stq'
      have hWFstq : T.WellFormed := hWFN.2.1 _ hmemN
      have hVal' : monitor_fold_val_partial (T', Q') = some M :=
        habs_full hWFstq hVal h_sq
      have hCI : consistentInstrumentation (Network.replace N rl (T', Q')) =
          some (MonitoredNetwork.replace MN rl ((T', Q'), M)) :=
        consistentInstrumentation_replace hCons hVal'
      exact ⟨(T, Q), (T', Q'), h_sq, hmemN, hCI.symm⟩
  | @mon_net_trans.comm MN p1 q1 lab1 S1 mtp mtp' mtq mtq' h_send h_recv hmem_p hmem_q =>
    cases hEq

/-- Monitored dequeue steps reflect to network dequeue steps. -/
theorem mon_dequeue_network_dequeue {N : Network} {MN MN' : MonitoredNetwork}
    {r p : Role} {lab : Lab} {S : DataSort}
    (hWFN : N.WellFormed)
    (hCons : consistentInstrumentation N = some MN)
    (hTr : mon_net_trans MN (mon_net_label.τ_dequeue r p lab S) MN') :
    ∃ N'', net_trans N (net_label.τ_dequeue r p lab S) N'' ∧
      consistentInstrumentation N'' = some MN' := by
  obtain ⟨stq, stq', hSQ, hmemN, hCI⟩ :=
    invert_mon_dequeue_new hCons hTr hWFN r p lab S rfl
  exact ⟨Network.replace N r stq',
    net_trans.dequeue hSQ hmemN, hCI.symm⟩

/-- Network dequeue steps are matched by the monitor: the session step is
    shared (dequeue needs no acceptability premise), and
    re-instrumentation goes through full absorption with well-formedness
    from the network invariant. -/
theorem network_dequeue_mon_dequeue {N N' : Network} {MN : MonitoredNetwork}
    {r p : Role} {lab : Lab} {S : DataSort}
    (hWFN : N.WellFormed)
    (hCons : consistentInstrumentation N = some MN)
    (hTr : net_trans N (net_label.τ_dequeue r p lab S) N') :
    ∃ MN', mon_net_trans MN (mon_net_label.τ_dequeue r p lab S) MN' ∧
      consistentInstrumentation N' = some MN' := by
  cases hTr with
  | @dequeue _ _ stq stq' _ _ hSQ hmem =>
    obtain ⟨M, hVal, hmemMN⟩ := mem_consistentInstrumentation hmem hCons
    obtain ⟨T, Q⟩ := stq
    obtain ⟨T', Q'⟩ := stq'
    have hWFstq : T.WellFormed := hWFN.2.1 _ hmem
    have hVal' : monitor_fold_val_partial (T', Q') = some M :=
      habs_full hWFstq hVal hSQ
    refine ⟨MonitoredNetwork.replace MN r ((T', Q'), M), ?_, ?_⟩
    · exact mon_net_trans.lift (mon_trans.dequeue hSQ) hmemMN
    · exact consistentInstrumentation_replace hCons hVal'

end MonitorSoundDequeue
