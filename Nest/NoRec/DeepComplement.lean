import Nest.SessionUtils
import Nest.MonitorToolkit
import Nest.NoRec.DrainAccept
import Nest.NoRec.DrainSurvival
import Nest.NoRec.NoRecEncoder

/-!
# Deep/drain duality core (choice-function core bridges, decision procedures, oldest-queue utilities).
-/


-- ================================================================
-- General dequeue scan: key back-propagation + transfer induction.
-- ================================================================

/-- Key back-propagation, NoRec: if an `extC p` state absorbs a `p`-fresh
    prefix and then fires the distinguished `recv p lab S` maximally, the
    `(lab, S)` key is present in its branches. Backward induction on the
    prefix: the base case inverts the γ-step (forced `base` — `pfxExt` needs
    `p ≠ p`); each step inverts the prefix maximal step (forced `pfxExt` —
    `base` is killed by freshness, other shapes by mismatch) and pulls
    presence back through `hkey`. Only ∃-level inversions (no maximality,
    no determinism, no lifting). -/
lemma dequeue_scan_key_backprop_norec {K : List (Lab × DataSort × SessionType)}
    {rest : Queue} {U1' U2' : SessionType}
    {p : Role} {lab : Lab} {S : DataSort}
    (hKNR : (SessionType.externalChoice p K).NoRec)
    (hKND : (SessionType.externalChoice p K).NoDupl)
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
        obtain ⟨hX1NR, hX1ND⟩ :=
          mon_tr_yes_preserves_norec_no_dupl hKNR hKND hYi'
        obtain ⟨T2', hmemK1⟩ := ih hX1NR hX1ND hfresh' hTi hGam
        rcases hkey lab S T2' hmemK1 with ⟨T0, hmemK⟩
        exact ⟨T0, hmemK⟩

/-- Absorption transfer across a dequeue scan, NoRec: if the queue
    `seen ++ [msg p lab S] ++ left` (with `seen` `p`-fresh) fully absorbs
    from `T` to `M`, and the session fires `inp p lab S` to `T'`, then the
    scanned queue `seen ++ left` absorbs from `T'` to the same `M`.
    Induction on `seen`: the empty case is `dequeue_head_preserves_absorption`; each step
    splits off the off-role head (maximal), inverts it (MaxDeriv-first, single
    `kept`), pulls the `(lab, S)`-key back through the tail by
    `dequeue_scan_key_backprop_norec`, converts presence+linkage to the
    same-target maximal step (`hall`/`hallMax`, as in the threaded peak),
    and recurses. Needs no well-formedness except in the head case. -/lemma monitor_fold_absorb_dequeue_transfer_norec {seen : Queue} {T T' M : SessionType}
    {p : Role} {lab : Lab} {S : DataSort} {left : Queue}
    (hTNR : T.NoRec) (hTND : T.NoDupl) (hTWF : T.WellFormed)
    (hfresh : ∀ m ∈ seen, m.1 ≠ p)
    (hST : st_trans T (st_label.inp p lab S) T')
    (hEnc : monitor_fold (T, seen ++ [QueueMessage.msg p lab S] ++ left) M) :
    monitor_fold (T', seen ++ left) M := by
  induction seen generalizing T T' M left hTNR hTND hTWF hST with
  | nil =>
    exact dequeue_head_preserves_absorption hTWF hEnc hST
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
              have hWNRND : (SessionType.externalChoice p kept).NoRec ∧
                  (SessionType.externalChoice p kept).NoDupl :=
                mon_tr_yes_preserves_norec_no_dupl hTNR hTND hY0'
              rcases dequeue_scan_key_backprop_norec hWNRND.1 hWNRND.2
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
              have hWWF : (SessionType.externalChoice p kept).WellFormed :=
                mon_tr_yes_preserves_wf hY0' hTWF
              have hTail : monitor_fold (Wstar, rest ++ left) M :=
                ih hWNRND.1 hWNRND.2 hWWF hfresh' hSTW hEncW
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
        | tRec _ => cases hTNR


/-- A deeply-draining state can approx-reduce to an empty queue. -/
theorem CanAlwaysDrainInternalDeep.drains {T : SessionType} {Q : Queue}
    (h : CanAlwaysDrainInternalDeep T Q) :
    ∃ (T' : SessionType) (ρ : List st_label), over_trans_trace (T, Q) ρ (T', []) := by
  obtain ⟨Tn, ρ, hTr, -⟩ := h
  exact ⟨Tn, ρ, hTr⟩


/-- A `Core`-deep state can approx-reduce to an empty queue (its
    witness trace). -/
theorem CanAlwaysDrainInternalDeepCore.drains {T : SessionType} {Q : Queue}
    (h : CanAlwaysDrainInternalDeepCore T Q) :
    ∃ (T' : SessionType) (ρ : List st_label), over_trans_trace (T, Q) ρ (T', []) := by
  cases h with
  | mk _ _ Tn ρ _ hTr _ _ _ => exact ⟨Tn, ρ, hTr⟩


/-- Suffix of a `Cannot` witness is `Cannot` of its midpoint: the
    stuck end travels, plus the on-trace conditions restricted
    through the prefix (same equation as the `Deep` suffix). -/
theorem CannotAlwaysDrainInternalDeep.suffix {T0 T1 Tn : SessionType}
    {Q0 Q1 Qn : Queue} {ρ ρ1 ρ2 : List st_label}
    (hne : Qn ≠ [])
    (hend : Tn = SessionType.tEnd ∨
      (∃ (branches : List (Role × Lab × DataSort × SessionType))
        (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
        (m : QueueMessage),
        Tn = SessionType.internalChoice branches ∧
        (p, lab, S, T') ∈ branches ∧ m ∈ Qn ∧ m.1 = p) ∨
      ((∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
        (lab : Lab) (S : DataSort) (m : QueueMessage),
        Tn = SessionType.externalChoice p branches ∧ oldest_from p Qn m ∧
        m = QueueMessage.msg p lab S ∧
        ∀ (T' : SessionType), (lab, S, T') ∉ branches) ∨
      (∃ (X : String) (B U : SessionType),
        Tn = SessionType.tRec X B ∧ UnfoldStar (SessionType.tRec X B) U ∧
        (U = SessionType.tEnd ∨
          (∃ (branches : List (Role × Lab × DataSort × SessionType))
            (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
            (m : QueueMessage),
            U = SessionType.internalChoice branches ∧
            (p, lab, S, T') ∈ branches ∧ m ∈ Qn ∧ m.1 = p) ∨
          (∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
            (lab : Lab) (S : DataSort) (m : QueueMessage),
            U = SessionType.externalChoice p branches ∧ oldest_from p Qn m ∧
            m = QueueMessage.msg p lab S ∧
            ∀ (T' : SessionType), (lab, S, T') ∉ branches)))))
    (hclos : ∀ (Ti : SessionType) (Qi : Queue) (σ1 σ2 : List st_label),
      over_trans_trace (T0, Q0) σ1 (Ti, Qi) →
      over_trans_trace (Ti, Qi) σ2 (Tn, Qn) →
      ρ = σ1 ++ σ2 →
      ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
        Ti = SessionType.internalChoice branches → branches ≠ [] →
        int_choice_fireable Ti Qi branches →
        ∃ (br : Role × Lab × DataSort × SessionType),
          br ∈ branches ∧ CannotAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
      (∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
        Ti = SessionType.externalChoice p branches → branches ≠ [] →
        (∀ m ∈ Qi, m.1 ≠ p) →
        ∀ (br : Lab × DataSort × SessionType),
          br ∈ branches → CannotAlwaysDrainInternalDeepCore br.2.2 Qi)))
    (h1 : over_trans_trace (T0, Q0) ρ1 (T1, Q1))
    (h2 : over_trans_trace (T1, Q1) ρ2 (Tn, Qn))
    (heq : ρ = ρ1 ++ ρ2) :
    CannotAlwaysDrainInternalDeep T1 Q1 := by
  refine ⟨Tn, Qn, ρ2, h2, hne, hend, ?_⟩
  intro Ti Qi σ1 σ2 g1 g2 geq2
  exact hclos Ti Qi (ρ1 ++ σ1) σ2 (over_trans_trace_append h1 g1) g2
    (by rw [heq, geq2, List.append_assoc])


/-- `Deep` at `tEnd` forces an empty queue (only `refl` traces). -/
theorem deep_tEnd_empty {Q : Queue}
    (h : CanAlwaysDrainInternalDeep SessionType.tEnd Q) : Q = [] := by
  obtain ⟨Tn, ρ, hTr, -⟩ := h
  cases ρ with
  | nil =>
    have heq := overTrTrace_nil_eq hTr
    exact (congrArg Prod.snd heq).symm
  | cons α ρ' =>
    cases hTr with
    | step hS _ =>
      cases hS with
      | dequeue hEq _ _ => cases hEq
      | specInp hEq _ _ => cases hEq
      | tauUnfold hU => cases hU
      | sendFresh hEq _ _ => cases hEq


/-- `Cannot` at `tEnd` forces a nonempty queue (only `refl` traces,
    whose end must satisfy `Qn ≠ []`). -/
theorem cannot_tEnd_nonempty {Q : Queue}
    (h : CannotAlwaysDrainInternalDeep SessionType.tEnd Q) : Q ≠ [] := by
  obtain ⟨Tn, Qn, ρ, hTr, hne, -, -⟩ := h
  cases ρ with
  | nil =>
    have heq := overTrTrace_nil_eq hTr
    have hQ : Qn = Q := congrArg Prod.snd heq
    rw [hQ] at hne
    exact hne
  | cons α ρ' =>
    cases hTr with
    | step hS _ =>
      cases hS with
      | dequeue hEq _ _ => cases hEq
      | specInp hEq _ _ => cases hEq
      | sendFresh hEq _ _ => cases hEq
      | tauUnfold hU => cases hU


/-- `Deep` at a blocked `intC` (some branch sender queued) is
    impossible: blocked states admit no step, so the only trace is
    `refl`, whose end still holds the queued message. -/
theorem deep_blocked_intC_false {branches : List (Role × Lab × DataSort × SessionType)}
    {Q : Queue} {br : Role × Lab × DataSort × SessionType} {m : QueueMessage}
    (hmemB : br ∈ branches) (hmemM : m ∈ Q) (heqM : m.1 = br.1)
    (h : CanAlwaysDrainInternalDeep (SessionType.internalChoice branches) Q) :
    False := by
  obtain ⟨Tn, ρ, hTr, -⟩ := h
  cases ρ with
  | nil =>
    have heq := overTrTrace_nil_eq hTr
    have hQ : Q = ([] : Queue) := (congrArg Prod.snd heq).symm
    rw [hQ] at hmemM
    simp at hmemM
  | cons α ρ' =>
    cases hTr with
    | step hS _ =>
      cases hS with
      | dequeue hEq _ _ => cases hEq
      | specInp hEq _ _ => cases hEq
      | sendFresh hEq _ hFresh =>
        cases hEq
        obtain ⟨p, lab, S, T0⟩ := br
        exact (hFresh p lab S T0 hmemB m hmemM) heqM
      | tauUnfold hU => cases hU


/-- Exclusivity at `tEnd`: drains force `[]`, failures force `≠[]`
   . -/
theorem deep_cannot_tEnd_excl {Q : Queue}
    (hD : CanAlwaysDrainInternalDeep SessionType.tEnd Q)
    (hC : CannotAlwaysDrainInternalDeep SessionType.tEnd Q) : False :=
  cannot_tEnd_nonempty hC (deep_tEnd_empty hD)


/-- Exclusivity at blocked `intC`: drains are impossible there
    (no induction). -/
theorem deep_cannot_blocked_excl
    {branches : List (Role × Lab × DataSort × SessionType)}
    {Q : Queue} {br : Role × Lab × DataSort × SessionType} {m : QueueMessage}
    (hmemB : br ∈ branches) (hmemM : m ∈ Q) (heqM : m.1 = br.1)
    (hD : CanAlwaysDrainInternalDeep (SessionType.internalChoice branches) Q) :
    False :=
  deep_blocked_intC_false hmemB hmemM heqM hD


/-- Corner: an oldest-absent end coexists impossibly with any drain —
    the drain's forced first dequeue has a present key for the same
    oldest message. -/
theorem corner_oldest_vs_drain {p : Role}
    {branches : List (Lab × DataSort × SessionType)} {Q : Queue}
    {Tn : SessionType} {ρd : List st_label}
    (hTrD : over_trans_trace (SessionType.externalChoice p branches, Q) ρd (Tn, []))
    {lab0 : Lab} {S0 : DataSort} {m0 : QueueMessage}
    (hOld : oldest_from p Q m0) (hmeq : m0 = QueueMessage.msg p lab0 S0)
    (habs : ∀ (T' : SessionType), (lab0, S0, T') ∉ branches) : False := by
  obtain ⟨seen, rest, hQeq, hm1, hseen⟩ := hOld
  subst hmeq
  have hpmem : QueueMessage.msg p lab0 S0 ∈ Q := by
    rw [hQeq]
    simp
  cases ρd with
  | nil =>
    have heq := overTrTrace_nil_eq hTrD
    have hQ : Q = ([] : Queue) := (congrArg Prod.snd heq).symm
    rw [hQ] at hpmem
    simp at hpmem
  | cons β ρd' =>
    cases hTrD with
    | step hS hT2 =>
      cases hS with
      | @dequeue _ _ _ _ p' lab S branches' hEqT hmem hQd =>
        rw [SessionType.externalChoice.injEq] at hEqT
        obtain ⟨rfl, rfl⟩ := hEqT
        obtain ⟨seen2, left2, hQeq2, hseen2⟩ := dequeue_oldest_of_some hQd
        have hEq : QueueMessage.msg p lab0 S0 = QueueMessage.msg p lab S :=
          oldest_from_unique ⟨seen, rest, hQeq, rfl, hseen⟩ ⟨seen2, left2, hQeq2, rfl, hseen2⟩
        rw [QueueMessage.msg.injEq] at hEq
        obtain ⟨-, rfl, rfl⟩ := hEq
        exact habs _ hmem
      | specInp hEq hmem hAbs =>
        cases hEq
        exact (hAbs _ hpmem rfl).elim
      | sendFresh hEq hST hFresh =>
        cases hEq
      | tauUnfold hU => cases hU

/-!
# NoRec.DeepComplement: NoRec deep/drain failure duality.

`mon_reject_implies_nodrain_norec` uses `drain_implies_mon_exists_accepts_norec`
from `Nest.NoRec.DrainAccept`; everything else is closed within this file
(modulo the shared deep-drainability core in `Nest.SessionUtils`).
-/

section MemWellFormed

/-! Membership WellFormed: branch targets inherit `WellFormed` (with `fv`
preservation). Used by the NoRec soundness chain, here and in `Nest.NoRec.SteerLoop`. -/

/-- Free variables distribute into internal-choice branch targets. -/
private lemma fv_mem_of_mem_intBranches
    {branches : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType} {y : String}
    (hmem : x ∈ branches) (hy : y ∈ SessionType.fv x.2.2.2) :
    y ∈ SessionType.fv (SessionType.internalChoice branches) := by
  revert hmem hy
  induction branches with
  | nil =>
    intro hmem hy
    simp at hmem
  | cons b bs ih =>
    intro hmem hy
    simp at hmem
    simp only [SessionType.fv]
    rcases hmem with rfl | hmem
    · exact List.mem_append.mpr (Or.inl hy)
    · exact List.mem_append.mpr (Or.inr (ih hmem hy))

/-- Free variables of an `extC` branch target occur in the parent. -/
private lemma fv_mem_of_mem_extBranches
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType} {y : String}
    (hmem : x ∈ branches) (hy : y ∈ SessionType.fv x.2.2) :
    y ∈ SessionType.fv (SessionType.externalChoice p branches) := by
  revert hmem hy
  induction branches with
  | nil =>
    intro hmem hy
    simp at hmem
  | cons b bs ih =>
    intro hmem hy
    simp at hmem
    simp only [SessionType.fv]
    rcases hmem with rfl | hmem
    · exact List.mem_append.mpr (Or.inl hy)
    · exact List.mem_append.mpr (Or.inr (ih hmem hy))

/-- `intC` branch targets inherit `WellFormed`. -/
theorem wf_of_mem_intBranches
    {branches : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType}
    (hmem : x ∈ branches)
    (hWF : (SessionType.internalChoice branches).WellFormed) :
    x.2.2.2.WellFormed := by
  obtain ⟨hND, hCl, hCt⟩ := hWF
  cases hND with
  | internalChoice _ _ hbr =>
    cases hCt with
    | internalChoice hct =>
      refine ⟨hbr _ hmem, ?_, hct _ hmem⟩
      show SessionType.fv _ = []
      cases hfv : SessionType.fv x.2.2.2 with
      | nil => rfl
      | cons y ys =>
        have hmy : y ∈ SessionType.fv x.2.2.2 := by
          rw [hfv]
          simp
        have hpar := fv_mem_of_mem_intBranches hmem hmy
        have hCl' : SessionType.fv (SessionType.internalChoice branches) = [] :=
          hCl
        rw [hCl'] at hpar
        simp at hpar

/-- `extC` branch targets inherit `WellFormed`. -/
theorem wf_of_mem_extBranches
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType}
    (hmem : x ∈ branches)
    (hWF : (SessionType.externalChoice p branches).WellFormed) :
    x.2.2.WellFormed := by
  obtain ⟨hND, hCl, hCt⟩ := hWF
  cases hND with
  | externalChoice _ _ hbr =>
    cases hCt with
    | externalChoice hct =>
      refine ⟨hbr _ hmem, ?_, hct _ hmem⟩
      show SessionType.fv _ = []
      cases hfv : SessionType.fv x.2.2 with
      | nil => rfl
      | cons y ys =>
        have hmy : y ∈ SessionType.fv x.2.2 := by
          rw [hfv]
          simp
        have hpar := fv_mem_of_mem_extBranches (p := p) hmem hmy
        have hCl' : SessionType.fv (SessionType.externalChoice p branches) = [] :=
          hCl
        rw [hCl'] at hpar
        simp at hpar

end MemWellFormed
section NostepCannot

/-- Stuck-nonempty `NoRec`+`WellFormed` states match a `Cannot`
    end-shape (terminal exhaustiveness): `tEnd` directly; `extC`
    by oldest-owner-message key absence (no owner message means a
    spec step fires; a present key would dequeue past the skipped
    prefix); `intC` by blockedness (fireable would step via any
    branch); `tVar`/`tRec` excluded by closedness/`NoRec`. -/
theorem cannot_end_of_nostep_norec {T : SessionType} {Q : Queue}
    (hNR : T.NoRec) (hWF : T.WellFormed)
    (hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
      ¬ over_trans (T, Q) α stq') :
    (T = SessionType.tEnd ∨
      (∃ (branches : List (Role × Lab × DataSort × SessionType))
        (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
        (m : QueueMessage),
        T = SessionType.internalChoice branches ∧
        (p, lab, S, T') ∈ branches ∧ m ∈ Q ∧ m.1 = p) ∨
      (∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
        (lab : Lab) (S : DataSort) (m : QueueMessage),
        T = SessionType.externalChoice p branches ∧ oldest_from p Q m ∧
        m = QueueMessage.msg p lab S ∧
        ∀ (T' : SessionType), (lab, S, T') ∉ branches) ∨
      (∃ (X : String) (B U : SessionType),
        T = SessionType.tRec X B ∧ UnfoldStar (SessionType.tRec X B) U ∧
        (U = SessionType.tEnd ∨
          (∃ (branches : List (Role × Lab × DataSort × SessionType))
            (p : Role) (lab : Lab) (S : DataSort) (T' : SessionType)
            (m : QueueMessage),
            U = SessionType.internalChoice branches ∧
            (p, lab, S, T') ∈ branches ∧ m ∈ Q ∧ m.1 = p) ∨
          (∃ (p : Role) (branches : List (Lab × DataSort × SessionType))
            (lab : Lab) (S : DataSort) (m : QueueMessage),
            U = SessionType.externalChoice p branches ∧ oldest_from p Q m ∧
            m = QueueMessage.msg p lab S ∧
            ∀ (T' : SessionType), (lab, S, T') ∉ branches)))) := by
  classical
  cases T with
  | tEnd => exact Or.inl rfl
  | externalChoice p branches =>
    have hneB : branches ≠ [] := hWF.1.ne_of_externalChoice
    by_cases hHasP : ∃ m ∈ Q, m.1 = p
    · obtain ⟨m, hOld, hm1⟩ := oldest_of_mem Q p hHasP
      obtain ⟨seen, rest, hQeq, hm1b, hseen⟩ := hOld
      obtain ⟨r, lab, S⟩ := m
      have hmr : r = p := hm1
      subst r
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨p, branches, lab, S, QueueMessage.msg p lab S, rfl, ?_, rfl, ?_⟩
      · exact ⟨seen, rest, hQeq, rfl, hseen⟩
      · intro T' hmem
        have hQ : Q.dequeue (QueueMessage.msg p lab S) = some (seen ++ rest) := by
          rw [hQeq]
          simp only [Queue.dequeue]
          exact dequeue_skip_seen hseen
        exact hNo _ _ (over_trans.dequeue rfl hmem hQ)
    · push Not at hHasP
      cases branches with
      | nil => exact absurd rfl hneB
      | cons br rest =>
        obtain ⟨lab, S, T0⟩ := br
        have hAbs : ∀ m ∈ Q, m.1 ≠ p := fun m hmem => hHasP _ hmem
        exact (hNo _ _ (over_trans.specInp rfl (List.mem_cons.mpr (Or.inl rfl)) hAbs)).elim
  | internalChoice branches =>
    have hneB : branches ≠ [] :=
      SessionType.WellFormed.ne_of_internalChoice rfl hWF
    by_cases hfire : int_choice_fireable (SessionType.internalChoice branches) Q branches
    · cases branches with
      | nil => exact absurd rfl hneB
      | cons br rest =>
        obtain ⟨p, lab, S, T0⟩ := br
        have hST : st_trans (SessionType.internalChoice ((p, lab, S, T0) :: rest))
            (st_label.out p lab S) T0 :=
          st_trans.intC (List.mem_cons.mpr (Or.inl rfl))
        have hFresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
            (r', l', s', U) ∈ ((p, lab, S, T0) :: rest) →
            ∀ m ∈ Q, m.1 ≠ r' := by
          intro r' l' s' U hmem m hmemM
          exact hfire (r', l', s', U) hmem m hmemM
        exact (hNo _ _ (over_trans.sendFresh rfl hST hFresh)).elim
    · unfold int_choice_fireable at hfire
      push Not at hfire
      obtain ⟨br, hmemB, m, hmemM, heqM⟩ := hfire
      obtain ⟨p, lab, S, T0⟩ := br
      exact Or.inr (Or.inl ⟨branches, p, lab, S, T0, m, rfl, hmemB,
        hmemM, heqM⟩)
  | tVar X =>
    obtain ⟨-, hCl, -⟩ := hWF
    unfold SessionType.IsClosed at hCl
    have hfv : SessionType.fv (SessionType.tVar X) = [X] := rfl
    rw [hfv] at hCl
    simp at hCl
  | tRec X B => cases hNR

/-- Refl-`Cannot` from stuck-nonempty (helper): end-shape via
    `cannot_end_of_nostep_norec`, closures vacuous (a fireable `intC`
    would send; an absent `extC` would spec). -/
theorem cannot_of_nostep_norec {T : SessionType} {Q : Queue}
    (hNR : T.NoRec) (hWF : T.WellFormed)
    (hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
      ¬ over_trans (T, Q) α stq')
    (hne : Q ≠ []) :
    CannotAlwaysDrainInternalDeep T Q := by
  obtain hend := cannot_end_of_nostep_norec hNR hWF hNo
  refine ⟨T, Q, [], over_trans_trace.refl _, hne, hend, ?_⟩
  intro Ti Qi ρ1 ρ2 h1 h2 heq
  cases ρ1 with
  | nil =>
    have hST := overTrTrace_nil_eq h1
    cases hST
    refine ⟨?_, ?_⟩
    · intro branches hEq hneB hfire
      cases branches with
      | nil => exact absurd rfl hneB
      | cons br rest =>
        obtain ⟨s, lab, S, U⟩ := br
        have hSTi : st_trans T (st_label.out s lab S) U := by
          rw [hEq]
          exact st_trans.intC (List.mem_cons.mpr (Or.inl rfl))
        have hFresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort)
            (U' : SessionType),
            (r', l', s', U') ∈ (s, lab, S, U) :: rest →
            ∀ m ∈ Q, m.1 ≠ r' := by
          intro r' l' s' U' hmem m hm
          exact hfire (r', l', s', U') hmem m hm
        exact (hNo _ _ (over_trans.sendFresh hEq hSTi hFresh)).elim
    · intro p branches2 hEq hneB habs br hmem
      obtain ⟨lab, S, U0⟩ := br
      exact (hNo _ _ (over_trans.specInp hEq hmem habs)).elim
  | cons α ρ1' =>
    cases h1 with
    | step hS _ => exact (hNo _ _ hS).elim
end NostepCannot
section DeepExclusion

/-- Exclusivity by size induction (every `over_trans` step shrinks the
    session, so one induction with the queue bound threaded through
    suffices; no mutual induction is needed). -/
theorem deep_excl_aux_norec (m : Nat) (T : SessionType) (Q : Queue) (n : Nat) :
    Q.length ≤ n → sizeOf T ≤ m → T.NoRec → T.WellFormed →
    CanAlwaysDrainInternalDeep T Q → ¬ CannotAlwaysDrainInternalDeep T Q := by
  revert T Q
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro T Q hlen hsize hNR hWF
    classical
    revert hlen hsize hNR hWF
    cases T with
    | tEnd =>
      intro hlen hsize hNR hWF hD hC
      exact deep_cannot_tEnd_excl hD hC
    | internalChoice branches =>
      intro hlen hsize hNR hWF hD hC
      by_cases hfire : int_choice_fireable (SessionType.internalChoice branches) Q
        branches
      · have hneB : branches ≠ [] :=
          SessionType.WellFormed.ne_of_internalChoice rfl hWF
        obtain ⟨TnD, ρD0, hTrD0, hallD⟩ := hD
        obtain ⟨TnC, QnC, ρC0, hTrC0, hneC0, hendC0, hallC⟩ := hC
        obtain ⟨hIntD, -⟩ :=
          hallD _ _ [] _ (over_trans_trace.refl _) hTrD0 (by simp)
        obtain ⟨hIntC, -⟩ :=
          hallC _ _ [] _ (over_trans_trace.refl _) hTrC0 (by simp)
        obtain ⟨br, hmemB, hCoreB⟩ := hIntC branches rfl hneB hfire
        obtain ⟨p, lab, S, T0⟩ := br
        have hGood : CanAlwaysDrainInternalDeepCore T0 Q :=
          hIntD branches rfl hneB (p, lab, S, T0) hmemB
        have hlt : sizeOf T0 < sizeOf (SessionType.internalChoice branches) :=
          sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
        have hNR0 : T0.NoRec := noRec_of_mem_intBranches hNR hmemB
        have hWF0 : T0.WellFormed := wf_of_mem_intBranches hmemB hWF
        exact ih (sizeOf T0) (by omega) T0 Q hlen (Nat.le_refl _) hNR0 hWF0
          hGood.toDeep hCoreB.toDef
      · unfold int_choice_fireable at hfire
        push Not at hfire
        obtain ⟨br, hmemB, m, hmemM, heqM⟩ := hfire
        exact deep_cannot_blocked_excl hmemB hmemM heqM hD
        | externalChoice p branches =>
          intro hlen hsize hNR hWF hD hC
          by_cases habsP : ∀ m ∈ Q, m.1 ≠ p
          · have hneB : branches ≠ [] := hWF.1.ne_of_externalChoice
            obtain ⟨TnD, ρD0, hTrD0, hallD⟩ := hD
            obtain ⟨TnC, QnC, ρC0, hTrC0, hneC0, hendC0, hallC⟩ := hC
            obtain ⟨-, hExtD, -⟩ :=
              hallD _ _ [] _ (over_trans_trace.refl _) hTrD0 (by simp)
            obtain ⟨-, hExtC⟩ :=
              hallC _ _ [] _ (over_trans_trace.refl _) hTrC0 (by simp)
            obtain ⟨br, hmemB, hCoreG⟩ := hExtD p branches rfl hneB
              (absence_imp_noDequeueFrom rfl habsP)
            obtain ⟨lab, S, T0⟩ := br
            have hBad : CannotAlwaysDrainInternalDeepCore T0 Q :=
              hExtC p branches rfl hneB habsP (lab, S, T0) hmemB
            have hlt : sizeOf T0 <
                sizeOf (SessionType.externalChoice p branches) :=
              sizeOf_SessionType_lt_sizeOf_externalChoice hmemB
            have hNR0 : T0.NoRec := noRec_of_mem_extBranches hNR hmemB
            have hWF0 : T0.WellFormed := wf_of_mem_extBranches hmemB hWF
            exact ih (sizeOf T0) (by omega) T0 Q hlen (Nat.le_refl _) hNR0
              hWF0 hCoreG.toDeep hBad.toDef
          · push Not at habsP
            obtain ⟨m, hmemM, hm1⟩ := habsP
            by_cases hnd : NoDequeueFrom (SessionType.externalChoice p branches) Q
            · obtain ⟨TnD2, ρD2, hTrD2, -⟩ := hD
              cases ρD2 with
              | nil =>
                have heq := overTrTrace_nil_eq hTrD2
                have hQ : Q = ([] : Queue) := (congrArg Prod.snd heq).symm
                rw [hQ] at hmemM
                simp at hmemM
              | cons α ρ' =>
                cases hTrD2 with
                | step hS _ =>
                  cases hS with
                  | dequeue hEq hmem hQd =>
                    injection hEq with hpeq hbeq'
                    subst hpeq
                    subst hbeq'
                    exact absurd ⟨_, _, _, _, _, st_trans.extC hmem, hQd⟩ hnd
                  | specInp hEq hmem hAbs =>
                    injection hEq with hpeq hbeq'
                    subst hpeq
                    subst hbeq'
                    exact (hAbs _ hmemM hm1).elim
                  | sendFresh hEq hST hFresh =>
                    cases hEq
                  | tauUnfold hU => exact Unfold1.absurd_of_NoRec hNR hU
            · obtain ⟨TnD, ρD0, hTrD0, hallD⟩ := hD
              obtain ⟨TnC, QnC, ρC0, hTrC0, hneC0, hendC0, hallC⟩ := hC
              cases ρC0 with
              | nil =>
                have heq := overTrTrace_nil_eq hTrC0
                have hTn : TnC = SessionType.externalChoice p branches :=
                  congrArg Prod.fst heq
                have hQn : QnC = Q := congrArg Prod.snd heq
                subst hTn
                subst hQn
                rcases hendC0 with hT | hI | hA | hR
                · cases hT
                · obtain ⟨branches2, q, lab2, S2, T2, m2, hEq, hmemB2, hmemM2,
                    heqM2⟩ := hI
                  cases hEq
                · obtain ⟨q, branches2, lab0, S0, m0, hEq, hOld, hmeq,
                    habs⟩ := hA
                  cases hEq with
                  | refl =>
                    exact corner_oldest_vs_drain hTrD0 hOld hmeq habs
                · obtain ⟨X, B, _, hEqT, -, -⟩ := hR
                  exact False.elim (by cases hEqT)
              | cons α ρC' =>
                have hTrC0copy := hTrC0
                cases hTrC0 with
                | step hSC hTC2 =>
                  have hStepD := extC_step_is_dequeue hmemM hm1 hSC
                  obtain ⟨Td1, Qd1, labd1, Sd1, hEqA1, hEqS1, hSTd1,
                    hQdd1⟩ := hStepD
                  have hTd1check := Td1
                  cases ρD0 with
                  | nil =>
                    have heq := overTrTrace_nil_eq hTrD0
                    have hQ : Q = ([] : Queue) := (congrArg Prod.snd heq).symm
                    rw [hQ] at hmemM
                    simp at hmemM
                  | cons β ρD' =>
                    have hTrD0copy := hTrD0
                    cases hTrD0
                    case step hSD hTD2 =>
                      obtain ⟨Td0, Qd0, labd0, Sd0, hEqA0, hEqS0, hSTd0,
                        hQdd0⟩ :=
                        extC_step_is_dequeue hmemM hm1 hSD
                      rw [hEqS0] at hSD hTD2
                      rw [hEqS1] at hSC hTC2
                      have hSame :=
                        extC_steps_coincide hWF.1 hmemM hm1 hSD hSC
                      obtain ⟨-, hmidEq⟩ := hSame
                      have hT : Td0 = Td1 := congrArg Prod.fst hmidEq
                      have hQ : Qd0 = Qd1 := congrArg Prod.snd hmidEq
                      have h1D : over_trans_trace (SessionType.externalChoice p branches,
                          Q) [β] (Td0, Qd0) :=
                        over_trans_trace.step hSD (over_trans_trace.refl _)
                      have h1C : over_trans_trace (SessionType.externalChoice p branches,
                          Q) [α] (Td1, Qd1) :=
                        over_trans_trace.step hSC (over_trans_trace.refl _)
                      have hD1 : CanAlwaysDrainInternalDeep Td1 Qd1 := by
                        have hD0 := CanAlwaysDrainInternalDeep.suffix hallD h1D hTD2 (by simp)
                        rw [hT, hQ] at hD0
                        exact hD0
                      have hC1 : CannotAlwaysDrainInternalDeep Td1 Qd1 :=
                        CannotAlwaysDrainInternalDeep.suffix hneC0
                          hendC0 hallC h1C hTC2 (by simp)
                      rw [hT, hQ] at hSD
                      have hNR1 : Td1.NoRec :=
                        over_trans_preserves_norec hSD hNR
                      have hWF1 : Td1.WellFormed :=
                        over_trans_preserves_wf hSD hWF
                      have hshrink : sizeOf Td1 <
                          sizeOf (SessionType.externalChoice p branches) :=
                        over_trans_session_shrink_norec hSD hNR
                      have hlen1 : Qd1.length ≤ n := by
                        have hdrop := Queue.dequeue_length_drop hQdd1
                        omega
                      exact ih (sizeOf Td1) (by omega) Td1 Qd1 hlen1
                        (Nat.le_refl _) hNR1 hWF1 hD1 hC1
        | tVar X =>
          intro _ _ _ hWF _ _
          obtain ⟨-, hCl, -⟩ := hWF
          unfold SessionType.IsClosed at hCl
          have hfv : SessionType.fv (SessionType.tVar X) = [X] := rfl
          rw [hfv] at hCl
          simp at hCl
        | tRec X B =>
          intro _ _ hNR _ _ _
          cases hNR

/-- Forward direction: `Deep` precludes `Cannot` at `NoRec`+`WellFormed`
    states. -/
theorem deep_excl_forward_norec {T : SessionType} {Q : Queue}
    (hNR : T.NoRec) (hWF : T.WellFormed)
    (hD : CanAlwaysDrainInternalDeep T Q)
    (hC : CannotAlwaysDrainInternalDeep T Q) : False :=
  deep_excl_aux_norec (sizeOf T) T Q Q.length (Nat.le_refl _) (Nat.le_refl _) hNR
    hWF hD hC
end DeepExclusion
section DeepComplement

/-- Per-branch disjunctions combine: either some branch takes the
    left, or every branch takes the right. -/
private theorem list_exists_or_forall {α : Type} {P Q : α → Prop}
    {bs : List α} :
    (∀ x ∈ bs, P x ∨ Q x) → (∃ x ∈ bs, P x) ∨ (∀ x ∈ bs, Q x) := by
  classical
  intro h
  by_cases hex : ∃ x ∈ bs, P x
  · obtain ⟨x, hmem, hP⟩ := hex
    exact Or.inl ⟨x, hmem, hP⟩
  · exact Or.inr (fun x hmem => by
      rcases h x hmem with hP | hQ
      · exfalso
        exact hex ⟨x, hmem, hP⟩
      · exact hQ)

/-- Disjunction by size induction: every `NoRec`+`WellFormed` state
    drains deeply or fails deeply (greedy-forward strategy). -/
theorem deep_or_cannot_aux_norec (m : Nat) (T : SessionType) (Q : Queue) (n : Nat) :
    Q.length ≤ n → sizeOf T ≤ m → T.NoRec → T.WellFormed →
    CanAlwaysDrainInternalDeep T Q ∨ CannotAlwaysDrainInternalDeep T Q := by
  revert T Q
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro T Q hlen hsize hNR hWF
    classical
    revert hlen hsize hNR hWF
    cases T with
    | tEnd =>
      intro hlen hsize hNR hWF
      cases Q with
      | nil =>
        refine Or.inl ⟨SessionType.tEnd, [], over_trans_trace.refl _, ?_⟩
        intro Ti Qi σ1 σ2 g1 g2 heq
        cases σ1 with
        | nil =>
          have hST := overTrTrace_nil_eq g1
          cases hST
          refine ⟨?_, ?_, ?_⟩
          · intro branches hEq hneB
            cases hEq
          · intro q branches hEq hneB hnd
            cases hEq
          · intro X B hEq
            cases hEq
        | cons α σ1' =>
          simp at heq
      | cons m0 rest =>
        refine Or.inr ⟨SessionType.tEnd, m0 :: rest, [], over_trans_trace.refl _,
          ?_, ?_, ?_⟩
        · exact List.ne_nil_of_mem (List.mem_cons.mpr (Or.inl rfl))
        · exact Or.inl rfl
        · intro Ti Qi σ1 σ2 g1 g2 heq
          cases σ1 with
          | nil =>
            have hST := overTrTrace_nil_eq g1
            cases hST
            refine ⟨?_, ?_⟩
            · intro branches hEq hneB hfire
              cases hEq
            · intro q branches hEq hneB habs br hmem
              cases hEq
          | cons α ρ1' =>
            simp at heq
    | internalChoice branches =>
      intro hlen hsize hNR hWF
      have hneB : branches ≠ [] :=
        SessionType.WellFormed.ne_of_internalChoice rfl hWF
      by_cases hfire : int_choice_fireable (SessionType.internalChoice branches) Q
        branches
      · have hbr : ∀ (br : Role × Lab × DataSort × SessionType),
            br ∈ branches →
            CanAlwaysDrainInternalDeep br.2.2.2 Q ∨
            CannotAlwaysDrainInternalDeep br.2.2.2 Q := by
          intro br hmemB
          obtain ⟨p, lab, S, T0⟩ := br
          have hlt : sizeOf T0 < sizeOf (SessionType.internalChoice branches) :=
            sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
          have hNR0 : T0.NoRec := noRec_of_mem_intBranches hNR hmemB
          have hWF0 : T0.WellFormed := wf_of_mem_intBranches hmemB hWF
          have hres := ih (sizeOf T0) (by omega) T0 Q hlen (Nat.le_refl _)
            hNR0 hWF0
          exact hres
        by_cases hall : ∀ (br : Role × Lab × DataSort × SessionType),
            br ∈ branches → CanAlwaysDrainInternalDeep br.2.2.2 Q
        · cases branches with
          | nil => exact absurd rfl hneB
          | cons br0 rest =>
            obtain ⟨p0, lab0, S0, T0⟩ := br0
            have hD0 : CanAlwaysDrainInternalDeep T0 Q :=
              hall _ (List.mem_cons.mpr (Or.inl rfl))
            have hFreshW : ∀ (r' : Role) (l' : Lab) (s' : DataSort)
                (U : SessionType),
                (r', l', s', U) ∈ ((p0, lab0, S0, T0) :: rest) →
                ∀ m ∈ Q, m.1 ≠ r' := by
              intro r' l' s' U hmem m hmemM
              exact hfire _ hmem _ hmemM
            have hND : (SessionType.internalChoice
                ((p0, lab0, S0, T0) :: rest)).NoDupl := hWF.1
            have hHI : ∀ (branches2 : List (Role × Lab × DataSort ×
                SessionType)),
                SessionType.internalChoice ((p0, lab0, S0, T0) :: rest) =
                  SessionType.internalChoice branches2 → branches2 ≠ [] →
                ∀ (br : Role × Lab × DataSort × SessionType),
                  br ∈ branches2 → CanAlwaysDrainInternalDeepCore br.2.2.2 Q := by
              intro branches2 hEq hneB2 br hmem2
              cases hEq
              exact (hall _ hmem2).toCore
            have hHE : ∀ (q : Role) (branches2 : List (Lab × DataSort ×
                SessionType)),
                SessionType.internalChoice ((p0, lab0, S0, T0) :: rest) =
                  SessionType.externalChoice q branches2 → branches2 ≠ [] →
                NoDequeueFrom (SessionType.internalChoice
                  ((p0, lab0, S0, T0) :: rest)) Q →
                ∃ (br : Lab × DataSort × SessionType),
                  br ∈ branches2 ∧ CanAlwaysDrainInternalDeepCore br.2.2 Q := by
              intro q branches2 hEq hneB2 hnd
              cases hEq
            exact Or.inl (deep_prepend_send_at_intC hND
              (List.mem_cons.mpr (Or.inl rfl)) hFreshW hD0
              hHI hHE)
        · push Not at hall
          obtain ⟨br, hmemB, hnD⟩ := hall
          rcases hbr br hmemB with hD0 | hC0
          · exact absurd hD0 hnD
          · obtain ⟨p, lab, S, T0⟩ := br
            have hFreshW : ∀ (r' : Role) (l' : Lab) (s' : DataSort)
                (U : SessionType),
                (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r' := by
              intro r' l' s' U hmem m hmemM
              exact hfire _ hmem _ hmemM
            have hCoreB : CannotAlwaysDrainInternalDeepCore T0 Q :=
              hC0.toCore
            have hND : (SessionType.internalChoice branches).NoDupl := hWF.1
            exact Or.inr (cannot_prepend_send_at_intC hND hmemB hFreshW hC0
              hCoreB)
      · have hNB : ¬ int_choice_fireable (SessionType.internalChoice branches) Q
          branches := hfire
        unfold int_choice_fireable at hfire
        push Not at hfire
        obtain ⟨br, hmemB, m, hmemM, heqM⟩ := hfire
        obtain ⟨p, lab, S, T0⟩ := br
        refine Or.inr ⟨SessionType.internalChoice branches, Q, [],
          over_trans_trace.refl _, ?_, ?_, ?_⟩
        · exact List.ne_nil_of_mem hmemM
        · exact Or.inr (Or.inl ⟨branches, p, lab, S, T0, m, rfl, hmemB,
            hmemM, heqM⟩)
        · intro Ti Qi ρ1 ρ2 h1 h2 heq
          cases ρ1 with
          | nil =>
            have hST := overTrTrace_nil_eq h1
            cases hST
            refine ⟨?_, ?_⟩
            · intro branches2 hEq hneB2 hfire2
              cases hEq
              exact absurd hfire2 hNB
            · intro q branches2 hEq hneB2 habs br2 hmem2
              cases hEq
          | cons α ρ1' =>
            simp at heq
    | externalChoice p branches =>
      intro hlen hsize hNR hWF
      have hneB : branches ≠ [] := hWF.1.ne_of_externalChoice
      by_cases habsP : ∀ m ∈ Q, m.1 ≠ p
      · have hbr : ∀ (br : Lab × DataSort × SessionType), br ∈ branches →
            CanAlwaysDrainInternalDeep br.2.2 Q ∨
            CannotAlwaysDrainInternalDeep br.2.2 Q := by
          intro br hmemB
          obtain ⟨lab, S, T0⟩ := br
          have hlt : sizeOf T0 <
              sizeOf (SessionType.externalChoice p branches) :=
            sizeOf_SessionType_lt_sizeOf_externalChoice hmemB
          have hNR0 : T0.NoRec := noRec_of_mem_extBranches hNR hmemB
          have hWF0 : T0.WellFormed := wf_of_mem_extBranches hmemB hWF
          have hres := ih (sizeOf T0) (by omega) T0 Q hlen (Nat.le_refl _)
            hNR0 hWF0
          exact hres
        rcases list_exists_or_forall hbr with ⟨br, hmemB, hD0⟩ | hall
        · obtain ⟨lab, S, T0⟩ := br
          have hCoreG : CanAlwaysDrainInternalDeepCore T0 Q := hD0.toCore
          have hND : (SessionType.externalChoice p branches).NoDupl := hWF.1
          have hHI : ∀ (branches2 : List (Role × Lab × DataSort ×
              SessionType)),
              SessionType.externalChoice p branches =
                SessionType.internalChoice branches2 → branches2 ≠ [] →
            ∀ (br : Role × Lab × DataSort × SessionType),
              br ∈ branches2 → CanAlwaysDrainInternalDeepCore br.2.2.2 Q := by
            intro branches2 hEq hneB2
            cases hEq
          have hHE : ∀ (q : Role) (branches2 : List (Lab × DataSort ×
              SessionType)),
              SessionType.externalChoice p branches =
                SessionType.externalChoice q branches2 → branches2 ≠ [] →
              NoDequeueFrom (SessionType.externalChoice p branches) Q →
              ∃ (br : Lab × DataSort × SessionType),
                br ∈ branches2 ∧ CanAlwaysDrainInternalDeepCore br.2.2 Q := by
            intro q branches2 hEq hneB2 hnd
            cases hEq
            exact ⟨(lab, S, T0), hmemB, hCoreG⟩
          exact Or.inl (deep_prepend_spec_at_extC hND hmemB habsP hD0 hHI
            hHE)
        · cases branches with
          | nil => exact absurd rfl hneB
          | cons br0 rest =>
            obtain ⟨lab0, S0, T0⟩ := br0
            have hC0 : CannotAlwaysDrainInternalDeep T0 Q :=
              hall _ (List.mem_cons.mpr (Or.inl rfl))
            have hAllBad : ∀ (br : Lab × DataSort × SessionType),
                br ∈ ((lab0, S0, T0) :: rest) →
                CannotAlwaysDrainInternalDeepCore br.2.2 Q := by
              intro br hmem
              exact (hall _ hmem).toCore
            have hND : (SessionType.externalChoice p
                ((lab0, S0, T0) :: rest)).NoDupl := hWF.1
            exact Or.inr (cannot_prepend_spec_at_extC hND
              (List.mem_cons.mpr (Or.inl rfl)) habsP hC0
              hAllBad)
      · push Not at habsP
        obtain ⟨m, hmemM, hm1⟩ := habsP
        by_cases hnd : NoDequeueFrom (SessionType.externalChoice p branches) Q
        · have hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
            ¬ over_trans (SessionType.externalChoice p branches, Q) α stq' := by
            intro α stq' hS
            cases hS with
            | dequeue hEq hmem hQd =>
              injection hEq with hpeq hbeq'
              subst hpeq
              subst hbeq'
              exact absurd ⟨_, _, _, _, _, st_trans.extC hmem, hQd⟩ hnd
            | specInp hEq hmem hAbs =>
              injection hEq with hpeq hbeq'
              subst hpeq
              subst hbeq'
              exact (hAbs _ hmemM hm1).elim
            | sendFresh hEq hST hFresh =>
              cases hEq
            | tauUnfold hU => exact Unfold1.absurd_of_NoRec hNR hU
          have hQne : Q ≠ [] := List.ne_nil_of_mem hmemM
          refine Or.inr ⟨SessionType.externalChoice p branches, Q, [],
            over_trans_trace.refl _, hQne, ?_, ?_⟩
          · exact cannot_end_of_nostep_norec hNR hWF hNo
          · intro Ti Qi σ1 σ2 g1 g2 heq
            cases σ1 with
            | nil =>
              have hST := overTrTrace_nil_eq g1
              cases hST
              refine ⟨?_, ?_⟩
              · intro branches2 hEq hneB hfire
                cases hEq
              · intro q branches2 hEq hneB habs2 br hmem2
                cases hEq
                exact (habs2 _ hmemM hm1).elim
            | cons α σ1' =>
              cases g1 with
              | step hS _ => exact (hNo _ _ hS).elim
        · unfold NoDequeueFrom at hnd
          push Not at hnd
          obtain ⟨T', Q', r, lab, S, hSTd, hQdd⟩ := hnd
          cases hSTd with
          | extC hmemSTd =>
            have hStep : over_trans (SessionType.externalChoice p branches, Q)
                (st_label.inp p lab S) (T', Q') :=
              over_trans.dequeue rfl hmemSTd hQdd
            have hshrink : sizeOf T' <
                sizeOf (SessionType.externalChoice p branches) :=
              over_trans_session_shrink_norec hStep hNR
            have hNR' : T'.NoRec := over_trans_preserves_norec hStep hNR
            have hWF' : T'.WellFormed := over_trans_preserves_wf hStep hWF
            have hlen' : Q'.length ≤ n := by
              have hdrop := Queue.dequeue_length_drop hQdd
              omega
            have hres := ih (sizeOf T') (by omega) T' Q' hlen'
              (Nat.le_refl _) hNR' hWF'
            rcases hres with hD1 | hC1
            · have hHI : ∀ (branches2 : List (Role × Lab × DataSort ×
                SessionType)),
                SessionType.externalChoice p branches =
                  SessionType.internalChoice branches2 → branches2 ≠ [] →
                ∀ (br : Role × Lab × DataSort × SessionType),
                  br ∈ branches2 → CanAlwaysDrainInternalDeepCore br.2.2.2 Q := by
                intro branches2 hEq hneB2
                cases hEq
              have hSTW : st_trans (SessionType.externalChoice p branches)
                  (st_label.inp p lab S) T' := st_trans.extC hmemSTd
              have hHE : ∀ (q : Role) (branches2 : List (Lab × DataSort ×
                  SessionType)),
                  SessionType.externalChoice p branches =
                    SessionType.externalChoice q branches2 → branches2 ≠ [] →
                  NoDequeueFrom (SessionType.externalChoice p branches) Q →
                  ∃ (br : Lab × DataSort × SessionType),
                    br ∈ branches2 ∧ CanAlwaysDrainInternalDeepCore br.2.2 Q := by
                intro q branches2 hEq hneB2 hnd2
                exact absurd ⟨_, _, _, _, _, hSTW, hQdd⟩ hnd2
              exact Or.inl (deep_prepend_dequeue_at_extC hWF.1 hmemSTd hQdd hD1
                hHI hHE)
            · have hHI : ∀ (branches2 : List (Role × Lab × DataSort ×
                SessionType)),
                SessionType.externalChoice p branches =
                  SessionType.internalChoice branches2 → branches2 ≠ [] →
                ∀ (br : Role × Lab × DataSort × SessionType),
                  br ∈ branches2 → CanAlwaysDrainInternalDeepCore br.2.2.2 Q := by
                intro branches2 hEq hneB2
                cases hEq
              exact Or.inr (cannot_prepend_dequeue_at_extC hWF.1 hmemSTd hQdd
                hC1)
    | tVar X =>
      intro hlen hsize hNR hWF
      obtain ⟨-, hCl, -⟩ := hWF
      unfold SessionType.IsClosed at hCl
      have hfv : SessionType.fv (SessionType.tVar X) = [X] := rfl
      rw [hfv] at hCl
      simp at hCl
    | tRec X B =>
      intro hlen hsize hNR hWF
      cases hNR

/-- The disjunction: every `NoRec`+`WellFormed` state drains deeply or
    fails deeply. -/
theorem deep_or_cannot_norec {T : SessionType} {Q : Queue}
    (hNR : T.NoRec) (hWF : T.WellFormed) :
    CanAlwaysDrainInternalDeep T Q ∨ CannotAlwaysDrainInternalDeep T Q :=
  deep_or_cannot_aux_norec (sizeOf T) T Q Q.length (Nat.le_refl _) (Nat.le_refl _)
    hNR hWF

/-- The iff: `Deep` holds iff `Cannot` does not, for all `NoRec`
    well-formed session types. -/
theorem deep_iff_not_cannot_norec {T : SessionType} {Q : Queue}
    (hNR : T.NoRec) (hWF : T.WellFormed) :
    CanAlwaysDrainInternalDeep T Q ↔ ¬ CannotAlwaysDrainInternalDeep T Q :=
  ⟨fun hD hC => deep_excl_forward_norec hNR hWF hD hC,
    fun hNC => Or.resolve_right (deep_or_cannot_norec hNR hWF) hNC⟩
end DeepComplement
section MonitorReject

/-- Monitor rejection implies no drain: a well-formed `NoRec` state with no
    accepting monitor cannot drain. Contrapositive of
    `drain_implies_mon_exists_accepts_norec` via the `Deep`/`Cannot`
    complementarity (`deep_or_cannot_norec`). -/
theorem mon_reject_implies_nodrain_norec (T : SessionType) (Q : Queue)
    (hNR : T.NoRec) (hWF : T.WellFormed)
    (hNo : ¬ ∃ M : SessionType, monitor_fold (T, Q) M) :
    CannotAlwaysDrainInternalDeep T Q := by
  rcases deep_or_cannot_norec hNR hWF with hD | hC
  · exfalso
    exact hNo (drain_implies_mon_exists_accepts_norec T Q hNR hWF hD)
  · exact hC
end MonitorReject

