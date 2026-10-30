import Nest.SessionUtils
import Nest.MonitorToolkit
import Nest.NoRec.Counterexamples.ProofUtils
import Nest.NoRec.NoRecEncoder
import Nest.NoRec.DrainCore

/-- Dequeue labels of a classified trace (in order), as monitor tags. -/
def sDeqOf : List (TrKind × st_label) → List ext_tag
  | [] => []
  | ((TrKind.dequeue, α) :: r) => overTagToExt α :: sDeqOf r
  | (_ :: r) => sDeqOf r

/-- Spec/send labels of a classified trace (in order), as monitor tags. -/
def sSpecOf : List (TrKind × st_label) → List ext_tag
  | [] => []
  | ((TrKind.dequeue, _) :: r) => sSpecOf r
  | ((TrKind.tau, _) :: r) => sSpecOf r
  | ((_, α) :: r) => overTagToExt α :: sSpecOf r

/-- Stuck states with nonempty queues admit no drain (refl needs `[]`,
    every step is ruled out). -/
theorem overTrTrace_no_drain_of_nostep {stq : SessionTypeWithQueue}
    (hNo : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
      ¬ over_trans stq α stq')
    (hne : stq.2 ≠ []) :
    ¬ ∃ (T' : SessionType) (ρ : List st_label),
      over_trans_trace stq ρ (T', []) := by
  intro hCon
  obtain ⟨T', ρ, hT⟩ := hCon
  cases hT with
  | refl _ => exact absurd rfl hne
  | step hStep _ => exact hNo _ _ hStep

/-- Dequeued messages of a classified trace, in drain order. -/
def deqMsgsOf : List (TrKind × st_label) → Queue
  | [] => []
  | ((TrKind.dequeue, st_label.inp p lab S) :: r) =>
    QueueMessage.msg p lab S :: deqMsgsOf r
  | ((TrKind.dequeue, st_label.out p lab S) :: r) =>
    QueueMessage.msg p lab S :: deqMsgsOf r
  | ((_ :: r)) => deqMsgsOf r
/-!
# Counterexample: `monitor_accepts_draining_sequence` is false.

Claim (paraphrased): any draining approx-trace `s` to `[]` reorders to
`monS = sDeq ++ sSpec` (dequeue labels first, then spec/send labels) such
that `T` performs the `sDeq` monitor run to `M` with `encTr (T,Q) M`, and
`M` performs the `sSpec` run to some `M'`.

Refuted by `ms_no_shared_endpoint_norec` below. Witness (all roles/labels
distinct strings; `Q = [(p,a,s), (q,b,s)]`):
- `T = extC r [(a → I), (b → Q1), (c → Q1)]`, `I = intC [(q,x → tEnd),
  (r,y → D2)]`, `D2 = extC p [(a → t2)]`, `t2 = extC q [(b → tEnd)]`,
  `Q1 = extC q [(b → P0)]`, `P0 = extC p [(a → tEnd)]`.
- Drain `s = [spec(r,c), deq(q,b), deq(p,a)]` to `(tEnd, [])`:
  `spec` is absent-`r`-safe; both dequeues are base `st_trans` steps with
  successful scans.
- `sDeq`-run (`[(q,b), (p,a)]`, out of queue order): `T -(q,b)-> M1`
  prunes the `a`-branch (`I` rejects `(q,b)` — the `q`-sender kills the
  `hno` side condition), then `M1 -(p,a)-> Mmon = extC r [(b → tEnd),
  (c → tEnd)]`.
- Fold (`[(p,a), (q,b)]`, queue order): `T -(p,a)-> F1` keeps all three
  branches, then `F1 -(q,b)-> Mfold
  = extC r [(a → intC [(r,y → tEnd)]), (b → tEnd), (c → tEnd)]`.
- `Mmon ≠ Mfold`, and both endpoints are unique (monitor-run
  determinism `ms_mon_yes_seq_det`, fold uniqueness
  `encQueueAux_value_unique_norec`), so no shared `M` exists.

Mechanism: prune-then-need divergence — the early `(q,b)`-prefix drops
the `a`-lineage (whose sub-branches reject `(q,b)`), while the
`(p,a)`-first order keeps it; both orders are individually executable
but join differently. The drain still succeeds because dequeues are
on-role base `st_trans` steps at the (unpruned) continuations.

This file is evidence only (not imported by `Nest.lean`); it imports only
`Nest.SessionUtils`.
-/

-- ================================================================
-- Witness types.
-- ================================================================

private def MS_P0 : SessionType :=
  SessionType.externalChoice "p" [("a", "s", SessionType.tEnd)]

private def MS_Q1 : SessionType :=
  SessionType.externalChoice "q" [("b", "s", MS_P0)]

private def MS_t2 : SessionType :=
  SessionType.externalChoice "q" [("b", "s", SessionType.tEnd)]

private def MS_D2 : SessionType :=
  SessionType.externalChoice "p" [("a", "s", MS_t2)]

private def MS_I : SessionType :=
  SessionType.internalChoice
    [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)]

private def MS_T : SessionType :=
  SessionType.externalChoice "r"
    [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)]

private def MS_M1 : SessionType :=
  SessionType.externalChoice "r" [("b", "s", MS_P0), ("c", "s", MS_P0)]

private def MS_Mmon : SessionType :=
  SessionType.externalChoice "r"
    [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)]

private def MS_I' : SessionType :=
  SessionType.internalChoice [("r", "y", "s", MS_t2)]

private def MS_Q1' : SessionType :=
  SessionType.externalChoice "q" [("b", "s", SessionType.tEnd)]

private def MS_F1 : SessionType :=
  SessionType.externalChoice "r"
    [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')]

private def MS_I'' : SessionType :=
  SessionType.internalChoice [("r", "y", "s", SessionType.tEnd)]

private def MS_Mfold : SessionType :=
  SessionType.externalChoice "r"
    [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
      ("c", "s", SessionType.tEnd)]

private def MS_Q : Queue :=
  [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"]

-- ================================================================
-- `T` is nonrec with no duplicate keys.
-- ================================================================

private lemma MS_T_NoRec : MS_T.NoRec := by
  unfold MS_T
  apply SessionType.NoRec.externalChoice
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | h
  · unfold MS_I
    apply SessionType.NoRec.internalChoice
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | h
    · exact SessionType.NoRec.end
    · unfold MS_D2
      apply SessionType.NoRec.externalChoice
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | h
      · unfold MS_t2
        apply SessionType.NoRec.externalChoice
        intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | h
        · exact SessionType.NoRec.end
        · simp at h
      · simp at h
    · simp at h
  · unfold MS_Q1
    apply SessionType.NoRec.externalChoice
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | h
    · unfold MS_P0
      apply SessionType.NoRec.externalChoice
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | h
      · exact SessionType.NoRec.end
      · simp at h
    · simp at h
  · unfold MS_Q1
    apply SessionType.NoRec.externalChoice
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | h
    · unfold MS_P0
      apply SessionType.NoRec.externalChoice
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | h
      · exact SessionType.NoRec.end
      · simp at h
    · simp at h
  · simp at h

private lemma MS_T_NoDupl : MS_T.NoDupl := by
  unfold MS_T
  apply SessionType.NoDupl.externalChoice
  · decide
  · intro h
    cases h
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | h
    · unfold MS_I
      apply SessionType.NoDupl.internalChoice
      · decide
      · intro h
        cases h
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | rfl | h
        · exact SessionType.NoDupl.end
        · unfold MS_D2
          apply SessionType.NoDupl.externalChoice
          · decide
          · intro h
            cases h
          · intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | h
            · unfold MS_t2
              apply SessionType.NoDupl.externalChoice
              · decide
              · intro h
                cases h
              · intro w hw
                simp only [List.mem_cons] at hw
                rcases hw with rfl | h
                · exact SessionType.NoDupl.end
                · simp at h
            · simp at h
        · simp at h
    · unfold MS_Q1
      apply SessionType.NoDupl.externalChoice
      · decide
      · intro h
        cases h
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | h
        · unfold MS_P0
          apply SessionType.NoDupl.externalChoice
          · decide
          · intro h
            cases h
          · intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | h
            · exact SessionType.NoDupl.end
            · simp at h
        · simp at h
    · unfold MS_Q1
      apply SessionType.NoDupl.externalChoice
      · decide
      · intro h
        cases h
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | h
        · unfold MS_P0
          apply SessionType.NoDupl.externalChoice
          · decide
          · intro h
            cases h
          · intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | h
            · exact SessionType.NoDupl.end
            · simp at h
        · simp at h
    · simp at h

private lemma MS_P0_Contractive : MS_P0.Contractive := by
  unfold MS_P0
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact SessionType.Contractive.end

private lemma MS_Q1_Contractive : MS_Q1.Contractive := by
  unfold MS_Q1
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MS_P0_Contractive

private lemma MS_t2_Contractive : MS_t2.Contractive := by
  unfold MS_t2
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact SessionType.Contractive.end

private lemma MS_D2_Contractive : MS_D2.Contractive := by
  unfold MS_D2
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MS_t2_Contractive

private lemma MS_I_Contractive : MS_I.Contractive := by
  unfold MS_I
  apply SessionType.Contractive.internalChoice
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | h
  · exact SessionType.Contractive.end
  · exact MS_D2_Contractive
  · simp at h

private lemma MS_T_Contractive : MS_T.Contractive := by
  unfold MS_T
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | h
  · exact MS_I_Contractive
  · exact MS_Q1_Contractive
  · exact MS_Q1_Contractive
  · simp at h

private lemma MS_T_IsClosed : MS_T.IsClosed := by
  unfold SessionType.IsClosed
  decide

private lemma MS_T_WF : MS_T.WellFormed :=
  ⟨MS_T_NoDupl, MS_T_IsClosed, MS_T_Contractive⟩

private lemma MS_P0_WF : MS_P0.WellFormed := by
  unfold MS_P0 SessionType.WellFormed
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.externalChoice (by decide) (by decide)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl
    exact SessionType.NoDupl.end
  · unfold SessionType.IsClosed
    decide
  · apply SessionType.Contractive.externalChoice
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl
    exact SessionType.Contractive.end

private lemma MS_M1_WF : MS_M1.WellFormed := by
  unfold MS_M1 SessionType.WellFormed
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.externalChoice (by decide) (by decide)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact MS_P0_WF.1
    · exact MS_P0_WF.1
  · unfold SessionType.IsClosed
    decide
  · apply SessionType.Contractive.externalChoice
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact MS_P0_WF.2.2
    · exact MS_P0_WF.2.2

-- ================================================================
-- Non-acceptance facts (`hcover` negative directions).
-- ================================================================

/-- `tEnd` admits no existential yes-transition. -/
private lemma ms_tEndNoExist : ∀ {γ : ext_tag} {T' : SessionType},
    ¬ mon_tr_yes_exist SessionType.tEnd γ T' := by
  intro γ T' h
  cases h with
  | base hb => cases hb

/-- The `a`-branch `I` rejects `(q,b)`: the `q`-sender kills `hno`. -/
private lemma ms_INoQB :
    ¬ ∃ T'', mon_tr_yes_exist MS_I (ext_tag.recv "q" "b" "s") T'' := by
  intro hex
  obtain ⟨T'', hE⟩ := hex
  cases hE with
  | base hb => cases hb
  | pfxInt hne hno _ _ _ _ =>
    exact absurd rfl
      (hno "q" "x" "s" _ (List.mem_cons.mpr (Or.inl rfl)))

-- ================================================================
-- Classified traces (`TrKind`, `ClassTr`, `sDeqOf`, `sSpecOf`,
-- `classForget`): use the public ports in `Nest.NoRec.Counterexamples.ProofUtils`
-- (transcribed from this file in Step 1); the local copies were removed on importing
-- it for `CanAlwaysDrainInternalDeep` (robust swap refutation below).
-- ================================================================

-- ================================================================
-- Monitor steps (maximal prefix derivations over concrete lists).
-- Targets are written with literal branch lists; use-site coercions to
-- the `MS_*` defs are definitional.
-- ================================================================

/-- `P0 -(p,a)-> tEnd` (base, maximal pair). -/
private lemma ms_P0pa :
    mon_tr_yes MS_P0 (ext_tag.recv "p" "a" "s") SessionType.tEnd := by
  have huniq : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", SessionType.tEnd)]) := by
    decide
  have hmem : ("a", "s", SessionType.tEnd) ∈
      [("a", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hb : mon_tr_yes_base MS_P0 (ext_tag.recv "p" "a" "s") SessionType.tEnd :=
    mon_tr_yes_base.extC huniq hmem
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- `P3b`: `Q1 -(p,a)-> Q1'`. -/
private lemma MS_P3b : mon_tr_yes
    (SessionType.externalChoice "q" [("b", "s", MS_P0)])
    (ext_tag.recv "p" "a" "s")
    (SessionType.externalChoice "q" [("b", "s", SessionType.tEnd)]) := by
  obtain ⟨hE, hM⟩ := ms_P0pa
  have hpair : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", MS_P0)]) := by
    decide
  have hmemB0 : ("b", "s", MS_P0) ∈ [("b", "s", MS_P0)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0 : ("b", "s", SessionType.tEnd) ∈
      [("b", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hne : [("b", "s", MS_P0)] ≠ [] ∧
      [("b", "s", SessionType.tEnd)] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0, List.ne_nil_of_mem hmemK0⟩
  have hNodupKept : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => x.1)
      [("b", "s", SessionType.tEnd)]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", SessionType.tEnd)]) (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", MS_P0)]) := by
    decide
  have hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ [("b", "s", MS_P0)] →
      (l, s, T1) ∈ [("b", "s", SessionType.tEnd)] →
      mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1 := by
    intro T0 T1 l s hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩
    have hT0eq : T0 = MS_P0 :=
      unique_target_of_nodup_ext hpair hmemB hmemB0
    subst T0
    exact hE
  have hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
      (hmemB : (l, s, T0) ∈ [("b", "s", MS_P0)])
      (hmemK : (l, s, T1) ∈ [("b", "s", SessionType.tEnd)])
      (hsub : mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 l s hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩
    have hT0eq : T0 = MS_P0 :=
      unique_target_of_nodup_ext hpair hmemB hmemB0
    subst T0
    cases proof_irrel hsub hE
    exact hM
  have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
      (l, s, T0) ∈ [("b", "s", MS_P0)] →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1) →
      ∃ T1, (l, s, T1) ∈ [("b", "s", SessionType.tEnd)] := by
    intro l s T0 hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩
    exact ⟨SessionType.tEnd, hmemK0⟩
  have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈ [("b", "s", SessionType.tEnd)] →
      ∃ T0, (l, s, T0) ∈ [("b", "s", MS_P0)] := by
    intro l s T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩
    exact ⟨MS_P0, hmemB0⟩
  exact ⟨mon_tr_yes_exist.pfxExt hne (show ("p" : Role) ≠ "q" from by decide)
      rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxExt (hne := hne)
      (hneq := show ("p" : Role) ≠ "q" from by decide) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- `P3a`: `I -(p,a)-> I'`. -/
private lemma MS_P3a : mon_tr_yes
    (SessionType.internalChoice
      [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)])
    (ext_tag.recv "p" "a" "s")
    (SessionType.internalChoice [("r", "y", "s", MS_t2)]) := by
  have huniqD2 : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_t2)]) := by
    decide
  have hmemD2 : ("a", "s", MS_t2) ∈ [("a", "s", MS_t2)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hbD2 : mon_tr_yes_base MS_D2 (ext_tag.recv "p" "a" "s") MS_t2 :=
    mon_tr_yes_base.extC huniqD2 hmemD2
  have hbD2E : mon_tr_yes_exist MS_D2 (ext_tag.recv "p" "a" "s") MS_t2 :=
    mon_tr_yes_exist.base hbD2
  have hbD2M : mon_tr_yes_max_deriv hbD2E := @mon_tr_yes_max_deriv.base _ _ _ hbD2
  have htriple : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)]) := by
    decide
  have hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort) (T0 : SessionType),
      (p', lab', S', T0) ∈
        [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)] →
      "p" ≠ p' := by
    intro p' lab' S' T0 hmemB
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · decide
    · decide
  have hall : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort),
      (r', l', s', T0') ∈
        [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)] →
      (r', l', s', T1) ∈ [("r", "y", "s", MS_t2)] →
      mon_tr_yes_exist T0' (ext_tag.recv "p" "a" "s") T1 := by
    intro T0' T1 r' l' s' hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    have hT0eq : T0' = MS_D2 := unique_target_of_nodup_int htriple hmemB
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    subst T0'
    exact hbD2E
  have hallMax : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort)
      (hmemB : (r', l', s', T0') ∈
        [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)])
      (hmemK : (r', l', s', T1) ∈ [("r", "y", "s", MS_t2)])
      (hsub : mon_tr_yes_exist T0' (ext_tag.recv "p" "a" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0' T1 r' l' s' hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    have hT0eq : T0' = MS_D2 := unique_target_of_nodup_int htriple hmemB
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    subst T0'
    cases proof_irrel hsub hbD2E
    exact hbD2M
  have hcover : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T0' : SessionType),
      (r', l', s', T0') ∈
        [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)] →
      (∃ T1, mon_tr_yes_exist T0' (ext_tag.recv "p" "a" "s") T1) →
      ∃ T1, (r', l', s', T1) ∈ [("r", "y", "s", MS_t2)] := by
    intro r' l' s' T0' hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨T1, hE⟩ := hex
      exact absurd hE ms_tEndNoExist
    · exact ⟨MS_t2, List.mem_cons.mpr (Or.inl rfl)⟩
  have hkey : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T1 : SessionType),
      (r', l', s', T1) ∈ [("r", "y", "s", MS_t2)] →
      ∃ T0', (r', l', s', T0') ∈
        [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)] := by
    intro r' l' s' T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨MS_D2, List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inl rfl)))⟩
  have hmemB0 : ("q", "x", "s", SessionType.tEnd) ∈
      [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0 : ("r", "y", "s", MS_t2) ∈ [("r", "y", "s", MS_t2)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hne : [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)] ≠ [] ∧
      [("r", "y", "s", MS_t2)] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0, List.ne_nil_of_mem hmemK0⟩
  have hNodupKept : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
      [("r", "y", "s", MS_t2)]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("r", "y", "s", MS_t2)]) (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("q", "x", "s", SessionType.tEnd), ("r", "y", "s", MS_D2)]) := by
    decide
  exact ⟨mon_tr_yes_exist.pfxInt hne hno rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxInt (hne := hne) (hno := hno) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- `P1`: `T -(q,b)-> M1-shape` (prunes the `a`-branch). -/
private lemma ms_Q1qb :
    mon_tr_yes MS_Q1 (ext_tag.recv "q" "b" "s") MS_P0 := by
  have huniq : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", MS_P0)]) := by
    decide
  have hmem : ("b", "s", MS_P0) ∈ [("b", "s", MS_P0)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hb : mon_tr_yes_base MS_Q1 (ext_tag.recv "q" "b" "s") MS_P0 :=
    mon_tr_yes_base.extC huniq hmem
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- `Q1' -(q,b)-> tEnd` (base, maximal pair). -/
private lemma ms_Q1pqb :
    mon_tr_yes MS_Q1' (ext_tag.recv "q" "b" "s") SessionType.tEnd := by
  have huniq : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", SessionType.tEnd)]) := by
    decide
  have hmem : ("b", "s", SessionType.tEnd) ∈
      [("b", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hb : mon_tr_yes_base MS_Q1' (ext_tag.recv "q" "b" "s") SessionType.tEnd :=
    mon_tr_yes_base.extC huniq hmem
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- `t2 -(q,b)-> tEnd` (base, maximal pair). -/
private lemma ms_t2qb :
    mon_tr_yes MS_t2 (ext_tag.recv "q" "b" "s") SessionType.tEnd := by
  have huniq : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", SessionType.tEnd)]) := by
    decide
  have hmem : ("b", "s", SessionType.tEnd) ∈
      [("b", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hb : mon_tr_yes_base MS_t2 (ext_tag.recv "q" "b" "s") SessionType.tEnd :=
    mon_tr_yes_base.extC huniq hmem
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- `P1`: `T -(q,b)-> M1-shape` (prunes the `a`-branch). -/
private lemma MS_P1 : mon_tr_yes
    (SessionType.externalChoice "r"
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)])
    (ext_tag.recv "q" "b" "s")
    (SessionType.externalChoice "r" [("b", "s", MS_P0), ("c", "s", MS_P0)]) := by
  obtain ⟨hE, hM⟩ := ms_Q1qb
  have hpair : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)]) := by
    decide
  have hmemB0b : ("b", "s", MS_Q1) ∈
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hmemB0c : ("c", "s", MS_Q1) ∈
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] :=
    List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have hmemK0b : ("b", "s", MS_P0) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0c : ("c", "s", MS_P0) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hne : [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] ≠ [] ∧
      [("b", "s", MS_P0), ("c", "s", MS_P0)] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0b, List.ne_nil_of_mem hmemK0b⟩
  have hNodupKept : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => x.1)
      [("b", "s", MS_P0), ("c", "s", MS_P0)]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", MS_P0), ("c", "s", MS_P0)]) (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)]) := by
    decide
  have hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈
        [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] →
      (l, s, T1) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] →
      mon_tr_yes_exist T0 (ext_tag.recv "q" "b" "s") T1 := by
    intro T0 T1 l s hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hT0eq : T0 = MS_Q1 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0b
      subst T0
      exact hE
    · have hT0eq : T0 = MS_Q1 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0c
      subst T0
      exact hE
  have hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
      (hmemB : (l, s, T0) ∈
        [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)])
      (hmemK : (l, s, T1) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)])
      (hsub : mon_tr_yes_exist T0 (ext_tag.recv "q" "b" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 l s hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hT0eq : T0 = MS_Q1 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0b
      subst T0
      cases proof_irrel hsub hE
      exact hM
    · have hT0eq : T0 = MS_Q1 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0c
      subst T0
      cases proof_irrel hsub hE
      exact hM
  have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
      (l, s, T0) ∈
        [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "q" "b" "s") T1) →
      ∃ T1, (l, s, T1) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] := by
    intro l s T0 hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact absurd hex ms_INoQB
    · exact ⟨MS_P0, hmemK0b⟩
    · exact ⟨MS_P0, hmemK0c⟩
  have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] →
      ∃ T0, (l, s, T0) ∈
        [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] := by
    intro l s T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨MS_Q1, hmemB0b⟩
    · exact ⟨MS_Q1, hmemB0c⟩
  exact ⟨mon_tr_yes_exist.pfxExt hne (show ("q" : Role) ≠ "r" from by decide)
      rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxExt (hne := hne)
      (hneq := show ("q" : Role) ≠ "r" from by decide) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- `P2`: `M1-shape -(p,a)-> Mmon-shape`. -/
private lemma MS_P2 : mon_tr_yes
    (SessionType.externalChoice "r" [("b", "s", MS_P0), ("c", "s", MS_P0)])
    (ext_tag.recv "p" "a" "s")
    (SessionType.externalChoice "r"
      [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)]) := by
  obtain ⟨hE, hM⟩ := ms_P0pa
  have hpair : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", MS_P0), ("c", "s", MS_P0)]) := by
    decide
  have hmemB0b : ("b", "s", MS_P0) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemB0c : ("c", "s", MS_P0) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hmemK0b : ("b", "s", SessionType.tEnd) ∈
      [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0c : ("c", "s", SessionType.tEnd) ∈
      [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hne : [("b", "s", MS_P0), ("c", "s", MS_P0)] ≠ [] ∧
      [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0b, List.ne_nil_of_mem hmemK0b⟩
  have hNodupKept : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => x.1)
      [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)])
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", MS_P0), ("c", "s", MS_P0)]) := by
    decide
  have hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] →
      (l, s, T1) ∈
        [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)] →
      mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1 := by
    intro T0 T1 l s hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hT0eq : T0 = MS_P0 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0b
      subst T0
      exact hE
    · have hT0eq : T0 = MS_P0 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0c
      subst T0
      exact hE
  have hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
      (hmemB : (l, s, T0) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)])
      (hmemK : (l, s, T1) ∈
        [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)])
      (hsub : mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 l s hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hT0eq : T0 = MS_P0 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0b
      subst T0
      cases proof_irrel hsub hE
      exact hM
    · have hT0eq : T0 = MS_P0 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0c
      subst T0
      cases proof_irrel hsub hE
      exact hM
  have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
      (l, s, T0) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1) →
      ∃ T1, (l, s, T1) ∈
        [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)] := by
    intro l s T0 hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨SessionType.tEnd, hmemK0b⟩
    · exact ⟨SessionType.tEnd, hmemK0c⟩
  have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈
        [("b", "s", SessionType.tEnd), ("c", "s", SessionType.tEnd)] →
      ∃ T0, (l, s, T0) ∈ [("b", "s", MS_P0), ("c", "s", MS_P0)] := by
    intro l s T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨MS_P0, hmemB0b⟩
    · exact ⟨MS_P0, hmemB0c⟩
  exact ⟨mon_tr_yes_exist.pfxExt hne (show ("p" : Role) ≠ "r" from by decide)
      rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxExt (hne := hne)
      (hneq := show ("p" : Role) ≠ "r" from by decide) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- `P3`: `T -(p,a)-> F1-shape` (keeps everything). -/
private lemma MS_P3 : mon_tr_yes
    (SessionType.externalChoice "r"
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)])
    (ext_tag.recv "p" "a" "s")
    (SessionType.externalChoice "r"
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')]) := by
  obtain ⟨hEa, hMa⟩ := MS_P3a
  obtain ⟨hEb, hMb⟩ := MS_P3b
  have hpair : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)]) := by
    decide
  have hmemB0a : ("a", "s", MS_I) ∈
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemB0b : ("b", "s", MS_Q1) ∈
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hmemB0c : ("c", "s", MS_Q1) ∈
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] :=
    List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have hmemK0a : ("a", "s", MS_I') ∈
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0b : ("b", "s", MS_Q1') ∈
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hmemK0c : ("c", "s", MS_Q1') ∈
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] :=
    List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have hne : [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] ≠ [] ∧
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0a, List.ne_nil_of_mem hmemK0a⟩
  have hNodupKept : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => x.1)
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')])
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)]) := by
    decide
  have hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈
        [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] →
      (l, s, T1) ∈
        [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] →
      mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1 := by
    intro T0 T1 l s hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hT0eq : T0 = MS_I :=
        unique_target_of_nodup_ext hpair hmemB hmemB0a
      subst T0
      exact hEa
    · have hT0eq : T0 = MS_Q1 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0b
      subst T0
      exact hEb
    · have hT0eq : T0 = MS_Q1 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0c
      subst T0
      exact hEb
  have hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
      (hmemB : (l, s, T0) ∈
        [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)])
      (hmemK : (l, s, T1) ∈
        [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')])
      (hsub : mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 l s hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hT0eq : T0 = MS_I :=
        unique_target_of_nodup_ext hpair hmemB hmemB0a
      subst T0
      cases proof_irrel hsub hEa
      exact hMa
    · have hT0eq : T0 = MS_Q1 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0b
      subst T0
      cases proof_irrel hsub hEb
      exact hMb
    · have hT0eq : T0 = MS_Q1 :=
        unique_target_of_nodup_ext hpair hmemB hmemB0c
      subst T0
      cases proof_irrel hsub hEb
      exact hMb
  have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
      (l, s, T0) ∈
        [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "p" "a" "s") T1) →
      ∃ T1, (l, s, T1) ∈
        [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] := by
    intro l s T0 hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨MS_I', hmemK0a⟩
    · exact ⟨MS_Q1', hmemK0b⟩
    · exact ⟨MS_Q1', hmemK0c⟩
  have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈
        [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] →
      ∃ T0, (l, s, T0) ∈
        [("a", "s", MS_I), ("b", "s", MS_Q1), ("c", "s", MS_Q1)] := by
    intro l s T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨MS_I, hmemB0a⟩
    · exact ⟨MS_Q1, hmemB0b⟩
    · exact ⟨MS_Q1, hmemB0c⟩
  exact ⟨mon_tr_yes_exist.pfxExt hne (show ("p" : Role) ≠ "r" from by decide)
      rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxExt (hne := hne)
      (hneq := show ("p" : Role) ≠ "r" from by decide) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- `P4a`: `I' -(q,b)-> I''`. -/
private lemma MS_P4a : mon_tr_yes
    (SessionType.internalChoice [("r", "y", "s", MS_t2)])
    (ext_tag.recv "q" "b" "s")
    (SessionType.internalChoice [("r", "y", "s", SessionType.tEnd)]) := by
  obtain ⟨hE, hM⟩ := ms_t2qb
  have htriple : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("r", "y", "s", MS_t2)]) := by
    decide
  have hmemB0 : ("r", "y", "s", MS_t2) ∈ [("r", "y", "s", MS_t2)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0 : ("r", "y", "s", SessionType.tEnd) ∈
      [("r", "y", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hne : [("r", "y", "s", MS_t2)] ≠ [] ∧
      [("r", "y", "s", SessionType.tEnd)] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0, List.ne_nil_of_mem hmemK0⟩
  have hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort) (T0 : SessionType),
      (p', lab', S', T0) ∈ [("r", "y", "s", MS_t2)] → "q" ≠ p' := by
    intro p' lab' S' T0 hmemB
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩
    decide
  have hNodupKept : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
      [("r", "y", "s", SessionType.tEnd)]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("r", "y", "s", SessionType.tEnd)]) (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("r", "y", "s", MS_t2)]) := by
    decide
  have hall : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort),
      (r', l', s', T0') ∈ [("r", "y", "s", MS_t2)] →
      (r', l', s', T1) ∈ [("r", "y", "s", SessionType.tEnd)] →
      mon_tr_yes_exist T0' (ext_tag.recv "q" "b" "s") T1 := by
    intro T0' T1 r' l' s' hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    have hT0eq : T0' = MS_t2 :=
      unique_target_of_nodup_int htriple hmemB hmemB0
    subst T0'
    exact hE
  have hallMax : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort)
      (hmemB : (r', l', s', T0') ∈ [("r", "y", "s", MS_t2)])
      (hmemK : (r', l', s', T1) ∈ [("r", "y", "s", SessionType.tEnd)])
      (hsub : mon_tr_yes_exist T0' (ext_tag.recv "q" "b" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0' T1 r' l' s' hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    have hT0eq : T0' = MS_t2 :=
      unique_target_of_nodup_int htriple hmemB hmemB0
    subst T0'
    cases proof_irrel hsub hE
    exact hM
  have hcover : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T0' : SessionType),
      (r', l', s', T0') ∈ [("r", "y", "s", MS_t2)] →
      (∃ T1, mon_tr_yes_exist T0' (ext_tag.recv "q" "b" "s") T1) →
      ∃ T1, (r', l', s', T1) ∈ [("r", "y", "s", SessionType.tEnd)] := by
    intro r' l' s' T0' hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨SessionType.tEnd, hmemK0⟩
  have hkey : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T1 : SessionType),
      (r', l', s', T1) ∈ [("r", "y", "s", SessionType.tEnd)] →
      ∃ T0', (r', l', s', T0') ∈ [("r", "y", "s", MS_t2)] := by
    intro r' l' s' T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨MS_t2, hmemB0⟩
  exact ⟨mon_tr_yes_exist.pfxInt hne hno rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxInt (hne := hne) (hno := hno) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- `P4`: `F1-shape -(q,b)-> Mfold-shape`. -/
private lemma MS_P4 : mon_tr_yes
    (SessionType.externalChoice "r"
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')])
    (ext_tag.recv "q" "b" "s")
    (SessionType.externalChoice "r"
      [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
        ("c", "s", SessionType.tEnd)]) := by
  obtain ⟨hEa, hMa⟩ := MS_P4a
  obtain ⟨hEb, hMb⟩ := ms_Q1pqb
  have hpair : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')]) := by
    decide
  have hmemB0a : ("a", "s", MS_I') ∈
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemB0b : ("b", "s", MS_Q1') ∈
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hmemB0c : ("c", "s", MS_Q1') ∈
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] :=
    List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have hmemK0a : ("a", "s", MS_I'') ∈
      [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
        ("c", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0b : ("b", "s", SessionType.tEnd) ∈
      [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
        ("c", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hmemK0c : ("c", "s", SessionType.tEnd) ∈
      [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
        ("c", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
  have hne : [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] ≠ [] ∧
      [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
        ("c", "s", SessionType.tEnd)] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0a, List.ne_nil_of_mem hmemK0a⟩
  have hNodupKept : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => x.1)
      [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
        ("c", "s", SessionType.tEnd)]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
        ("c", "s", SessionType.tEnd)]) (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')]) := by
    decide
  have hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈
        [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] →
      (l, s, T1) ∈
        [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
          ("c", "s", SessionType.tEnd)] →
      mon_tr_yes_exist T0 (ext_tag.recv "q" "b" "s") T1 := by
    intro T0 T1 l s hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hT0eq : T0 = MS_I' :=
        unique_target_of_nodup_ext hpair hmemB hmemB0a
      subst T0
      exact hEa
    · have hT0eq : T0 = MS_Q1' :=
        unique_target_of_nodup_ext hpair hmemB hmemB0b
      subst T0
      exact hEb
    · have hT0eq : T0 = MS_Q1' :=
        unique_target_of_nodup_ext hpair hmemB hmemB0c
      subst T0
      exact hEb
  have hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
      (hmemB : (l, s, T0) ∈
        [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')])
      (hmemK : (l, s, T1) ∈
        [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
          ("c", "s", SessionType.tEnd)])
      (hsub : mon_tr_yes_exist T0 (ext_tag.recv "q" "b" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 l s hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hT0eq : T0 = MS_I' :=
        unique_target_of_nodup_ext hpair hmemB hmemB0a
      subst T0
      cases proof_irrel hsub hEa
      exact hMa
    · have hT0eq : T0 = MS_Q1' :=
        unique_target_of_nodup_ext hpair hmemB hmemB0b
      subst T0
      cases proof_irrel hsub hEb
      exact hMb
    · have hT0eq : T0 = MS_Q1' :=
        unique_target_of_nodup_ext hpair hmemB hmemB0c
      subst T0
      cases proof_irrel hsub hEb
      exact hMb
  have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
      (l, s, T0) ∈
        [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "q" "b" "s") T1) →
      ∃ T1, (l, s, T1) ∈
        [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
          ("c", "s", SessionType.tEnd)] := by
    intro l s T0 hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨MS_I'', hmemK0a⟩
    · exact ⟨SessionType.tEnd, hmemK0b⟩
    · exact ⟨SessionType.tEnd, hmemK0c⟩
  have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈
        [("a", "s", MS_I''), ("b", "s", SessionType.tEnd),
          ("c", "s", SessionType.tEnd)] →
      ∃ T0, (l, s, T0) ∈
        [("a", "s", MS_I'), ("b", "s", MS_Q1'), ("c", "s", MS_Q1')] := by
    intro l s T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨MS_I', hmemB0a⟩
    · exact ⟨MS_Q1', hmemB0b⟩
    · exact ⟨MS_Q1', hmemB0c⟩
  exact ⟨mon_tr_yes_exist.pfxExt hne (show ("q" : Role) ≠ "r" from by decide)
      rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxExt (hne := hne)
      (hneq := show ("q" : Role) ≠ "r" from by decide) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

-- ================================================================
-- The drain and its label sequences.
-- ================================================================

private def MS_ks : List (TrKind × st_label) :=
  [(TrKind.spec, st_label.inp "r" "c" "s"),
    (TrKind.dequeue, st_label.inp "q" "b" "s"),
    (TrKind.dequeue, st_label.inp "p" "a" "s")]

private lemma MS_hSTa : st_trans MS_T (st_label.inp "r" "c" "s") MS_Q1 :=
  st_trans.extC (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))

private lemma MS_hAbs : ∀ m ∈ MS_Q, m.1 ≠ "r" := by
  intro m hm
  simp only [MS_Q, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl
  · decide
  · decide

private lemma MS_hSTb : st_trans MS_Q1 (st_label.inp "q" "b" "s") MS_P0 :=
  st_trans.extC (List.mem_cons.mpr (Or.inl rfl))

private lemma MS_hQb : Queue.dequeue MS_Q (QueueMessage.msg "q" "b" "s") =
    some [QueueMessage.msg "p" "a" "s"] := by
  decide

private lemma MS_hSTc :
    st_trans MS_P0 (st_label.inp "p" "a" "s") SessionType.tEnd :=
  st_trans.extC (List.mem_cons.mpr (Or.inl rfl))

private lemma MS_hQc : Queue.dequeue [QueueMessage.msg "p" "a" "s"]
    (QueueMessage.msg "p" "a" "s") = some [] := by
  decide

private lemma MS_hTr :
    ClassTr (MS_T, MS_Q) MS_ks (SessionType.tEnd, []) :=
  ClassTr.spec MS_hSTa MS_hAbs
    (ClassTr.deq MS_hSTb MS_hQb
      (ClassTr.deq MS_hSTc MS_hQc (ClassTr.refl _)))

private lemma MS_eDeq : sDeqOf MS_ks =
    [ext_tag.recv "q" "b" "s", ext_tag.recv "p" "a" "s"] := by
  decide

private lemma MS_eSpec : sSpecOf MS_ks = [ext_tag.recv "r" "c" "s"] := by
  decide

-- ================================================================
-- The two runs, the fold, and uniqueness.
-- ================================================================

/-- `sDeq`-run endpoint. -/
private lemma MS_run : mon_yes_seq MS_T
    [ext_tag.recv "q" "b" "s", ext_tag.recv "p" "a" "s"] MS_Mmon := by
  have hY1 : mon_tr_yes MS_T (ext_tag.recv "q" "b" "s") MS_M1 := MS_P1
  have hY2 : mon_tr_yes MS_M1 (ext_tag.recv "p" "a" "s") MS_Mmon := MS_P2
  exact mon_yes_seq.step hY1 (mon_yes_seq.step hY2 (mon_yes_seq.refl _))

/-- Fold endpoint. -/
private lemma MS_fold : monitor_fold_aux MS_Q MS_T MS_Mfold := by
  have hY1 : mon_tr_yes MS_T (ext_tag.recv "p" "a" "s") MS_F1 := MS_P3
  have hY2 : mon_tr_yes MS_F1 (ext_tag.recv "q" "b" "s") MS_Mfold := MS_P4
  show ∃ T_mid, mon_tr_yes MS_T (ext_tag.recv "p" "a" "s") T_mid ∧
    monitor_fold_aux [QueueMessage.msg "q" "b" "s"] T_mid MS_Mfold
  exact ⟨MS_F1, hY1, MS_Mfold, hY2, rfl⟩

/-- Monitor runs are deterministic (`WellFormed` source). -/
private lemma ms_mon_yes_seq_det {T M1 M2 : SessionType} {ρ : List ext_tag}
    (hWF : T.WellFormed)
    (h1 : mon_yes_seq T ρ M1) (h2 : mon_yes_seq T ρ M2) : M1 = M2 := by
  induction h1 generalizing M2 with
  | refl =>
    cases h2
    rfl
  | step hY1 _ ih =>
    cases h2 with
    | step hY2 h2t =>
      have hEq := mon_tr_yes_target_unique hWF hY1 hY2
      subst hEq
      have hWFm := mon_tr_yes_preserves_wf hY1 hWF
      exact ih hWFm h2t

/-- The endpoints differ. -/
private lemma ms_ne : MS_Mmon ≠ MS_Mfold := by
  intro h
  injection h with hR hL
  injection hL with hE _
  have hb : ("b" : Lab) = "a" := congrArg Prod.fst hE
  exact absurd hb (by decide)

/-- Certified refutation: the drain's `sDeq`-run and its fold never share
    an endpoint (which already refutes the full claim — the `sSpec` run
    is an extra conjunct). -/
theorem ms_no_shared_endpoint_norec :
    ∃ (T : SessionType) (Q : Queue) (ks : List (TrKind × st_label))
      (T' : SessionType),
      T.NoRec ∧ T.NoDupl ∧
      ClassTr (T, Q) ks (T', []) ∧
      sDeqOf ks = [ext_tag.recv "q" "b" "s", ext_tag.recv "p" "a" "s"] ∧
      sSpecOf ks = [ext_tag.recv "r" "c" "s"] ∧
      (∀ M : SessionType, mon_yes_seq T (sDeqOf ks) M → monitor_fold (T, Q) M →
        False) := by
  refine ⟨MS_T, MS_Q, MS_ks, SessionType.tEnd, MS_T_NoRec, MS_T_NoDupl,
    MS_hTr, MS_eDeq, MS_eSpec, ?_⟩
  intro M hR hF
  rw [MS_eDeq] at hR
  have hF' : monitor_fold_aux MS_Q MS_T M := hF
  have e1 : MS_Mmon = M := ms_mon_yes_seq_det MS_T_WF MS_run hR
  have e2 : MS_Mfold = M :=
    monitor_fold_aux_value_unique MS_Q MS_T MS_Mfold M MS_T_WF MS_fold hF'
  have e : MS_Mmon = MS_Mfold := e1.trans e2.symm
  exact absurd e ms_ne

/-- Certified refutation with the fold hypothesis: even when `(T,Q)` folds
    (witnessed below by `MS_fold`), the drain's `sDeq`-run and the fold
    never share an endpoint — so the strengthened
    `monitor_accepts_draining_sequence` (fold `M` + drain to `[]` implies
    the `sDeq` run reaches that same `M`, plus an `sSpec` run after it)
    is already false at its first conjunct. The `sSpec` run is moot. -/
theorem ms_fold_hyp_still_false_norec :
    ∃ (T : SessionType) (Q : Queue) (ks : List (TrKind × st_label))
      (T' Mf : SessionType),
      T.NoRec ∧ T.NoDupl ∧
      monitor_fold (T, Q) Mf ∧
      ClassTr (T, Q) ks (T', []) ∧
      sDeqOf ks = [ext_tag.recv "q" "b" "s", ext_tag.recv "p" "a" "s"] ∧
      sSpecOf ks = [ext_tag.recv "r" "c" "s"] ∧
      (∀ M : SessionType, mon_yes_seq T (sDeqOf ks) M → monitor_fold (T, Q) M →
        False) := by
  refine ⟨MS_T, MS_Q, MS_ks, SessionType.tEnd, MS_Mfold, MS_T_NoRec,
    MS_T_NoDupl, MS_fold, MS_hTr, MS_eDeq, MS_eSpec, ?_⟩
  intro M hR hF
  rw [MS_eDeq] at hR
  have hF' : monitor_fold_aux MS_Q MS_T M := hF
  have e1 : MS_Mmon = M := ms_mon_yes_seq_det MS_T_WF MS_run hR
  have e2 : MS_Mfold = M :=
    monitor_fold_aux_value_unique MS_Q MS_T MS_Mfold M MS_T_WF MS_fold hF'
  have e : MS_Mmon = MS_Mfold := e1.trans e2.symm
  exact absurd e ms_ne

/-- A foldability-flavoured variant of the always-drain refutation:
    assuming the queue folds adds nothing — the same witness satisfies the
    hypothesis (`MS_fold`) while the `sDeq`-run endpoint (`MS_Mmon`) and the
    fold endpoint (`MS_Mfold`) diverge. Stated with plain `∃ Mf, monitor_fold`
    to keep this file's `Basic`-only import. -/
theorem ms_fold_version_false_norec :
    ∃ (T : SessionType) (Q : Queue) (ks : List (TrKind × st_label))
      (T' : SessionType),
      T.NoRec ∧ T.NoDupl ∧
      (∃ Mf, monitor_fold (T, Q) Mf) ∧
      ClassTr (T, Q) ks (T', []) ∧
      sDeqOf ks = [ext_tag.recv "q" "b" "s", ext_tag.recv "p" "a" "s"] ∧
      sSpecOf ks = [ext_tag.recv "r" "c" "s"] ∧
      (∀ M : SessionType, mon_yes_seq T (sDeqOf ks) M → monitor_fold (T, Q) M →
        False) := by
  obtain ⟨T, Q, ks, T', Mf, hNR, hND, hF, hTr, hDeq, hSpec, hNo⟩ :=
    ms_fold_hyp_still_false_norec
  exact ⟨T, Q, ks, T', hNR, hND, ⟨Mf, hF⟩, hTr, hDeq, hSpec, hNo⟩

/-- No unconditional distinct-role dequeue diamond: same-endpoint
    commutation of two `recv` yes-steps with different roles is FALSE in
    general. Witness: `MS_P3`/`MS_P4` give the `(p,a)`-then-`(q,b)` run
    `T ⇒ F1 ⇒ Mfold`; a diamond would complete it to the swapped order
    ending at `Mfold`, but determinism pins the swapped run's midpoint to
    `M1` (`MS_P1`) and its endpoint against `MS_P2` to `Mmon ≠ Mfold`
    (`ms_ne`). Consistent with the banked conditional diamonds, whose
    shape premises fail exactly here (`T = extC r`, first label off-role).
    This refutes the "commute Q-runs into sDeq-runs" step of the
    `monitor_accepts_draining_sequence` amendment. -/
theorem no_unconditional_deq_deq_diamond :
    ¬ ∀ {T1 T2 T3 : SessionType} {q1 q2 : Role} {l1 l2 : Lab} {S1 S2 : DataSort},
      mon_tr_yes T1 (ext_tag.recv q1 l1 S1) T2 →
      mon_tr_yes T2 (ext_tag.recv q2 l2 S2) T3 → q1 ≠ q2 →
      ∃ M', mon_tr_yes T1 (ext_tag.recv q2 l2 S2) M' ∧
        mon_tr_yes M' (ext_tag.recv q1 l1 S1) T3 := by
  intro hAll
  obtain ⟨M', hS, hC⟩ := hAll MS_P3 MS_P4 (by decide : ("p" : Role) ≠ "q")
  have e1 : M' = MS_M1 :=
    mon_tr_yes_target_unique MS_T_WF hS MS_P1
  subst e1
  have e2 : MS_Mfold = MS_Mmon :=
    mon_tr_yes_target_unique MS_M1_WF hC MS_P2
  exact absurd e2.symm ms_ne

/-- Adjacent distinct-sender queue swaps do NOT preserve fold endpoints:
    `Q = Q1 ++ [p-msg, q-msg] ++ Q2` folding to `M` does not imply the
    swapped `Q'` folds to the same `M` (reading `q ≠ q` as `p ≠ q`).
    Witness: `MS_Q = [(p,a),(q,b)]` folds to `MS_Mfold`, but the swapped
    queue folds (via `MS_P1`/`MS_P2`, i.e. `MS_run`) to `MS_Mmon`, and
    `ms_ne` forbids identifying them. Companion to
    `no_unconditional_deq_deq_diamond` (same mechanism at run level). -/
theorem queue_swap_distinct_senders_fold_false :
    ¬ ∀ (T : SessionType) (Q1 Q2 : Queue) (p q : Role) (lab lab' : Lab)
      (S S' : DataSort) (M : SessionType), p ≠ q →
      monitor_fold (T, Q1 ++ [QueueMessage.msg p lab S] ++
        [QueueMessage.msg q lab' S'] ++ Q2) M →
      monitor_fold (T, Q1 ++ [QueueMessage.msg q lab' S'] ++
        [QueueMessage.msg p lab S] ++ Q2) M := by
  intro hAll
  have hPre : monitor_fold (MS_T, [] ++ [QueueMessage.msg "p" "a" "s"] ++
      [QueueMessage.msg "q" "b" "s"] ++ []) MS_Mfold := by
    simp only [List.nil_append, List.append_nil, List.singleton_append]
    exact MS_fold
  have hF : monitor_fold (MS_T,
      [] ++ [QueueMessage.msg "q" "b" "s"] ++
        [QueueMessage.msg "p" "a" "s"] ++ []) MS_Mfold :=
    hAll MS_T [] [] "p" "q" "a" "b" "s" "s" MS_Mfold (by decide) hPre
  have hF' : monitor_fold_aux [QueueMessage.msg "q" "b" "s",
      QueueMessage.msg "p" "a" "s"] MS_T MS_Mfold := by
    simp only [List.nil_append, List.append_nil, List.singleton_append] at hF
    exact hF
  obtain ⟨Tmid, hY1, hRest⟩ := hF'
  obtain ⟨Tmid2, hY2, hEnd⟩ := hRest
  simp only [monitor_fold_aux] at hEnd
  subst hEnd
  have hSeq : mon_yes_seq MS_T
      [ext_tag.recv "q" "b" "s", ext_tag.recv "p" "a" "s"] MS_Mfold :=
    mon_yes_seq.step hY1 (mon_yes_seq.step hY2 (mon_yes_seq.refl _))
  have e : MS_Mfold = MS_Mmon :=
    ms_mon_yes_seq_det MS_T_WF hSeq MS_run
  exact absurd e.symm ms_ne

/-- `(MS_I, MS_Q)` is stuck: `inp` has no `intC` rule and every
    `sendFresh` branch sender is junk-blocked (`q` is queued). Kills
    the `spec-a` stub in pinning. -/
private lemma MS_I_nostep : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
    ¬ over_trans (MS_I, MS_Q) α stq' := by
  intro α stq' hS
  cases hS with
  | dequeue hST hQ =>
    unfold MS_I at hST
    cases hST
  | specInp hST hAbs =>
    unfold MS_I at hST
    cases hST
  | sendFresh hEq hST hFresh =>
    unfold MS_I at hEq
    cases hEq
    have hmemB : (("q", "x", "s", SessionType.tEnd) : Role × Lab × DataSort ×
        SessionType) ∈ [("q", "x", "s", SessionType.tEnd),
        ("r", "y", "s", MS_D2)] := by
      simp
    have hmemM : QueueMessage.msg "q" "b" "s" ∈ MS_Q := by simp [MS_Q]
    have hcon := hFresh _ _ _ _ hmemB _ hmemM
    simp at hcon

/-- Live steps from `(MS_T, MS_Q)`: the three `r`-specs (dequeues miss
    the `p`/`q` queue, `sendFresh` needs `intC`). -/
private lemma MS_T_inv : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
    over_trans (MS_T, MS_Q) α stq' →
    (α = st_label.inp "r" "a" "s" ∧ stq' = (MS_I, MS_Q)) ∨
    (α = st_label.inp "r" "b" "s" ∧ stq' = (MS_Q1, MS_Q)) ∨
    (α = st_label.inp "r" "c" "s" ∧ stq' = (MS_Q1, MS_Q)) := by
  intro α stq' hS
  cases hS with
  | dequeue hST hQ =>
    unfold MS_T at hST
    cases hST with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [MS_Q, Queue.dequeue, Queue.dequeue.go] at hQ
  | specInp hST hAbs =>
    unfold MS_T at hST
    cases hST with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | sendFresh hEq _ _ =>
    unfold MS_T at hEq
    cases hEq

/-- Single live step from `(MS_Q1, MS_Q)`: the `b`-dequeue. -/
private lemma MS_Q1_inv : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
    over_trans (MS_Q1, MS_Q) α stq' →
    α = st_label.inp "q" "b" "s" ∧
      stq' = (MS_P0, [QueueMessage.msg "p" "a" "s"]) := by
  intro α stq' hS
  cases hS with
  | dequeue hST hQ =>
    unfold MS_Q1 at hST
    cases hST with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      obtain rfl := Option.some_inj.mp (MS_hQb.symm.trans hQ)
      exact ⟨rfl, rfl⟩
  | specInp hST hAbs =>
    unfold MS_Q1 at hST
    cases hST with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      have hmemB : QueueMessage.msg "q" "b" "s" ∈ MS_Q := by simp [MS_Q]
      have habs := hAbs _ hmemB
      simp at habs
  | sendFresh hEq _ _ =>
    unfold MS_Q1 at hEq
    cases hEq

/-- Single live step past the `b`-dequeue: the `a`-dequeue. -/
private lemma MS_P0_inv : ∀ (α : st_label) (stq' : SessionTypeWithQueue),
    over_trans (MS_P0, [QueueMessage.msg "p" "a" "s"]) α stq' →
    α = st_label.inp "p" "a" "s" ∧ stq' = (SessionType.tEnd, []) := by
  intro α stq' hS
  cases hS with
  | dequeue hST hQ =>
    have hP0 : MS_P0 =
        SessionType.externalChoice "p" [("a", "s", SessionType.tEnd)] := rfl
    rw [hP0] at hST
    cases hST with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      obtain rfl := Option.some_inj.mp (MS_hQc.symm.trans hQ)
      exact ⟨rfl, rfl⟩
  | specInp hST hAbs =>
    have hP0 : MS_P0 =
        SessionType.externalChoice "p" [("a", "s", SessionType.tEnd)] := rfl
    rw [hP0] at hST
    cases hST with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      have hmemA : QueueMessage.msg "p" "a" "s" ∈ [QueueMessage.msg "p" "a" "s"] := by
        simp
      have habs := hAbs _ hmemA
      simp at habs
  | sendFresh hEq _ _ =>
    have hP0 : MS_P0 =
        SessionType.externalChoice "p" [("a", "s", SessionType.tEnd)] := rfl
    rw [hP0] at hEq
    cases hEq

/-- `MS_Q1` is `Core`-deep for `MS_Q` (dequeue chain witness). -/
private lemma MS_Q1core :
    CanAlwaysDrainInternalDeepCore MS_Q1 MS_Q := by
  refine CanAlwaysDrainInternalDeepCore.mk MS_Q1 MS_Q SessionType.tEnd
    [st_label.inp "q" "b" "s", st_label.inp "p" "a" "s"]
    (fun _ _ _ _ => ("b", "s", MS_P0)) ?_ ?_ ?_ ?_
  · exact over_trans_trace.step (over_trans.dequeue MS_hSTb MS_hQb)
      (over_trans_trace.step (over_trans.dequeue MS_hSTc MS_hQc) (over_trans_trace.refl _))
  · intro Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hne br hmem
    cases ρ1 with
    | nil =>
      cases overTrTrace_nil_eq h1
      unfold MS_Q1 at hEq
      cases hEq
    | cons α' ρ1' =>
      cases h1 with
      | step hS hT =>
        rcases MS_Q1_inv _ _ hS with ⟨rfl, rfl⟩
        cases ρ1' with
        | nil =>
          cases overTrTrace_nil_eq hT
          unfold MS_P0 at hEq
          cases hEq
        | cons α2 ρ1'' =>
          cases hT with
          | step hS2 hT2 =>
            rcases MS_P0_inv _ _ hS2 with ⟨rfl, rfl⟩
            obtain ⟨rfl, rfl⟩ := by simpa using heq
            cases overTrTrace_nil_eq hT2
            cases hEq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    cases ρ1 with
    | nil =>
      cases overTrTrace_nil_eq h1
      exact (hnd ⟨_, _, _, _, _, MS_hSTb, MS_hQb⟩).elim
    | cons α' ρ1' =>
      cases h1 with
      | step hS hT =>
        rcases MS_Q1_inv _ _ hS with ⟨rfl, rfl⟩
        cases ρ1' with
        | nil =>
          cases overTrTrace_nil_eq hT
          exact (hnd ⟨_, _, _, _, _, MS_hSTc, MS_hQc⟩).elim
        | cons α2 ρ1'' =>
          cases hT with
          | step hS2 hT2 =>
            rcases MS_P0_inv _ _ hS2 with ⟨rfl, rfl⟩
            obtain ⟨rfl, rfl⟩ := by simpa using heq
            cases overTrTrace_nil_eq hT2
            cases hEq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    cases ρ1 with
    | nil =>
      cases overTrTrace_nil_eq h1
      exact (hnd ⟨_, _, _, _, _, MS_hSTb, MS_hQb⟩).elim
    | cons α' ρ1' =>
      cases h1 with
      | step hS hT =>
        rcases MS_Q1_inv _ _ hS with ⟨rfl, rfl⟩
        cases ρ1' with
        | nil =>
          cases overTrTrace_nil_eq hT
          exact (hnd ⟨_, _, _, _, _, MS_hSTc, MS_hQc⟩).elim
        | cons α2 ρ1'' =>
          cases hT with
          | step hS2 hT2 =>
            rcases MS_P0_inv _ _ hS2 with ⟨rfl, rfl⟩
            obtain ⟨rfl, rfl⟩ := by simpa using heq
            cases overTrTrace_nil_eq hT2
            cases hEq

/-- Pin lemma for the `spec-c → deq-b → deq-a` witness: splits land on
    the witness path (`spec-a` stubs cannot drain). -/
private lemma MS_pin : ∀ (ρ1 : List st_label) (Ti : SessionType) (Qi : Queue)
    (ρ2 : List st_label),
    over_trans_trace (MS_T, MS_Q) ρ1 (Ti, Qi) →
    over_trans_trace (Ti, Qi) ρ2 (SessionType.tEnd, []) →
    [st_label.inp "r" "c" "s", st_label.inp "q" "b" "s",
      st_label.inp "p" "a" "s"] = ρ1 ++ ρ2 →
    (Ti, Qi) = (MS_T, MS_Q) ∨ (Ti, Qi) = (MS_Q1, MS_Q) ∨
    (Ti, Qi) = (MS_P0, [QueueMessage.msg "p" "a" "s"]) ∨
    (Ti, Qi) = (SessionType.tEnd, []) := by
  intro ρ1 Ti Qi ρ2 h1 h2 heq
  cases ρ1 with
  | nil =>
    cases overTrTrace_nil_eq h1
    exact Or.inl rfl
  | cons α ρ1' =>
    cases h1 with
    | step hS hT =>
      rcases MS_T_inv _ _ hS with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        exact overTrTrace_no_drain_of_nostep MS_I_nostep (by simp [MS_Q])
          ⟨_, _, over_trans_trace_append hT h2⟩
      · cases ρ1' with
        | nil =>
          cases overTrTrace_nil_eq hT
          exact Or.inr (Or.inl rfl)
        | cons α2 ρ1'' =>
          cases hT with
          | step hS2 hT2 =>
            rcases MS_Q1_inv _ _ hS2 with ⟨rfl, rfl⟩
            cases ρ1'' with
            | nil =>
              cases overTrTrace_nil_eq hT2
              exact Or.inr (Or.inr (Or.inl rfl))
            | cons α3 ρ1''' =>
              cases hT2 with
              | step hS3 hT3 =>
                obtain ⟨hα3, hmid3⟩ := MS_P0_inv _ _ hS3
                rw [hα3] at heq
                rw [hmid3] at hT3
                exfalso
                simpa using heq
      · cases ρ1' with
        | nil =>
          cases overTrTrace_nil_eq hT
          exact Or.inr (Or.inl rfl)
        | cons α2 ρ1'' =>
          cases hT with
          | step hS2 hT2 =>
            rcases MS_Q1_inv _ _ hS2 with ⟨rfl, rfl⟩
            cases ρ1'' with
            | nil =>
              cases overTrTrace_nil_eq hT2
              exact Or.inr (Or.inr (Or.inl rfl))
            | cons α3 ρ1''' =>
              cases hT2 with
              | step hS3 hT3 =>
                obtain ⟨hα3, hmid3⟩ := MS_P0_inv _ _ hS3
                rw [hα3] at heq
                rw [hmid3] at hT3
                obtain ⟨rfl, rfl⟩ := by simpa using heq
                cases overTrTrace_nil_eq hT3
                exact Or.inr (Or.inr (Or.inr rfl))

/-- The MS witness is internally robust: it drains (via `MS_hTr`,
    forgotten to `over_trans_trace`) and its head is `extC`, so the
    `internalChoice`-branch condition holds vacuously. -/
theorem ms_robust : CanAlwaysDrainInternalDeep MS_T MS_Q := by
  refine ⟨SessionType.tEnd,
    [st_label.inp "r" "c" "s", st_label.inp "q" "b" "s",
      st_label.inp "p" "a" "s"],
    over_trans_trace.step (over_trans.specInp MS_hSTa MS_hAbs)
      (over_trans_trace.step (over_trans.dequeue MS_hSTb MS_hQb)
        (over_trans_trace.step (over_trans.dequeue MS_hSTc MS_hQc)
          (over_trans_trace.refl _))),
    ?_⟩
  intro Ti Qi ρ1 ρ2 h1 h2 heq
  rcases MS_pin ρ1 Ti Qi ρ2 h1 h2 heq with h | h | h | h <;> cases h
  · refine ⟨?_, ?_⟩
    · intro branches hEq _ _ _
      unfold MS_T at hEq
      cases hEq
    · intro p branches hEq _ _
      unfold MS_T at hEq
      cases hEq
      exact ⟨("b", "s", MS_Q1),
        List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), MS_Q1core⟩
  · refine ⟨?_, ?_⟩
    · intro branches hEq _ _ _
      unfold MS_Q1 at hEq
      cases hEq
    · intro _ _ _ _ hnd
      exact (hnd ⟨_, _, _, _, _, MS_hSTb, MS_hQb⟩).elim
  · refine ⟨?_, ?_⟩
    · intro branches hEq _ _ _
      unfold MS_P0 at hEq
      cases hEq
    · intro _ _ _ _ hnd
      exact (hnd ⟨_, _, _, _, _, MS_hSTc, MS_hQc⟩).elim
  · refine ⟨?_, ?_⟩
    · intro branches hEq _ _ _
      cases hEq
    · intro _ _ hEq _ _
      cases hEq

/-- Robustness does not save the queue-swap-fold claim: `MS_T`/`MS_Q`
    satisfy BOTH `CanAlwaysDrainInternalDeep` and `monitor_fold _ MS_Mfold`,
    yet the swapped queue folds to `MS_Mmon ≠ MS_Mfold` (same
    determinism argument as `queue_swap_distinct_senders_fold_false`). -/
theorem robust_fold_swap_false :
    ¬ ∀ (T : SessionType) (Q1 Q2 : Queue) (p q : Role) (lab lab' : Lab)
      (S S' : DataSort) (M : SessionType), p ≠ q →
      CanAlwaysDrainInternalDeep T
        (Q1 ++ [QueueMessage.msg p lab S] ++
          [QueueMessage.msg q lab' S'] ++ Q2) →
      monitor_fold (T, Q1 ++ [QueueMessage.msg p lab S] ++
        [QueueMessage.msg q lab' S'] ++ Q2) M →
      monitor_fold (T, Q1 ++ [QueueMessage.msg q lab' S'] ++
        [QueueMessage.msg p lab S] ++ Q2) M := by
  intro hAll
  have hR : CanAlwaysDrainInternalDeep MS_T
      ([] ++ [QueueMessage.msg "p" "a" "s"] ++
        [QueueMessage.msg "q" "b" "s"] ++ []) := by
    simpa only [MS_Q, List.nil_append, List.append_nil, List.singleton_append]
      using ms_robust
  have hFold : monitor_fold (MS_T, [] ++ [QueueMessage.msg "p" "a" "s"] ++
      [QueueMessage.msg "q" "b" "s"] ++ []) MS_Mfold := by
    simp only [List.nil_append, List.append_nil, List.singleton_append]
    exact MS_fold
  have hF := hAll MS_T [] [] "p" "q" "a" "b" "s" "s" MS_Mfold
    (by decide) hR hFold
  have hF' : monitor_fold_aux [QueueMessage.msg "q" "b" "s",
      QueueMessage.msg "p" "a" "s"] MS_T MS_Mfold := by
    simp only [List.nil_append, List.append_nil, List.singleton_append] at hF
    exact hF
  obtain ⟨Tmid, hY1, hRest⟩ := hF'
  obtain ⟨Tmid2, hY2, hEnd⟩ := hRest
  simp only [monitor_fold_aux] at hEnd
  subst hEnd
  have hSeq : mon_yes_seq MS_T
      [ext_tag.recv "q" "b" "s", ext_tag.recv "p" "a" "s"] MS_Mfold :=
    mon_yes_seq.step hY1 (mon_yes_seq.step hY2 (mon_yes_seq.refl _))
  have e : MS_Mfold = MS_Mmon :=
    ms_mon_yes_seq_det MS_T_WF hSeq MS_run
  exact absurd e.symm ms_ne

-- ================================================================
-- Unconditional fold-step-1 is false: `FS_T` folds `[mp, mq]` (via the
-- `s`-branch) yet refuses `mq` outright — the `q`-sender branch
-- kills prefix-`hno` and no base fires a `recv` at `intC`.
-- Consequence: every fold-swap/descent program needs drain-derived
-- freshness (or shape premises) for `intC` nodes; `hno` side
-- conditions are load-bearing, not bureaucratic.
-- ================================================================

private def FS_Sy1 : SessionType :=
  SessionType.externalChoice "q" [("b", "s", SessionType.tEnd)]

private def FS_Sy : SessionType :=
  SessionType.externalChoice "p" [("a", "s", FS_Sy1)]

private def FS_T : SessionType :=
  SessionType.internalChoice
    [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)]

private def FS_F1 : SessionType :=
  SessionType.internalChoice [("s", "y", "s", FS_Sy1)]

private def FS_M : SessionType :=
  SessionType.internalChoice [("s", "y", "s", SessionType.tEnd)]

/-- `Sy -(p,a)-> Sy1` (base, maximal pair). -/
private lemma fs_sy_pa : mon_tr_yes FS_Sy (ext_tag.recv "p" "a" "s") FS_Sy1 := by
  have huniq : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("a", "s", FS_Sy1)]) := by
    decide
  have hmem : ("a", "s", FS_Sy1) ∈ [("a", "s", FS_Sy1)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hb : mon_tr_yes_base FS_Sy (ext_tag.recv "p" "a" "s") FS_Sy1 :=
    mon_tr_yes_base.extC huniq hmem
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- Step 1: `T -(p,a)-> F1` (the `q`-branch drops — `tEnd` rejects). -/
private lemma fs_step1 : mon_tr_yes FS_T (ext_tag.recv "p" "a" "s") FS_F1 := by
  obtain ⟨hE, hM⟩ := fs_sy_pa
  have htriple : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)]) := by
    decide
  have hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort) (T0 : SessionType),
      (p', lab', S', T0) ∈
        [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)] →
      "p" ≠ p' := by
    intro p' lab' S' T0 hmemB
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · decide
    · decide
  have hall : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort),
      (r', l', s', T0') ∈
        [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)] →
      (r', l', s', T1) ∈ [("s", "y", "s", FS_Sy1)] →
      mon_tr_yes_exist T0' (ext_tag.recv "p" "a" "s") T1 := by
    intro T0' T1 r' l' s' hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    have hT0eq : T0' = FS_Sy := unique_target_of_nodup_int htriple hmemB
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    subst T0'
    exact hE
  have hallMax : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort)
      (hmemB : (r', l', s', T0') ∈
        [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)])
      (hmemK : (r', l', s', T1) ∈ [("s", "y", "s", FS_Sy1)])
      (hsub : mon_tr_yes_exist T0' (ext_tag.recv "p" "a" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0' T1 r' l' s' hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    have hT0eq : T0' = FS_Sy := unique_target_of_nodup_int htriple hmemB
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    subst T0'
    cases proof_irrel hsub hE
    exact hM
  have hcover : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T0' : SessionType),
      (r', l', s', T0') ∈
        [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)] →
      (∃ T1, mon_tr_yes_exist T0' (ext_tag.recv "p" "a" "s") T1) →
      ∃ T1, (r', l', s', T1) ∈ [("s", "y", "s", FS_Sy1)] := by
    intro r' l' s' T0' hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨T1, hE⟩ := hex
      exact absurd hE ms_tEndNoExist
    · exact ⟨FS_Sy1, List.mem_cons.mpr (Or.inl rfl)⟩
  have hkey : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T1 : SessionType),
      (r', l', s', T1) ∈ [("s", "y", "s", FS_Sy1)] →
      ∃ T0', (r', l', s', T0') ∈
        [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)] := by
    intro r' l' s' T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨FS_Sy, List.mem_cons.mpr
      (Or.inr (List.mem_cons.mpr (Or.inl rfl)))⟩
  have hmemB0 : ("q", "x", "s", SessionType.tEnd) ∈
      [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0 : ("s", "y", "s", FS_Sy1) ∈ [("s", "y", "s", FS_Sy1)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hne : [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)] ≠ [] ∧
      [("s", "y", "s", FS_Sy1)] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0, List.ne_nil_of_mem hmemK0⟩
  have hNodupKept : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
      [("s", "y", "s", FS_Sy1)]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("s", "y", "s", FS_Sy1)]) (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("q", "x", "s", SessionType.tEnd), ("s", "y", "s", FS_Sy)]) := by
    decide
  exact ⟨mon_tr_yes_exist.pfxInt hne hno rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxInt (hne := hne) (hno := hno) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- `Sy1 -(q,b)-> tEnd` (base, maximal pair). -/
private lemma fs_sy1_qb : mon_tr_yes FS_Sy1 (ext_tag.recv "q" "b" "s")
    SessionType.tEnd := by
  have huniq : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      [("b", "s", SessionType.tEnd)]) := by
    decide
  have hmem : ("b", "s", SessionType.tEnd) ∈ [("b", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hb : mon_tr_yes_base FS_Sy1 (ext_tag.recv "q" "b" "s") SessionType.tEnd :=
    mon_tr_yes_base.extC huniq hmem
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- Step 2: `F1 -(q,b)-> M` (single branch). -/
private lemma fs_step2 : mon_tr_yes FS_F1 (ext_tag.recv "q" "b" "s") FS_M := by
  obtain ⟨hE, hM⟩ := fs_sy1_qb
  have htriple : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("s", "y", "s", FS_Sy1)]) := by
    decide
  have hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort) (T0 : SessionType),
      (p', lab', S', T0) ∈ [("s", "y", "s", FS_Sy1)] →
      "q" ≠ p' := by
    intro p' lab' S' T0 hmemB
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩
    decide
  have hall : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort),
      (r', l', s', T0') ∈ [("s", "y", "s", FS_Sy1)] →
      (r', l', s', T1) ∈ [("s", "y", "s", SessionType.tEnd)] →
      mon_tr_yes_exist T0' (ext_tag.recv "q" "b" "s") T1 := by
    intro T0' T1 r' l' s' hmemB hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    have hT0eq : T0' = FS_Sy1 := unique_target_of_nodup_int htriple hmemB
      (List.mem_cons.mpr (Or.inl rfl))
    subst T0'
    exact hE
  have hallMax : ∀ (T0' T1 : SessionType) (r' : Role) (l' : Lab) (s' : DataSort)
      (hmemB : (r', l', s', T0') ∈ [("s", "y", "s", FS_Sy1)])
      (hmemK : (r', l', s', T1) ∈ [("s", "y", "s", SessionType.tEnd)])
      (hsub : mon_tr_yes_exist T0' (ext_tag.recv "q" "b" "s") T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0' T1 r' l' s' hmemB hmemK hsub
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    have hT0eq : T0' = FS_Sy1 := unique_target_of_nodup_int htriple hmemB
      (List.mem_cons.mpr (Or.inl rfl))
    subst T0'
    cases proof_irrel hsub hE
    exact hM
  have hcover : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T0' : SessionType),
      (r', l', s', T0') ∈ [("s", "y", "s", FS_Sy1)] →
      (∃ T1, mon_tr_yes_exist T0' (ext_tag.recv "q" "b" "s") T1) →
      ∃ T1, (r', l', s', T1) ∈ [("s", "y", "s", SessionType.tEnd)] := by
    intro r' l' s' T0' hmemB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨SessionType.tEnd, List.mem_cons.mpr (Or.inl rfl)⟩
  have hkey : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (T1 : SessionType),
      (r', l', s', T1) ∈ [("s", "y", "s", SessionType.tEnd)] →
      ∃ T0', (r', l', s', T0') ∈ [("s", "y", "s", FS_Sy1)] := by
    intro r' l' s' T1 hmemK
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemK
    rcases hmemK with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨FS_Sy1, List.mem_cons.mpr (Or.inl rfl)⟩
  have hmemB0 : ("s", "y", "s", FS_Sy1) ∈ [("s", "y", "s", FS_Sy1)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hmemK0 : ("s", "y", "s", SessionType.tEnd) ∈
      [("s", "y", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hne : [("s", "y", "s", FS_Sy1)] ≠ [] ∧
      [("s", "y", "s", SessionType.tEnd)] ≠ [] :=
    ⟨List.ne_nil_of_mem hmemB0, List.ne_nil_of_mem hmemK0⟩
  have hNodupKept : List.Nodup (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
      [("s", "y", "s", SessionType.tEnd)]) := by
    decide
  have horder : List.Sublist (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("s", "y", "s", SessionType.tEnd)]) (List.map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      [("s", "y", "s", FS_Sy1)]) := by
    decide
  exact ⟨mon_tr_yes_exist.pfxInt hne hno rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxInt (hne := hne) (hno := hno) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- Fold of `[mp, mq]`. -/
private lemma fs_fold : monitor_fold_aux
    [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"] FS_T FS_M := by
  have hY1 : mon_tr_yes FS_T (ext_tag.recv "p" "a" "s") FS_F1 := fs_step1
  have hY2 : mon_tr_yes FS_F1 (ext_tag.recv "q" "b" "s") FS_M := fs_step2
  show ∃ T_mid, mon_tr_yes FS_T (ext_tag.recv "p" "a" "s") T_mid ∧
    monitor_fold_aux [QueueMessage.msg "q" "b" "s"] T_mid FS_M
  exact ⟨FS_F1, hY1, FS_M, hY2, rfl⟩

/-- `T` refuses `mq`: the `q`-sender branch kills prefix-`hno`. -/
private lemma fs_refuse : ¬ ∃ X, mon_tr_yes FS_T (ext_tag.recv "q" "b" "s") X := by
  intro hex
  obtain ⟨X, hY⟩ := hex
  obtain ⟨hE, hM⟩ := hY
  cases hE with
  | base hb => cases hb
  | pfxInt hne hno _ _ _ _ =>
    exact absurd rfl
      (hno "q" "x" "s" _ (List.mem_cons.mpr (Or.inl rfl)))

/-- Unconditional fold-step-1 is FALSE: `FS_T` folds `[mp, mq]` (via
    the `s`-branch) yet refuses `mq` outright — prefix-`hno` fails on
    the `q`-sender branch and no base fires a `recv` at `intC`.
    Consequence: every fold-swap/descent program needs drain-derived
    freshness (or shape premises) for `intC` nodes; `hno` side
    conditions are load-bearing, not bureaucratic. -/
theorem fold_swap_step1_false :
    ¬ ∀ (T : SessionType) (M : SessionType) (p q : Role) (lab lab' : Lab)
      (S S' : DataSort), p ≠ q →
      monitor_fold (T, [QueueMessage.msg p lab S, QueueMessage.msg q lab' S']) M →
      ∃ X, mon_tr_yes T (ext_tag.recv q lab' S') X := by
  intro hAll
  have hFold : monitor_fold
      (FS_T, [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"]) FS_M :=
    fs_fold
  obtain ⟨X, hX⟩ := hAll FS_T FS_M "p" "q" "a" "b" "s" "s" (by decide) hFold
  exact fs_refuse ⟨X, hX⟩

/-- Multi-prefix example types: a two-spec ladder
    `r -spec(c)-> s -spec(d)-> p -deq(a)-> q -deq(b)-> tEnd`,
    all singleton branches. -/
private def MP_T4 : SessionType := SessionType.tEnd
private def MP_T3 : SessionType :=
  SessionType.externalChoice "q" [("b", "s", MP_T4)]
private def MP_T2 : SessionType :=
  SessionType.externalChoice "p" [("a", "s", MP_T3)]
private def MP_T1 : SessionType :=
  SessionType.externalChoice "s" [("d", "s", MP_T2)]
private def MP_T : SessionType :=
  SessionType.externalChoice "r" [("c", "s", MP_T1)]

private def MP_ks : List (TrKind × st_label) :=
  [(TrKind.spec, st_label.inp "r" "c" "s"),
    (TrKind.spec, st_label.inp "s" "d" "s"),
    (TrKind.dequeue, st_label.inp "p" "a" "s"),
    (TrKind.dequeue, st_label.inp "q" "b" "s")]

private lemma MP_hST1 : st_trans MP_T (st_label.inp "r" "c" "s") MP_T1 :=
  st_trans.extC (List.mem_cons.mpr (Or.inl rfl))

private lemma MP_hAbs1 :
    ∀ m ∈ [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"], m.1 ≠ "r" := by
  intro m hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl
  · decide
  · decide

private lemma MP_hST2 : st_trans MP_T1 (st_label.inp "s" "d" "s") MP_T2 :=
  st_trans.extC (List.mem_cons.mpr (Or.inl rfl))

private lemma MP_hAbs2 :
    ∀ m ∈ [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"], m.1 ≠ "s" := by
  intro m hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl
  · decide
  · decide

private lemma MP_hST3 :
    st_trans MP_T2 (st_label.inp "p" "a" "s") MP_T3 :=
  st_trans.extC (List.mem_cons.mpr (Or.inl rfl))

private lemma MP_hQ3 : Queue.dequeue
    [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"]
    (QueueMessage.msg "p" "a" "s") = some [QueueMessage.msg "q" "b" "s"] := by
  decide

private lemma MP_hST4 :
    st_trans MP_T3 (st_label.inp "q" "b" "s") SessionType.tEnd :=
  st_trans.extC (List.mem_cons.mpr (Or.inl rfl))

private lemma MP_hQ4 : Queue.dequeue [QueueMessage.msg "q" "b" "s"]
    (QueueMessage.msg "q" "b" "s") = some [] := by
  decide

/-- The two-spec-prefix p-order drain. -/
theorem MP_drain : ClassTr
    (MP_T, [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"]) MP_ks
    (SessionType.tEnd, []) :=
  ClassTr.spec MP_hST1 MP_hAbs1
    (ClassTr.spec MP_hST2 MP_hAbs2
      (ClassTr.deq MP_hST3 MP_hQ3
        (ClassTr.deq MP_hST4 MP_hQ4 (ClassTr.refl _))))

/-- Routing side-conditions: two non-dequeue heads (checkable) and
    p-order drain order (computes). -/
theorem MP_routing :
    (∃ k1 k2 rest, MP_ks = k1 :: k2 :: rest ∧
      k1.1 ≠ TrKind.dequeue ∧ k2.1 ≠ TrKind.dequeue) ∧
    deqMsgsOf MP_ks =
      [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"] := by
  have hks0 : MP_ks =
      [(TrKind.spec, st_label.inp "r" "c" "s"),
        (TrKind.spec, st_label.inp "s" "d" "s"),
        (TrKind.dequeue, st_label.inp "p" "a" "s"),
        (TrKind.dequeue, st_label.inp "q" "b" "s")] := rfl
  refine ⟨⟨_, _, _, hks0, by decide, by decide⟩, ?_⟩
  rfl

private lemma MP_T4_NoRec : MP_T4.NoRec := SessionType.NoRec.end

private lemma MP_T3_NoRec : MP_T3.NoRec := by
  unfold MP_T3
  apply SessionType.NoRec.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MP_T4_NoRec

private lemma MP_T2_NoRec : MP_T2.NoRec := by
  unfold MP_T2
  apply SessionType.NoRec.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MP_T3_NoRec

private lemma MP_T1_NoRec : MP_T1.NoRec := by
  unfold MP_T1
  apply SessionType.NoRec.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MP_T2_NoRec

private lemma MP_T_NoRec : MP_T.NoRec := by
  unfold MP_T
  apply SessionType.NoRec.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MP_T1_NoRec

private lemma MP_T4_NoDupl : MP_T4.NoDupl := SessionType.NoDupl.end

private lemma MP_T3_NoDupl : MP_T3.NoDupl := by
  unfold MP_T3
  apply SessionType.NoDupl.externalChoice
  · decide
  · intro h
    cases h
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl
    exact MP_T4_NoDupl

private lemma MP_T2_NoDupl : MP_T2.NoDupl := by
  unfold MP_T2
  apply SessionType.NoDupl.externalChoice
  · decide
  · intro h
    cases h
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl
    exact MP_T3_NoDupl

private lemma MP_T1_NoDupl : MP_T1.NoDupl := by
  unfold MP_T1
  apply SessionType.NoDupl.externalChoice
  · decide
  · intro h
    cases h
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl
    exact MP_T2_NoDupl

private lemma MP_T_NoDupl : MP_T.NoDupl := by
  unfold MP_T
  apply SessionType.NoDupl.externalChoice
  · decide
  · intro h
    cases h
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl
    exact MP_T1_NoDupl

private lemma MP_T_IsClosed : MP_T.IsClosed := by
  unfold SessionType.IsClosed
  decide

private lemma MP_T4_Contractive : MP_T4.Contractive :=
  SessionType.Contractive.end

private lemma MP_T3_Contractive : MP_T3.Contractive := by
  unfold MP_T3
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MP_T4_Contractive

private lemma MP_T3_IsClosed : MP_T3.IsClosed := by
  unfold SessionType.IsClosed
  decide

private lemma MP_T3_WF : MP_T3.WellFormed :=
  ⟨MP_T3_NoDupl, MP_T3_IsClosed, MP_T3_Contractive⟩

private lemma MP_T2_Contractive : MP_T2.Contractive := by
  unfold MP_T2
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MP_T3_Contractive

private lemma MP_T2_IsClosed : MP_T2.IsClosed := by
  unfold SessionType.IsClosed
  decide

private lemma MP_T2_WF : MP_T2.WellFormed :=
  ⟨MP_T2_NoDupl, MP_T2_IsClosed, MP_T2_Contractive⟩

private lemma MP_T1_Contractive : MP_T1.Contractive := by
  unfold MP_T1
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MP_T2_Contractive

private lemma MP_T1_IsClosed : MP_T1.IsClosed := by
  unfold SessionType.IsClosed
  decide

private lemma MP_T1_WF : MP_T1.WellFormed :=
  ⟨MP_T1_NoDupl, MP_T1_IsClosed, MP_T1_Contractive⟩

private lemma MP_T_Contractive : MP_T.Contractive := by
  unfold MP_T
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl
  exact MP_T1_Contractive

private lemma MP_T_WF : MP_T.WellFormed :=
  ⟨MP_T_NoDupl, MP_T_IsClosed, MP_T_Contractive⟩

/-- Kept-filter terms for the direct `M'` construction below: `F3/F2/F1`
    are the `mq`-filters down the ladder, `G2/G1` the subsequent
    `mp`-filters. Pure terms (no proofs); every entry is singleton-keyed,
    so all opaque `choose` targets pin by key-nodup + determinism. -/
private noncomputable def MP_F3 : List (Lab × DataSort × SessionType) :=
  extBranchesWithmon_tr_yes "p" [("a", "s", MP_T3)] "q" "b" "s"
    (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')

private noncomputable def MP_F2 : List (Lab × DataSort × SessionType) :=
  extBranchesWithmon_tr_yes "s" [("d", "s", MP_T2)] "q" "b" "s"
    (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')

private noncomputable def MP_F1 : List (Lab × DataSort × SessionType) :=
  extBranchesWithmon_tr_yes "r" [("c", "s", MP_T1)] "q" "b" "s"
    (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')

private noncomputable def MP_G2 : List (Lab × DataSort × SessionType) :=
  extBranchesWithmon_tr_yes "s" MP_F2 "p" "a" "s"
    (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')

private noncomputable def MP_G1 : List (Lab × DataSort × SessionType) :=
  extBranchesWithmon_tr_yes "r" MP_F1 "p" "a" "s"
    (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')

/-- Multi-prefix instance, proved directly (no residue call): the two-spec
    ladder's singleton branches force every kept-filter pin (key-nodup +
    determinism), so `M'` is built bottom-up with standard axioms only.
    `hFold`/`hM`/`hR` are unused (kept for interface fidelity). -/
theorem swap_just2_multi_prefix_example
    {M : SessionType}
    (hFold : monitor_fold
      (MP_T, [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"]) M)
    (hM : mon_yes_seq M (sSpecOf MP_ks) SessionType.tEnd)
    (hR : CanAlwaysDrainInternalDeep MP_T
      [QueueMessage.msg "p" "a" "s", QueueMessage.msg "q" "b" "s"]) :
    ∃ M', monitor_fold
      (MP_T, [QueueMessage.msg "q" "b" "s", QueueMessage.msg "p" "a" "s"]) M' ∧
      mon_yes_seq M' (sSpecOf MP_ks) SessionType.tEnd := by
  have _ := hFold
  have _ := hM
  have _ := hR
  have hspec : sSpecOf MP_ks =
      [ext_tag.recv "r" "c" "s", ext_tag.recv "s" "d" "s"] := rfl
  -- Bottom rung: on-role base mq-step at MP_T3 (singleton key).
  have hpair3 : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      ([("b", "s", MP_T4)] : List (Lab × DataSort × SessionType))) := by
    decide
  have hmemB3 : (("b", "s", MP_T4) : Lab × DataSort × SessionType) ∈
      ([("b", "s", MP_T4)] : List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  have hb3 : mon_tr_yes_base MP_T3 (ext_tag.recv "q" "b" "s") MP_T4 :=
    mon_tr_yes_base.extC hpair3 hmemB3
  have hMq3 : mon_tr_yes MP_T3 (ext_tag.recv "q" "b" "s") MP_T4 :=
    ⟨mon_tr_yes_exist.base hb3, @mon_tr_yes_max_deriv.base _ _ _ hb3⟩
  -- mq-ladder rung at MP_T2 (off-role prefix over a singleton origin).
  have hmemA3 : (("a", "s", MP_T3) : Lab × DataSort × SessionType) ∈
      ([("a", "s", MP_T3)] : List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  obtain ⟨Uop3, he3mem⟩ := sd_kept_of_acceptable (pe := "p") hmemA3
    ⟨MP_T4, hMq3⟩
  have hne3 : MP_F3 ≠ [] := List.ne_nil_of_mem he3mem
  have hW3mq : mon_tr_yes MP_T2 (ext_tag.recv "q" "b" "s")
      (SessionType.externalChoice "p" MP_F3) :=
    sd_maxPfxExt_of_kept_ne_norec MP_T2_NoRec MP_T2_NoDupl (by decide) hne3
  -- Pin the opaque F3-entry target (singleton origin forces MP_T3).
  obtain ⟨T0s3, hmem03, hYU3⟩ := mem_extBranchesWithmon_tr_yes_recv he3mem
  have hnodA : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      ([("a", "s", MP_T3)] : List (Lab × DataSort × SessionType))) := by
    decide
  have hT03 : T0s3 = MP_T3 :=
    unique_target_of_nodup_ext hnodA hmem03 hmemA3
  rw [hT03] at hYU3
  have hUop3 : Uop3 = MP_T4 :=
    mon_tr_yes_target_unique MP_T3_WF hYU3 hMq3
  rw [hUop3] at he3mem
  have hNDW3 : (SessionType.externalChoice "p" MP_F3).NoDupl :=
    (mon_tr_yes_preserves_norec_no_dupl MP_T2_NoRec MP_T2_NoDupl hW3mq).2
  have hW3mp : mon_tr_yes (SessionType.externalChoice "p" MP_F3)
      (ext_tag.recv "p" "a" "s") MP_T4 :=
    (spec_monitor_step_iff rfl hNDW3).mpr ⟨MP_T4, he3mem, rfl⟩
  -- mq-ladder rung at MP_T1.
  have hmemA2 : (("d", "s", MP_T2) : Lab × DataSort × SessionType) ∈
      ([("d", "s", MP_T2)] : List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  obtain ⟨Uop2, he2mem⟩ := sd_kept_of_acceptable (pe := "s") hmemA2
    ⟨SessionType.externalChoice "p" MP_F3, hW3mq⟩
  have hne2 : MP_F2 ≠ [] := List.ne_nil_of_mem he2mem
  have hW2mq : mon_tr_yes MP_T1 (ext_tag.recv "q" "b" "s")
      (SessionType.externalChoice "s" MP_F2) :=
    sd_maxPfxExt_of_kept_ne_norec MP_T1_NoRec MP_T1_NoDupl (by decide) hne2
  have hNRW2 : (SessionType.externalChoice "s" MP_F2).NoRec :=
    (mon_tr_yes_preserves_norec_no_dupl MP_T1_NoRec MP_T1_NoDupl hW2mq).1
  have hNDW2 : (SessionType.externalChoice "s" MP_F2).NoDupl :=
    (mon_tr_yes_preserves_norec_no_dupl MP_T1_NoRec MP_T1_NoDupl hW2mq).2
  obtain ⟨T0s2, hmem02, hYU2⟩ := mem_extBranchesWithmon_tr_yes_recv he2mem
  have hnodD : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      ([("d", "s", MP_T2)] : List (Lab × DataSort × SessionType))) := by
    decide
  have hT02 : T0s2 = MP_T2 :=
    unique_target_of_nodup_ext hnodD hmem02 hmemA2
  rw [hT02] at hYU2
  have hUop2 : Uop2 = SessionType.externalChoice "p" MP_F3 :=
    mon_tr_yes_target_unique MP_T2_WF hYU2 hW3mq
  rw [hUop2] at he2mem
  -- mp-step at the pinned W2 endpoint (onward acceptor for the W1 level).
  obtain ⟨UopG2, heG2mem⟩ := sd_kept_of_acceptable (pe := "s") he2mem
    ⟨MP_T4, hW3mp⟩
  have hneG2 : MP_G2 ≠ [] := List.ne_nil_of_mem heG2mem
  have hW2mp : mon_tr_yes (SessionType.externalChoice "s" MP_F2)
      (ext_tag.recv "p" "a" "s") (SessionType.externalChoice "s" MP_G2) :=
    sd_maxPfxExt_of_kept_ne_norec hNRW2 hNDW2 (by decide) hneG2
  have hNDU1 : (SessionType.externalChoice "s" MP_G2).NoDupl :=
    (mon_tr_yes_preserves_norec_no_dupl hNRW2 hNDW2 hW2mp).2
  -- mq-ladder rung at MP_T.
  have hmemA1 : (("c", "s", MP_T1) : Lab × DataSort × SessionType) ∈
      ([("c", "s", MP_T1)] : List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  obtain ⟨Uop1, he1mem⟩ := sd_kept_of_acceptable (pe := "r") hmemA1
    ⟨SessionType.externalChoice "s" MP_F2, hW2mq⟩
  have hne1 : MP_F1 ≠ [] := List.ne_nil_of_mem he1mem
  have hW1mq : mon_tr_yes MP_T (ext_tag.recv "q" "b" "s")
      (SessionType.externalChoice "r" MP_F1) :=
    sd_maxPfxExt_of_kept_ne_norec MP_T_NoRec MP_T_NoDupl (by decide) hne1
  have hNRW1 : (SessionType.externalChoice "r" MP_F1).NoRec :=
    (mon_tr_yes_preserves_norec_no_dupl MP_T_NoRec MP_T_NoDupl hW1mq).1
  have hNDW1 : (SessionType.externalChoice "r" MP_F1).NoDupl :=
    (mon_tr_yes_preserves_norec_no_dupl MP_T_NoRec MP_T_NoDupl hW1mq).2
  obtain ⟨T0s1, hmem01, hYU1⟩ := mem_extBranchesWithmon_tr_yes_recv he1mem
  have hnodC : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
      ([("c", "s", MP_T1)] : List (Lab × DataSort × SessionType))) := by
    decide
  have hT01 : T0s1 = MP_T1 :=
    unique_target_of_nodup_ext hnodC hmem01 hmemA1
  rw [hT01] at hYU1
  have hUop1 : Uop1 = SessionType.externalChoice "s" MP_F2 :=
    mon_tr_yes_target_unique MP_T1_WF hYU1 hW2mq
  rw [hUop1] at he1mem
  -- mp-step at W1; the fold closes around the pinned (c)-entry.
  obtain ⟨UopG1, heG1mem⟩ := sd_kept_of_acceptable (pe := "r") he1mem
    ⟨SessionType.externalChoice "s" MP_G2, hW2mp⟩
  have hneG1 : MP_G1 ≠ [] := List.ne_nil_of_mem heG1mem
  have hW1mp : mon_tr_yes (SessionType.externalChoice "r" MP_F1)
      (ext_tag.recv "p" "a" "s") (SessionType.externalChoice "r" MP_G1) :=
    sd_maxPfxExt_of_kept_ne_norec hNRW1 hNDW1 (by decide) hneG1
  have hM'ND : (SessionType.externalChoice "r" MP_G1).NoDupl :=
    (mon_tr_yes_preserves_norec_no_dupl hNRW1 hNDW1 hW1mp).2
  have hFold' : monitor_fold
      (MP_T, [QueueMessage.msg "q" "b" "s", QueueMessage.msg "p" "a" "s"])
      (SessionType.externalChoice "r" MP_G1) :=
    ⟨SessionType.externalChoice "r" MP_F1, hW1mq, _, hW1mp, rfl⟩
  -- Key-nodup squeeze for MP_F1 (singleton origin): pins G1-entry target.
  have hnodF1 : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) MP_F1) := by
    have hsub : (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        MP_F1).Sublist
        (List.map (fun a : {x // x ∈ [("c", "s", MP_T1)]} => (a.val.1, a.val.2.1))
          [("c", "s", MP_T1)].attach) :=
      sd_filterMap_keys_sublist ?hkeyOrd1
    have hatt : List.map
        (fun a : {x // x ∈ [("c", "s", MP_T1)]} => (a.val.1, a.val.2.1))
        [("c", "s", MP_T1)].attach =
        List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
          [("c", "s", MP_T1)] :=
      List.attach_map_val
        (f := fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
    rw [hatt] at hsub
    have hnodOrigin : List.Nodup (List.map
        (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        ([("c", "s", MP_T1)] : List (Lab × DataSort × SessionType))) := by
      decide
    exact hsub.nodup hnodOrigin
    · intro a ha b hb
      rcases a with ⟨⟨l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  obtain ⟨T0sG, hmem0G, hYUG⟩ := mem_extBranchesWithmon_tr_yes_recv heG1mem
  have hT0sG : T0sG = SessionType.externalChoice "s" MP_F2 :=
    unique_target_of_nodup_ext hnodF1 hmem0G he1mem
  rw [hT0sG] at hYUG
  have hWFW2 : (SessionType.externalChoice "s" MP_F2).WellFormed :=
    mon_tr_yes_preserves_wf hW2mq MP_T1_WF
  have hUopG1 : UopG1 = SessionType.externalChoice "s" MP_G2 :=
    mon_tr_yes_target_unique hWFW2 hYUG hW2mp
  rw [hUopG1] at heG1mem
  have hRun1 : mon_tr_yes (SessionType.externalChoice "r" MP_G1)
      (ext_tag.recv "r" "c" "s") (SessionType.externalChoice "s" MP_G2) :=
    (spec_monitor_step_iff rfl hM'ND).mpr
      ⟨SessionType.externalChoice "s" MP_G2, heG1mem, rfl⟩
  -- Key-nodup squeeze for MP_F2 (singleton origin): pins G2-entry target.
  have hnodF2 : List.Nodup (List.map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) MP_F2) := by
    have hsub : (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        MP_F2).Sublist
        (List.map (fun a : {x // x ∈ [("d", "s", MP_T2)]} => (a.val.1, a.val.2.1))
          [("d", "s", MP_T2)].attach) :=
      sd_filterMap_keys_sublist ?hkeyOrd2
    have hatt : List.map
        (fun a : {x // x ∈ [("d", "s", MP_T2)]} => (a.val.1, a.val.2.1))
        [("d", "s", MP_T2)].attach =
        List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
          [("d", "s", MP_T2)] :=
      List.attach_map_val
        (f := fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
    rw [hatt] at hsub
    have hnodOrigin : List.Nodup (List.map
        (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
        ([("d", "s", MP_T2)] : List (Lab × DataSort × SessionType))) := by
      decide
    exact hsub.nodup hnodOrigin
    · intro a ha b hb
      rcases a with ⟨⟨l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  obtain ⟨T0sG2, hmem0G2, hYU2G⟩ := mem_extBranchesWithmon_tr_yes_recv heG2mem
  have hT0sG2 : T0sG2 = SessionType.externalChoice "p" MP_F3 :=
    unique_target_of_nodup_ext hnodF2 hmem0G2 he2mem
  rw [hT0sG2] at hYU2G
  have hWFW3 : (SessionType.externalChoice "p" MP_F3).WellFormed :=
    mon_tr_yes_preserves_wf hW3mq MP_T2_WF
  have hUopG2 : UopG2 = MP_T4 :=
    mon_tr_yes_target_unique hWFW3 hYU2G hW3mp
  rw [hUopG2] at heG2mem
  have hS : mon_tr_yes (SessionType.externalChoice "s" MP_G2)
      (ext_tag.recv "s" "d" "s") MP_T4 :=
    (spec_monitor_step_iff rfl hNDU1).mpr ⟨MP_T4, heG2mem, rfl⟩
  rw [hspec]
  exact ⟨_, hFold', mon_yes_seq.step hRun1 (mon_yes_seq.step hS (mon_yes_seq.refl _))⟩
