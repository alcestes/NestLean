import Nest.StuckWitness

/-!
# Evidence: monitor refusal coexists with an enabled take (single-state).

`T1` offers `inp p b` (live `b`-branch) while absorbing the off-role prefix
`[q0-x]` by pruning to the `a`-branch — so the prefix-fold monitor `M1`
refuses `recv p b`, yet the take of `(p, b, sb)` is `sq_trans`-enabled (the
arrival sits oldest-from-`p` behind the prefix). Single-state
(`monitor_fold` + refusal + enabled take, no network, no liveness): any proof
of refusal ⟹ never-take must use liveness (or star-reachability) in an
essential way — pure shape arguments cannot close it. It does NOT refute
`recvAccept` under liveness (the take lands in the pruned branch with the
prefix stranded; whether that kills liveness is the persistence wall).

This file is evidence only (not imported by `Nest.lean`).
-/

/-- Absorbing continuation: consumes the prefix, then dead. -/
private def CxRT_A1 : SessionType :=
  SessionType.externalChoice "q0" [("x", "sx", SessionType.tEnd)]

/-- Source: `b`-branch offers the arrival key, `a`-branch absorbs the prefix. -/
private def CxRT_T1 : SessionType :=
  SessionType.externalChoice "p" [(("a", "sa", CxRT_A1)), (("b", "sb", SessionType.tEnd))]

/-- The absorbed prefix. -/
private def CxRT_Qpre : Queue := [QueueMessage.msg "q0" "x" "sx"]

/-- Prefix-fold target: pruned to the live line, then drained. -/
private def CxRT_M1 : SessionType :=
  SessionType.externalChoice "p" [(("a", "sa", SessionType.tEnd))]

/-- `tEnd` admits no existential yes-transition. -/
private lemma CxRT_tEndNoExist : ∀ {γ : ext_tag} {T' : SessionType},
    ¬ mon_tr_yes_exist SessionType.tEnd γ T' := by
  intro γ T' h
  cases h with
  | base hb => cases hb

/-- Prefix fold: `recv q0-x` prunes to the `a`-line, which then drains. -/
private lemma CxRT_hPre :
    mon_tr_yes CxRT_T1 (ext_tag.recv "q0" "x" "sx") CxRT_M1 := by
  have hne : ([(("a", "sa", CxRT_A1)), (("b", "sb", SessionType.tEnd))] :
      List (Lab × DataSort × SessionType)) ≠ [] ∧
      ([(("a", "sa", SessionType.tEnd))] :
      List (Lab × DataSort × SessionType)) ≠ [] :=
    ⟨by decide, by decide⟩
  have hneq : ("q0" : Role) ≠ "p" := by decide
  have hkept : CxRT_M1 = SessionType.externalChoice "p" [("a", "sa", SessionType.tEnd)] :=
    rfl
  have hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ ([(("a", "sa", CxRT_A1)), (("b", "sb", SessionType.tEnd))] :
        List (Lab × DataSort × SessionType)) →
      (l, s, T1) ∈ ([(("a", "sa", SessionType.tEnd))] :
        List (Lab × DataSort × SessionType)) →
      mon_tr_yes_exist T0 (ext_tag.recv "q0" "x" "sx") T1 := by
    intro T0 T1 l s hmB hmK
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl⟩ := hmK
      simp only [List.mem_cons, List.mem_nil_iff] at hmB
      rcases hmB with hmB | hmB | hmB
      · obtain ⟨rfl, rfl, rfl⟩ := hmB
        apply mon_tr_yes_exist.base
        apply mon_tr_yes_base.extC
        · decide
        · simp
      · obtain ⟨h1, _⟩ := (Prod.mk.injEq ..).mp hmB
        exact absurd h1 (by decide : ("a" : Lab) ≠ "b")
      · simp at hmB
    · simp at hmK
  have hNodupKept : List.Nodup (([("a", "sa", SessionType.tEnd)] :
      List (Lab × DataSort × SessionType)).map
      (fun x : Lab × DataSort × SessionType => x.1)) := by
    decide
  have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈ ([(("a", "sa", SessionType.tEnd))] :
        List (Lab × DataSort × SessionType)) →
      ∃ T0, (l, s, T0) ∈ ([(("a", "sa", CxRT_A1)), (("b", "sb", SessionType.tEnd))] :
        List (Lab × DataSort × SessionType)) := by
    intro l s T1 hmK
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl⟩ := hmK
      exact ⟨CxRT_A1, by simp⟩
    · simp at hmK
  have hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ ([(("a", "sa", CxRT_A1)), (("b", "sb", SessionType.tEnd))] :
        List (Lab × DataSort × SessionType)) →
      (l, s, T1) ∈ ([(("a", "sa", SessionType.tEnd))] :
        List (Lab × DataSort × SessionType)) →
      ∀ (hsub : mon_tr_yes_exist T0 (ext_tag.recv "q0" "x" "sx") T1),
        mon_tr_yes_max_deriv hsub := by
    intro T0 T1 l s hmB hmK hsub
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl⟩ := hmK
      simp only [List.mem_cons, List.mem_nil_iff] at hmB
      rcases hmB with hmB | hmB | hmB
      · obtain ⟨rfl, rfl, rfl⟩ := hmB
        cases hsub with
        | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
        | pfxExt _ hneq _ _ _ _ => exact absurd rfl hneq
      · obtain ⟨h1, _⟩ := (Prod.mk.injEq ..).mp hmB
        exact absurd h1 (by decide : ("a" : Lab) ≠ "b")
      · simp at hmB
    · simp at hmK
  have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
      (l, s, T0) ∈ ([(("a", "sa", CxRT_A1)), (("b", "sb", SessionType.tEnd))] :
        List (Lab × DataSort × SessionType)) →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "q0" "x" "sx") T1) →
      ∃ T1, (l, s, T1) ∈ ([(("a", "sa", SessionType.tEnd))] :
        List (Lab × DataSort × SessionType)) := by
    intro l s T0 hmB hex
    simp only [List.mem_cons, List.mem_nil_iff] at hmB
    rcases hmB with hmB | hmB | hmB
    · obtain ⟨rfl, rfl, rfl⟩ := hmB
      exact ⟨SessionType.tEnd, by simp⟩
    · obtain ⟨rfl, rfl, rfl⟩ := hmB
      obtain ⟨T1, hex1⟩ := hex
      exact absurd hex1 CxRT_tEndNoExist
    · simp at hmB
  have horder : List.Sublist (([("a", "sa", SessionType.tEnd)] :
      List (Lab × DataSort × SessionType)).map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
      (([(("a", "sa", CxRT_A1)), (("b", "sb", SessionType.tEnd))] :
      List (Lab × DataSort × SessionType)).map
      (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) := by
    decide
  show mon_tr_yes CxRT_T1 (ext_tag.recv "q0" "x" "sx") CxRT_M1
  unfold CxRT_T1 CxRT_M1
  exact ⟨mon_tr_yes_exist.pfxExt hne hneq hkept hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxExt (hne := hne) (hneq := hneq) (hkept := hkept)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- Prefix absorption holds. -/
private lemma CxRT_hEnc : monitor_fold (CxRT_T1, CxRT_Qpre) CxRT_M1 := by
  show monitor_fold (CxRT_T1, [QueueMessage.msg "q0" "x" "sx"]) CxRT_M1
  simp only [monitor_fold, monitor_fold_aux]
  exact ⟨CxRT_M1, CxRT_hPre, rfl⟩

/-- The pruned monitor refuses the arrival key. -/
private lemma CxRT_hNo : ∀ M2, ¬ mon_tr_yes CxRT_M1 (ext_tag.recv "p" "b" "sb") M2 := by
  intro M2 hYes
  rcases hYes with ⟨hE, hM⟩
  cases hM with
  | @base _ _ _ hb =>
    cases hb with
    | extC _ hmem =>
      simp only [List.mem_cons, List.mem_nil_iff] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨h1, _⟩ := (Prod.mk.injEq ..).mp hmem
        exact absurd h1 (by decide : ("b" : Lab) ≠ "a")
      · simp at hmem
  | @pfxExt _ _ _ _ _ _ _ _ hneq _ _ _ _ _ _ _ =>
    exact absurd rfl hneq

/-- The take of the refused arrival is enabled (oldest-from-`p` behind the prefix). -/
private lemma CxRT_hTake :
    ∃ T2 Q2, sq_trans (CxRT_T1, CxRT_Qpre ++ [QueueMessage.msg "p" "b" "sb"])
      (sq_action.dequeue "p" "b" "sb") (T2, Q2) := by
  refine ⟨SessionType.tEnd, CxRT_Qpre, ?_⟩
  apply sq_trans.dequeue
  · apply st_trans.extC
    simp
  · show Queue.dequeue (CxRT_Qpre ++ [QueueMessage.msg "p" "b" "sb"])
      (QueueMessage.msg "p" "b" "sb") = some CxRT_Qpre
    simp only [CxRT_Qpre]
    decide

/-- Certified coexistence: prefix absorption + monitor refusal of the arrival
    + an enabled take of that same arrival. -/
theorem refusal_take_coexist :
    ∃ (T1 : SessionType) (Qpre : Queue) (M1 : SessionType)
      (p' : Role) (lab' : Lab) (S' : DataSort),
    monitor_fold (T1, Qpre) M1 ∧
    (∀ M2, ¬ mon_tr_yes M1 (ext_tag.recv p' lab' S') M2) ∧
    (∃ T2 Q2, sq_trans (T1, Qpre ++ [QueueMessage.msg p' lab' S'])
      (sq_action.dequeue p' lab' S') (T2, Q2)) := by
  exact ⟨CxRT_T1, CxRT_Qpre, CxRT_M1, "p", "b", "sb",
    CxRT_hEnc, CxRT_hNo, CxRT_hTake⟩
