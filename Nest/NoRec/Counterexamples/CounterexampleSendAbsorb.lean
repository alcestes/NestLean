import Nest.SessionUtils

/-!
# Evidence: same-state data does not discharge `hAcc`.

`monitor_fold_aux_out_aux_norec` (`Nest.SessionUtils`) commutes a session send past a
queue fold modulo `hAcc` (`∃ M', monitor_fold (T2, Qpre) M'` at the send
target). This file certifies that `hAcc` is load-bearing and independent:
a `tRec`-free, `NoRec`/`NoDupl` witness with prefix absorption AND full-queue
absorption AND a send step, yet no target absorption.

Shape: `T1 = intC [(r0,a,A), (r,b,B)]` with `A = extC q0 [x → extC p [m → end]]`
absorbing `Qpre = [q0-x]` and `B = tEnd` refusing it. The `Qpre`-fold prunes
to the `A`-line (`M1`); the full fold (`Qpre ++ [p-m]`) succeeds through it
(`Mfull`); the send selects the dead `B`-line, from which `Qpre` never folds.

Consequence: `sendAbsorb` cannot
close from same-state consistency + shapes + determinism. Remaining routes
are future-consistency + split-back (absent-`r` hole: `io_send` is external,
outside `τ*`/liveness scope) and liveness-drain (fairness yields
session-futures, not the fold-from-`T2` the conclusion demands).

This file is evidence only (not imported by `Nest.lean`).
-/

/-- Continuation after the live branch consumes `q0`-`x`: still offers `p`-`m`. -/
private def CxSA_A2 : SessionType :=
  SessionType.externalChoice "p" [("m", "sm", SessionType.tEnd)]

/-- Live branch: consumes `q0`-`x`, then offers `p`-`m`. -/
private def CxSA_A : SessionType :=
  SessionType.externalChoice "q0" [("x", "sx", CxSA_A2)]

/-- Dead branch: refuses everything. -/
private def CxSA_B : SessionType := SessionType.tEnd

/-- Source: internal choice with one absorbing and one dead branch. -/
private def CxSA_T1 : SessionType :=
  SessionType.internalChoice [(("r0", "a", "sa", CxSA_A)), (("r", "b", "sb", CxSA_B))]

/-- Prefix-fold target: pruned to the live line. -/
private def CxSA_M1 : SessionType :=
  SessionType.internalChoice [(("r0", "a", "sa", CxSA_A2))]

/-- Full-fold target: live line drained. -/
private def CxSA_Mfull : SessionType :=
  SessionType.internalChoice [(("r0", "a", "sa", SessionType.tEnd))]

/-- The absorbed prefix. -/
private def CxSA_Qpre : Queue := [QueueMessage.msg "q0" "x" "sx"]

/-- `tEnd` admits no existential yes-transition. -/
private lemma CxSA_tEndNoExist : ∀ {γ : ext_tag} {T' : SessionType},
    ¬ mon_tr_yes_exist SessionType.tEnd γ T' := by
  intro γ T' h
  cases h with
  | base hb => cases hb

private lemma CxSA_r0_ne_r : ("r0" : Role) ≠ "r" := by decide
private lemma CxSA_r0_ne_q0 : ("r0" : Role) ≠ "q0" := by decide
private lemma CxSA_r_ne_q0 : ("r" : Role) ≠ "q0" := by decide
private lemma CxSA_r0_ne_p : ("r0" : Role) ≠ "p" := by decide

/-- Source is recursion-free. -/
private lemma CxSA_T1NoRec : CxSA_T1.NoRec := by
  unfold CxSA_T1 CxSA_A CxSA_A2 CxSA_B
  apply SessionType.NoRec.internalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff] at hx
  rcases hx with rfl | rfl | h
  · apply SessionType.NoRec.externalChoice
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff] at hy
    rcases hy with rfl | h
    · apply SessionType.NoRec.externalChoice
      intro z hz
      simp only [List.mem_cons, List.mem_nil_iff] at hz
      rcases hz with rfl | h
      · exact SessionType.NoRec.end
      · simp at h
    · simp at h
  · exact SessionType.NoRec.end
  · simp at h

/-- Source has no duplicate keys. -/
private lemma CxSA_T1NoDupl : CxSA_T1.NoDupl := by
  unfold CxSA_T1 CxSA_A CxSA_A2 CxSA_B
  apply SessionType.NoDupl.internalChoice
  · decide
  · decide
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff] at hx
    rcases hx with rfl | rfl | h
    · apply SessionType.NoDupl.externalChoice
      · decide
      · decide
      · intro y hy
        simp only [List.mem_cons, List.mem_nil_iff] at hy
        rcases hy with rfl | h
        · apply SessionType.NoDupl.externalChoice
          · decide
          · decide
          · intro z hz
            simp only [List.mem_cons, List.mem_nil_iff] at hz
            rcases hz with rfl | h
            · exact SessionType.NoDupl.end
            · simp at h
        · simp at h
    · exact SessionType.NoDupl.end
    · simp at h

/-- Prefix fold: `recv q0-x` prunes to the live line. -/
private lemma CxSA_hPre :
    mon_tr_yes CxSA_T1 (ext_tag.recv "q0" "x" "sx") CxSA_M1 := by
  have hne : ([(("r0", "a", "sa", CxSA_A)), (("r", "b", "sb", CxSA_B))] :
      List (Role × Lab × DataSort × SessionType)) ≠ [] ∧
      ([(("r0", "a", "sa", CxSA_A2))] :
      List (Role × Lab × DataSort × SessionType)) ≠ [] :=
    ⟨by decide, by decide⟩
  have hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort) (T0 : SessionType),
      (p', lab', S', T0) ∈ ([(("r0", "a", "sa", CxSA_A)), (("r", "b", "sb", CxSA_B))] :
        List (Role × Lab × DataSort × SessionType)) → "q0" ≠ p' := by
    intro p' lab' S' T0 hm
    simp only [List.mem_cons, List.mem_nil_iff] at hm
    rcases hm with h | h | h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact CxSA_r0_ne_q0.symm
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact CxSA_r_ne_q0.symm
    · simp at h
  have hkept : CxSA_M1 = SessionType.internalChoice [("r0", "a", "sa", CxSA_A2)] :=
    rfl
  have hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
      (r, l, s, T0) ∈ ([(("r0", "a", "sa", CxSA_A)), (("r", "b", "sb", CxSA_B))] :
        List (Role × Lab × DataSort × SessionType)) →
      (r, l, s, T1) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) →
      mon_tr_yes_exist T0 (ext_tag.recv "q0" "x" "sx") T1 := by
    intro T0 T1 r l s hmB hmK
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmK
      simp only [List.mem_cons, List.mem_nil_iff] at hmB
      rcases hmB with hmB | hmB | hmB
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmB
        apply mon_tr_yes_exist.base
        apply mon_tr_yes_base.extC
        · decide
        · simp
      · obtain ⟨h1, _⟩ := (Prod.mk.injEq ..).mp hmB
        exact absurd h1 CxSA_r0_ne_r
      · simp at hmB
    · simp at hmK
  have hNodupKept : List.Nodup (([("r0", "a", "sa", CxSA_A2)] :
      List (Role × Lab × DataSort × SessionType)).map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) := by
    decide
  have hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
      (r, l, s, T1) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) →
      ∃ T0, (r, l, s, T0) ∈ ([(("r0", "a", "sa", CxSA_A)), (("r", "b", "sb", CxSA_B))] :
        List (Role × Lab × DataSort × SessionType)) := by
    intro r l s T1 hmK
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmK
      exact ⟨CxSA_A, by simp⟩
    · simp at hmK
  have hallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
      (r, l, s, T0) ∈ ([(("r0", "a", "sa", CxSA_A)), (("r", "b", "sb", CxSA_B))] :
        List (Role × Lab × DataSort × SessionType)) →
      (r, l, s, T1) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) →
      ∀ (hsub : mon_tr_yes_exist T0 (ext_tag.recv "q0" "x" "sx") T1),
        mon_tr_yes_max_deriv hsub := by
    intro T0 T1 r l s hmB hmK hsub
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmK
      simp only [List.mem_cons, List.mem_nil_iff] at hmB
      rcases hmB with hmB | hmB | hmB
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmB
        cases hsub with
        | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
        | pfxExt _ hneq _ _ _ _ => exact absurd rfl hneq
      · obtain ⟨h1, _⟩ := (Prod.mk.injEq ..).mp hmB
        exact absurd h1 CxSA_r0_ne_r
      · simp at hmB
    · simp at hmK
  have hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
      (r, l, s, T0) ∈ ([(("r0", "a", "sa", CxSA_A)), (("r", "b", "sb", CxSA_B))] :
        List (Role × Lab × DataSort × SessionType)) →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "q0" "x" "sx") T1) →
      ∃ T1, (r, l, s, T1) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) := by
    intro r l s T0 hmB hex
    simp only [List.mem_cons, List.mem_nil_iff] at hmB
    rcases hmB with hmB | hmB | hmB
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmB
      exact ⟨CxSA_A2, by simp⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmB
      obtain ⟨T1, hex1⟩ := hex
      unfold CxSA_B at hex1
      exact absurd hex1 CxSA_tEndNoExist
    · simp at hmB
  have horder : List.Sublist (([("r0", "a", "sa", CxSA_A2)] :
      List (Role × Lab × DataSort × SessionType)).map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
      (([(("r0", "a", "sa", CxSA_A)), (("r", "b", "sb", CxSA_B))] :
      List (Role × Lab × DataSort × SessionType)).map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) := by
    exact List.Sublist.cons_cons _ (List.Sublist.cons _ List.Sublist.slnil)
  show mon_tr_yes CxSA_T1 (ext_tag.recv "q0" "x" "sx") CxSA_M1
  unfold CxSA_T1 CxSA_M1
  exact ⟨mon_tr_yes_exist.pfxInt hne (fun p' lab' S' T0 hm => hno p' lab' S' T0 hm)
    hkept hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxInt (hne := hne) (hno := fun p' lab' S' T0 hm => hno p' lab' S' T0 hm)
      (hkept := hkept) (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- Second fold step: `recv p-m` drains the live line. -/
private lemma CxSA_hFull2 :
    mon_tr_yes CxSA_M1 (ext_tag.recv "p" "m" "sm") CxSA_Mfull := by
  have hne : ([(("r0", "a", "sa", CxSA_A2))] :
      List (Role × Lab × DataSort × SessionType)) ≠ [] ∧
      ([(("r0", "a", "sa", SessionType.tEnd))] :
      List (Role × Lab × DataSort × SessionType)) ≠ [] :=
    ⟨by decide, by decide⟩
  have hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort) (T0 : SessionType),
      (p', lab', S', T0) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) → "p" ≠ p' := by
    intro p' lab' S' T0 hm
    simp only [List.mem_cons, List.mem_nil_iff] at hm
    rcases hm with h | h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact CxSA_r0_ne_p.symm
    · simp at h
  have hkept : CxSA_Mfull = SessionType.internalChoice [("r0", "a", "sa", SessionType.tEnd)] :=
    rfl
  have hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
      (r, l, s, T0) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) →
      (r, l, s, T1) ∈ ([(("r0", "a", "sa", SessionType.tEnd))] :
        List (Role × Lab × DataSort × SessionType)) →
      mon_tr_yes_exist T0 (ext_tag.recv "p" "m" "sm") T1 := by
    intro T0 T1 r l s hmB hmK
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmK
      simp only [List.mem_cons, List.mem_nil_iff] at hmB
      rcases hmB with hmB | hmB
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmB
        apply mon_tr_yes_exist.base
        apply mon_tr_yes_base.extC
        · decide
        · simp
      · simp at hmB
    · simp at hmK
  have hNodupKept : List.Nodup (([("r0", "a", "sa", SessionType.tEnd)] :
      List (Role × Lab × DataSort × SessionType)).map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) := by
    decide
  have hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
      (r, l, s, T1) ∈ ([(("r0", "a", "sa", SessionType.tEnd))] :
        List (Role × Lab × DataSort × SessionType)) →
      ∃ T0, (r, l, s, T0) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) := by
    intro r l s T1 hmK
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmK
      exact ⟨CxSA_A2, by simp⟩
    · simp at hmK
  have hallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
      (r, l, s, T0) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) →
      (r, l, s, T1) ∈ ([(("r0", "a", "sa", SessionType.tEnd))] :
        List (Role × Lab × DataSort × SessionType)) →
      ∀ (hsub : mon_tr_yes_exist T0 (ext_tag.recv "p" "m" "sm") T1),
        mon_tr_yes_max_deriv hsub := by
    intro T0 T1 r l s hmB hmK hsub
    simp only [List.mem_cons, List.mem_nil_iff] at hmK
    rcases hmK with hmK | hmK
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmK
      simp only [List.mem_cons, List.mem_nil_iff] at hmB
      rcases hmB with hmB | hmB
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmB
        cases hsub with
        | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
        | pfxExt _ hneq _ _ _ _ => exact absurd rfl hneq
      · simp at hmB
    · simp at hmK
  have hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
      (r, l, s, T0) ∈ ([(("r0", "a", "sa", CxSA_A2))] :
        List (Role × Lab × DataSort × SessionType)) →
      (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "p" "m" "sm") T1) →
      ∃ T1, (r, l, s, T1) ∈ ([(("r0", "a", "sa", SessionType.tEnd))] :
        List (Role × Lab × DataSort × SessionType)) := by
    intro r l s T0 hmB _hex
    simp only [List.mem_cons, List.mem_nil_iff] at hmB
    rcases hmB with hmB | hmB
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hmB
      exact ⟨SessionType.tEnd, by simp⟩
    · simp at hmB
  have horder : List.Sublist (([("r0", "a", "sa", SessionType.tEnd)] :
      List (Role × Lab × DataSort × SessionType)).map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
      (([(("r0", "a", "sa", CxSA_A2))] :
      List (Role × Lab × DataSort × SessionType)).map
      (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) := by
    exact List.Sublist.refl _
  show mon_tr_yes CxSA_M1 (ext_tag.recv "p" "m" "sm") CxSA_Mfull
  unfold CxSA_M1 CxSA_Mfull
  exact ⟨mon_tr_yes_exist.pfxInt hne (fun p' lab' S' T0 hm => hno p' lab' S' T0 hm)
    hkept hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxInt (hne := hne) (hno := fun p' lab' S' T0 hm => hno p' lab' S' T0 hm)
      (hkept := hkept) (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩

/-- Prefix absorption holds. -/
private lemma CxSA_hEncPre : monitor_fold (CxSA_T1, CxSA_Qpre) CxSA_M1 := by
  show monitor_fold (CxSA_T1, [QueueMessage.msg "q0" "x" "sx"]) CxSA_M1
  simp only [monitor_fold, monitor_fold_aux]
  exact ⟨CxSA_M1, CxSA_hPre, rfl⟩

/-- Full-queue absorption holds (through the pruned line). -/
private lemma CxSA_hEncFull :
    monitor_fold (CxSA_T1, CxSA_Qpre ++ [QueueMessage.msg "p" "m" "sm"] ++ ([] : Queue))
      CxSA_Mfull := by
  show monitor_fold (CxSA_T1, [QueueMessage.msg "q0" "x" "sx", QueueMessage.msg "p" "m" "sm"])
    CxSA_Mfull
  simp only [monitor_fold, monitor_fold_aux]
  exact ⟨CxSA_M1, CxSA_hPre, CxSA_Mfull, CxSA_hFull2, rfl⟩

/-- The send selects the dead line. -/
private lemma CxSA_hST : st_trans CxSA_T1 (st_label.out "r" "b" "sb") CxSA_B :=
  st_trans.intC (by simp [CxSA_B])

/-- Certified refutation: prefix + full absorption + send hold, yet the
    send target absorbs nothing — `hAcc` is independent of same-state data. -/
theorem sendAbsorb_sameState_false_norec :
    ∃ (T1 T2 M1 Mfull : SessionType) (Qpre : Queue)
      (p r : Role) (lab : Lab) (S : DataSort) (lab' : Lab) (S' : DataSort),
    T1.NoRec ∧ T1.NoDupl ∧
    monitor_fold (T1, Qpre) M1 ∧
    monitor_fold (T1, Qpre ++ [QueueMessage.msg p lab S] ++ ([] : Queue)) Mfull ∧
    st_trans T1 (st_label.out r lab' S') T2 ∧
    ¬ ∃ M2, monitor_fold (T2, Qpre) M2 := by
  refine ⟨CxSA_T1, CxSA_B, CxSA_M1, CxSA_Mfull, CxSA_Qpre,
    "p", "r", "m", "sm", "b", "sb",
    CxSA_T1NoRec, CxSA_T1NoDupl, CxSA_hEncPre, CxSA_hEncFull, CxSA_hST, ?_⟩
  intro hCon
  obtain ⟨M2, hM2⟩ := hCon
  simp only [monitor_fold, monitor_fold_aux, CxSA_Qpre] at hM2
  obtain ⟨Tmid, hYes, _⟩ := hM2
  unfold CxSA_B at hYes
  exact CxSA_tEndNoExist hYes.1
