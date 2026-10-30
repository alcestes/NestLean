import Nest.SessionUtils
/-!
# IntPfxDiamondTest: maximal-shape regression test for internal-choice receives.

Pins the `pfxInt` machinery in `Nest.SessionUtils`: source send, maximal receive
keeping exactly the acceptable branch, with explicit maximality evidence.
-/
open Cslib

/-
Maximal-shape regression test for internal-choice receives (kept as a
built test per the project strategy; formerly
`Nest.CounterexampleIntPfxDiamond`, whose `CxIntPfxDiamondFalse` refuted
the BARE `intPfx_diamond` — vacuous for the current version, which
carries the extra acceptability hypothesis `h_acc` (false on the
instance, since the out-branch continuation is `tEnd`) and is proved).

What this pins: source send (`DxSend`: `st_trans.intC`), maximal receive
keeping exactly the acceptable branch (`DxRecv`: coverage-dropping of
the `tEnd`-continuation branch, source order, `hallMax` assembly with
off-role side condition `DxOffRole`), all with explicit `pfxInt`
maximality. Guards the `pfxInt` machinery in `Nest.SessionUtils` against
regressions (complement to `Nest.ConfDiamondExtTest`, which pins
`pfxExt`).

Concretely: `branches` offers `out "p"` via a `tEnd` continuation (no
receives), plus a second branch whose continuation accepts
`recv "q" "l" "s"`. The maximal monitor transition keeps only the second
branch, so `X` cannot step with `out "p"`.
-/

/-- Diamond witness branch: `q`-offer of `(l, s)` ending in `tEnd`. -/
def DxBranch : SessionType :=
  SessionType.externalChoice "q" [("l", "s", SessionType.tEnd)]

/-- Diamond witness branches: a dead leaf plus the live `DxBranch`. -/
def DxBranches : List (Role × Lab × DataSort × SessionType) :=
  [("p", "a", "sa", SessionType.tEnd), ("r", "b", "sb", DxBranch)]

/-- Diamond witness tag: receiving `(q, l, s)`. -/
def DxGammaRecv : ext_tag := ext_tag.recv "q" "l" "s"

/-- Diamond witness kept list: the surviving `(r, b, sb)` branch. -/
def DxKept : List (Role × Lab × DataSort × SessionType) :=
  [("r", "b", "sb", SessionType.tEnd)]

/-- Diamond witness join: internal choice over the kept branches. -/
def DxX : SessionType := SessionType.internalChoice DxKept

-- `tEnd` admits no receive yes-transition (all four `Exist` constructors need
-- choice/`tRec` heads; `base` subcases need them too).
/-- `tEnd` admits no receive yes-transition (all `Exist` constructors need choice/`tRec` heads). -/
private lemma t_end_no_exist_recv {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    ¬ mon_tr_yes_exist SessionType.tEnd (ext_tag.recv q lab S) T' := by
  intro h
  cases h with
  | base hb => cases hb

-- Branch continuation accepts via base extC (existential).
/-- The witness branch accepts the witness tag (existential base step). -/
private lemma DxBranchYesE : mon_tr_yes_exist DxBranch DxGammaRecv SessionType.tEnd := by
  unfold DxBranch DxGammaRecv
  apply mon_tr_yes_exist.base
  apply mon_tr_yes_base.extC
  · simp
  · simp

-- Branch continuation accepts maximally (base derivations are maximal).
/-- The witness branch accepts the witness tag (full yes-transition: existential plus maximal). -/
private lemma DxBranchYes : mon_tr_yes DxBranch DxGammaRecv SessionType.tEnd := by
  have hb : mon_tr_yes_base DxBranch DxGammaRecv SessionType.tEnd := by
    unfold DxBranch DxGammaRecv
    apply mon_tr_yes_base.extC <;> simp
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

-- Source is off-role for "q".
/-- Every branch sender differs from `q` (off-role side condition for the diamond). -/
private lemma DxOffRole : ∀ p' lab' S' T0,
    (p', lab', S', T0) ∈ DxBranches → "q" ≠ p' := by
  intro p' lab' S' T0 hmem
  unfold DxBranches at hmem
  simp at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide

-- Source sends `out "p" "a" "sa"` to `tEnd` (first branch).
/-- Send fire: the internal choice fires `(p, a, sa)` into `tEnd`. -/
theorem DxSend : st_trans (SessionType.internalChoice DxBranches)
    (st_label.out "p" "a" "sa") SessionType.tEnd :=
  st_trans.intC (by unfold DxBranches; simp)

-- Maximal monitor transition keeps only the second branch.
/-- Receive fire: the internal choice accepts the `q`-tag, keeping only the live branch. -/
theorem DxRecv : mon_tr_yes (SessionType.internalChoice DxBranches) DxGammaRecv DxX := by
  have hne : DxBranches ≠ [] ∧ DxKept ≠ [] := by
    unfold DxBranches DxKept
    constructor <;> simp
  have hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
      (r, l, s, T0) ∈ DxBranches → (r, l, s, T1) ∈ DxKept →
        mon_tr_yes_exist T0 DxGammaRecv T1 := by
    intro T0 T1 r l s hSrc hKept
    unfold DxKept at hKept
    simp at hKept
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hKept
    unfold DxBranches at hSrc
    simp at hSrc
    subst hSrc
    exact DxBranchYesE
  have hallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort)
      (hmemB : (r, l, s, T0) ∈ DxBranches) (hmemK : (r, l, s, T1) ∈ DxKept)
      (hsub : mon_tr_yes_exist T0 DxGammaRecv T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 r l s hmemB hmemK hsub
    unfold DxKept at hmemK
    simp at hmemK
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemK
    unfold DxBranches at hmemB
    simp at hmemB
    subst hmemB
    cases hsub with
    | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
    | pfxExt hne hneq _ _ _ _ =>
      exact absurd rfl hneq
  have hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
      (r, l, s, T0) ∈ DxBranches → (∃ T1, mon_tr_yes_exist T0 DxGammaRecv T1) →
        ∃ T1, (r, l, s, T1) ∈ DxKept := by
    intro r l s T0 hmemB hex
    unfold DxBranches at hmemB
    simp at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · -- ("p","a","sa",tEnd): un acceptable — `tEnd` admits no receive.
      rcases hex with ⟨T1, hT1⟩
      exact absurd hT1 t_end_no_exist_recv
    · exact ⟨SessionType.tEnd, by unfold DxKept; simp⟩
  have horder : List.Sublist
      (DxKept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
      (DxBranches.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) := by
    unfold DxKept DxBranches DxBranch
    simp
  have hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ DxBranches → "q" ≠ p' := DxOffRole
  have hNodupKept : List.Nodup (DxKept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) := by
    unfold DxKept; simp
  have hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
      (r, l, s, T1) ∈ DxKept → ∃ T0, (r, l, s, T0) ∈ DxBranches := by
    intro r l s T1 hKept
    unfold DxKept at hKept
    simp at hKept
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hKept
    exact ⟨DxBranch, by unfold DxBranches; simp⟩
  have hkept : DxX = SessionType.internalChoice DxKept := rfl
  exact ⟨mon_tr_yes_exist.pfxInt hne hno hkept hall hNodupKept hkey,
    @mon_tr_yes_max_deriv.pfxInt DxBranches DxKept "q" "l" "s"
      DxX hne hno hkept hall hNodupKept hkey
      hallMax hcover horder⟩
