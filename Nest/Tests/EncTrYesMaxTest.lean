import Nest.SessionUtils
/-!
# mon_tr_yesMaxTest: maximal kept-sets regression test.

The existential helper `mon_tr_yes_exist` is nondeterministic (strict subsets
allowed); the maximal `mon_tr_yes` (hereditary + coverage + source order)
rules out the singleton (coverage violation) and keeps the full list.
-/
open Cslib

/-
Regression test for the maximal kept-sets fix (`Basic.mon_tr_yes`, paper
`def:monitor-state-st`). Formerly `Nest/Counterexamplemon_tr_yesNondet.lean`:
the existential helper `mon_tr_yes_exist` is nondeterministic (strict subsets
allowed), while the maximal `mon_tr_yes` (hereditary + coverage + source-order)
rules out the singleton (coverage violation) and keeps the full list.
Kept as a test to keep the fix built.
-/

/-- Maximality witness branch: `q`-offer of `(l, s)` ending in `tEnd`. -/
def CxBranch : SessionType :=
  SessionType.externalChoice "q" [("l", "s", SessionType.tEnd)]

/-- Maximality witness branches: two senders sharing the live branch body. -/
def CxBranches : List (Role × Lab × DataSort × SessionType) :=
  [("r1", "a", "sa", CxBranch), ("r2", "b", "sb", CxBranch)]

/-- Maximality witness tag: receiving `(q, l, s)`. -/
def CxGamma : ext_tag := ext_tag.recv "q" "l" "s"

/-- Kept list keeping only the first branch target (non-maximal candidate). -/
def CxKeptOne : List (Role × Lab × DataSort × SessionType) :=
  [("r1", "a", "sa", SessionType.tEnd)]

/-- Kept list keeping both branch targets (maximal candidate). -/
def CxKeptBoth : List (Role × Lab × DataSort × SessionType) :=
  [("r1", "a", "sa", SessionType.tEnd), ("r2", "b", "sb", SessionType.tEnd)]

-- Branch type accepts the tag via base extC (existential).
/-- The witness branch accepts the witness tag (existential base step). -/
private lemma CxBranchYesE : mon_tr_yes_exist CxBranch CxGamma SessionType.tEnd := by
  unfold CxBranch CxGamma
  apply mon_tr_yes_exist.base
  apply mon_tr_yes_base.extC
  · simp
  · simp

-- Branch type accepts maximally (base derivations are maximal).
/-- The witness branch accepts the witness tag (full yes-transition). -/
private lemma CxBranchYes : mon_tr_yes CxBranch CxGamma SessionType.tEnd := by
  have hb : mon_tr_yes_base CxBranch CxGamma SessionType.tEnd := by
    unfold CxBranch CxGamma
    apply mon_tr_yes_base.extC <;> simp
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

-- Full source is off-role for q.
/-- Every branch sender differs from `q` (off-role side condition). -/
private lemma CxOffRole : ∀ p' lab' S' T0,
    (p', lab', S', T0) ∈ CxBranches → "q" ≠ p' := by
  intro p' lab' S' T0 hmem
  unfold CxBranches at hmem
  simp at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide

-- Existential fires with singleton kept (non-maximal, allowed).
/-- Existential fire keeping one branch: the choice accepts the tag into the singleton kept list. -/
theorem CxFireOneE :
    mon_tr_yes_exist (SessionType.internalChoice CxBranches) CxGamma
      (SessionType.internalChoice CxKeptOne) := by
  have hne : CxBranches ≠ [] ∧ CxKeptOne ≠ [] := by
    unfold CxBranches CxKeptOne
    constructor <;> simp
  refine mon_tr_yes_exist.pfxInt (branches := CxBranches) (kept := CxKeptOne)
    (q := "q") (lab := "l") (S := "s") hne CxOffRole rfl ?hall ?nodup ?hkey
  · intro T0 T1 r l s hSrc hKept
    unfold CxKeptOne at hKept
    simp at hKept
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hKept
    unfold CxBranches at hSrc
    simp at hSrc
    subst hSrc
    exact CxBranchYesE
  · unfold CxKeptOne
    simp
  · intro r l s T1 hKept
    unfold CxKeptOne at hKept
    simp at hKept
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hKept
    exact ⟨CxBranch, by unfold CxBranches; simp⟩

-- Existential fires with full kept.
/-- Existential fire keeping both branches: the choice accepts the tag into the full kept list. -/
theorem CxFireBothE :
    mon_tr_yes_exist (SessionType.internalChoice CxBranches) CxGamma
      (SessionType.internalChoice CxKeptBoth) := by
  have hne : CxBranches ≠ [] ∧ CxKeptBoth ≠ [] := by
    unfold CxBranches CxKeptBoth
    constructor <;> simp
  refine mon_tr_yes_exist.pfxInt (branches := CxBranches) (kept := CxKeptBoth)
    (q := "q") (lab := "l") (S := "s") hne CxOffRole rfl ?hall ?nodup ?hkey
  · intro T0 T1 r l s hSrc hKept
    unfold CxKeptBoth at hKept
    simp at hKept
    rcases hKept with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · unfold CxBranches at hSrc
      simp at hSrc
      subst hSrc
      exact CxBranchYesE
    · unfold CxBranches at hSrc
      simp at hSrc
      subst hSrc
      exact CxBranchYesE
  · unfold CxKeptBoth
    simp
  · intro r l s T1 hKept
    unfold CxKeptBoth at hKept
    simp at hKept
    rcases hKept with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨CxBranch, by unfold CxBranches; simp⟩
    · exact ⟨CxBranch, by unfold CxBranches; simp⟩

/-- The one-branch and two-branch kept choices differ (maximality is non-trivial). -/
theorem CxTargetsNe :
    SessionType.internalChoice CxKeptOne ≠
      SessionType.internalChoice CxKeptBoth := by
  intro h
  have hlist : CxKeptOne = CxKeptBoth := by injection h
  have hlen : CxKeptOne.length = CxKeptBoth.length := congrArg List.length hlist
  unfold CxKeptOne CxKeptBoth at hlen
  simp at hlen

/-- Existential version is nondeterministic. -/
theorem CxExistNotUnique :
    ∃ (M T1 T2 : SessionType) (γ : ext_tag),
      mon_tr_yes_exist M γ T1 ∧ mon_tr_yes_exist M γ T2 ∧ T1 ≠ T2 :=
  ⟨_, _, _, _, CxFireOneE, CxFireBothE, CxTargetsNe⟩

-- Maximal version fires with full kept (hereditary base + coverage + order).
/-- Full yes-transition keeping both branches (existential plus maximal). -/
theorem CxFireBoth :
    mon_tr_yes (SessionType.internalChoice CxBranches) CxGamma
      (SessionType.internalChoice CxKeptBoth) := by
  have hne : CxBranches ≠ [] ∧ CxKeptBoth ≠ [] := by
    unfold CxBranches CxKeptBoth
    constructor <;> simp
  have hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
      (r, l, s, T0) ∈ CxBranches → (r, l, s, T1) ∈ CxKeptBoth →
        mon_tr_yes_exist T0 CxGamma T1 := by
    intro T0 T1 r l s hSrc hKept
    unfold CxKeptBoth at hKept
    simp at hKept
    rcases hKept with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · unfold CxBranches at hSrc
      simp at hSrc
      subst hSrc
      exact CxBranchYesE
    · unfold CxBranches at hSrc
      simp at hSrc
      subst hSrc
      exact CxBranchYesE
  have hallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort)
      (hmemB : (r, l, s, T0) ∈ CxBranches) (hmemK : (r, l, s, T1) ∈ CxKeptBoth)
      (hsub : mon_tr_yes_exist T0 CxGamma T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 r l s hmemB hmemK hsub
    -- First constrain (r,l,s,T0) to one of the two source branches (both have
    -- target CxBranch). This substitutes T0 = CxBranch and concrete keys.
    unfold CxBranches at hmemB
    simp at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · -- r1 branch: T0 = CxBranch (externalChoice "q" ...), tag recv "q" ...
      cases hsub with
      | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
      | pfxExt hne hneq _ _ _ _ =>
        -- pfxExt needs q ≠ p, but q = "q", p = "q" (CxBranch role). Contradiction.
        simp [CxBranch, CxGamma] at hneq
    · cases hsub with
      | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
      | pfxExt hne hneq _ _ _ _ =>
        simp [CxBranch, CxGamma] at hneq
  have hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
      (r, l, s, T0) ∈ CxBranches → (∃ T1, mon_tr_yes_exist T0 CxGamma T1) →
        ∃ T1, (r, l, s, T1) ∈ CxKeptBoth := by
    intro r l s T0 hmemB _
    unfold CxBranches at hmemB
    simp at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨SessionType.tEnd, by unfold CxKeptBoth; simp⟩
    · exact ⟨SessionType.tEnd, by unfold CxKeptBoth; simp⟩
  have horder : List.Sublist
      (CxKeptBoth.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
      (CxBranches.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) := by
    unfold CxKeptBoth CxBranches CxBranch
    simp
  have hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ CxBranches → "q" ≠ p' := CxOffRole
  have hNodupKept : List.Nodup (CxKeptBoth.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) := by
    unfold CxKeptBoth; simp
  have hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
      (r, l, s, T1) ∈ CxKeptBoth → ∃ T0, (r, l, s, T0) ∈ CxBranches := by
    intro r l s T1 hKept
    unfold CxKeptBoth at hKept
    simp at hKept
    rcases hKept with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨CxBranch, by unfold CxBranches; simp⟩
    · exact ⟨CxBranch, by unfold CxBranches; simp⟩
  have hkept : SessionType.internalChoice CxKeptBoth = SessionType.internalChoice CxKeptBoth := rfl
  exact ⟨mon_tr_yes_exist.pfxInt hne hno hkept hall hNodupKept hkey,
    @mon_tr_yes_max_deriv.pfxInt CxBranches CxKeptBoth "q" "l" "s"
      (SessionType.internalChoice CxKeptBoth) hne hno hkept hall hNodupKept hkey
      hallMax hcover horder⟩

-- Singleton kept violates coverage (r2 branch acceptable but dropped).
/-- The singleton kept list is not maximal: the fuller derivation strictly extends it. -/
theorem CxOneNotMax :
    ¬ mon_tr_yes (SessionType.internalChoice CxBranches) CxGamma
      (SessionType.internalChoice CxKeptOne) := by
  rintro ⟨hE, hM⟩
  cases hM with
  | @base _ _ _ hb => cases hb
  | @pfxInt branches kept q lab S T' hne hno hkept hall hNodupKept hkey hallMax hcover horder =>
    -- kept = CxKeptOne (via hkept + target equality), but r2 acceptable.
    have hkeq : CxKeptOne = kept := by
      cases hkept
      rfl
    subst hkeq
    -- r2 branch target accepts existentially.
    have hacc : ∃ T1, mon_tr_yes_exist CxBranch CxGamma T1 := ⟨_, CxBranchYesE⟩
    have hmemB : ("r2", "b", "sb", CxBranch) ∈ CxBranches := by
      unfold CxBranches; simp
    rcases hcover "r2" "b" "sb" CxBranch hmemB hacc with ⟨T1, hmemK⟩
    unfold CxKeptOne at hmemK
    simp at hmemK
