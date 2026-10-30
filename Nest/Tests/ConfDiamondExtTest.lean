import Nest.SessionUtils
/-!
# ConfDiamondExtTest: peak-existence form of `conf_diamond_ext`.

The PEAK-EXISTENCE form of `conf_diamond_ext` (as previously stated in
`Nest.MonitorToolkit`) is false under the maximal kept-sets semantics; the
current equality-form statement is proved, and this file justifies the
restatement by exhibiting the counterexample shape.
-/
open Cslib

/-
Counterexample: the PEAK-EXISTENCE form of `conf_diamond_ext` (as previously
stated in `Nest.MonitorToolkit`) is false
under the maximal kept-sets semantics (`Basic.mon_tr_yes`, paper
`def:monitor-state-st`). The current `Nest.MonitorToolkit.conf_diamond_ext` is the
equality-form restatement — this file justifies the
restatement, it does not refute the current statement. Same pruning
phenomenon as
`Nest.CounterexampleIntPfxDiamond`: the off-role receive keeps only the
acceptable branch, while the on-role receive selects the dropped branch
(whose continuation is `tEnd` and admits no further receive). The diamond's
first conjunct (`mon_tr_yes U recv-q …` with `U = tEnd`) is then impossible.

Concretely: `externalChoice "p"` over `[("a","sa",tEnd), ("b","sb",Cb)]`.
On-role `recv "p" "a" "sa"` gives `tEnd`; off-role `recv "q" "l" "s"`
keeps only the second branch.
-/

/-- Diamond witness branch: `q`-offer of `(l, s)` ending in `tEnd`. -/
def ExBranch : SessionType :=
  SessionType.externalChoice "q" [("l", "s", SessionType.tEnd)]

/-- Diamond witness branches: two `tEnd` leaves plus the live `ExBranch`. -/
def ExBranches : List (Lab × DataSort × SessionType) :=
  [("a", "sa", SessionType.tEnd), ("b", "sb", ExBranch)]

/-- Diamond witness tag: receiving `(q, l, s)`. -/
def ExGammaQ : ext_tag := ext_tag.recv "q" "l" "s"

/-- Diamond witness kept list: the surviving `(b, sb)` branch target. -/
def ExKept : List (Lab × DataSort × SessionType) :=
  [("b", "sb", SessionType.tEnd)]

/-- Diamond witness join: `p`-choice over the kept branches. -/
def ExT1 : SessionType := SessionType.externalChoice "p" ExKept

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
private lemma ExBranchYesE : mon_tr_yes_exist ExBranch ExGammaQ SessionType.tEnd := by
  unfold ExBranch ExGammaQ
  apply mon_tr_yes_exist.base
  apply mon_tr_yes_base.extC
  · simp
  · simp

-- On-role receive gives `tEnd` (base `STMon-ExtC`, maximal via `base`).
/-- On-role fire: the `p`-headed choice accepts `(p, a, sa)` into `tEnd`. -/
theorem ExOnRole : mon_tr_yes (SessionType.externalChoice "p" ExBranches)
    (ext_tag.recv "p" "a" "sa") SessionType.tEnd := by
  have hb : mon_tr_yes_base (SessionType.externalChoice "p" ExBranches)
      (ext_tag.recv "p" "a" "sa") SessionType.tEnd := by
    apply mon_tr_yes_base.extC
    · decide
    · unfold ExBranches; simp
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

-- Off-role receive keeps only the second branch (maximal).
/-- Off-role fire: the `p`-headed choice accepts the `q`-tag, keeping only the live branch. -/
theorem ExOffRole : mon_tr_yes (SessionType.externalChoice "p" ExBranches)
    ExGammaQ ExT1 := by
  have hne : ExBranches ≠ [] ∧ ExKept ≠ [] := by
    unfold ExBranches ExKept
    constructor <;> simp
  have hneq : "q" ≠ "p" := by decide
  have hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
      (l, s, T0) ∈ ExBranches → (l, s, T1) ∈ ExKept →
        mon_tr_yes_exist T0 ExGammaQ T1 := by
    intro T0 T1 l s hSrc hKept
    unfold ExKept at hKept
    simp at hKept
    obtain ⟨rfl, rfl, rfl⟩ := hKept
    unfold ExBranches at hSrc
    simp at hSrc
    subst hSrc
    exact ExBranchYesE
  have hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
      (hmemB : (l, s, T0) ∈ ExBranches) (hmemK : (l, s, T1) ∈ ExKept)
      (hsub : mon_tr_yes_exist T0 ExGammaQ T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0 T1 l s hmemB hmemK hsub
    unfold ExKept at hmemK
    simp at hmemK
    obtain ⟨rfl, rfl, rfl⟩ := hmemK
    unfold ExBranches at hmemB
    simp at hmemB
    subst hmemB
    cases hsub with
    | base hb => exact @mon_tr_yes_max_deriv.base _ _ _ hb
    | pfxExt hne hneq _ _ _ _ =>
      exact absurd rfl hneq
  have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
      (l, s, T0) ∈ ExBranches → (∃ T1, mon_tr_yes_exist T0 ExGammaQ T1) →
        ∃ T1, (l, s, T1) ∈ ExKept := by
    intro l s T0 hmemB hex
    unfold ExBranches at hmemB
    simp at hmemB
    rcases hmemB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- ("a","sa",tEnd): unacceptable — `tEnd` admits no receive.
      rcases hex with ⟨T1, hT1⟩
      exact absurd hT1 t_end_no_exist_recv
    · exact ⟨SessionType.tEnd, by unfold ExKept; simp⟩
  have horder : List.Sublist
      (ExKept.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)))
      (ExBranches.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1))) := by
    unfold ExKept ExBranches ExBranch
    simp
  have hNodupKept : List.Nodup (ExKept.map (λ x : Lab × DataSort × SessionType => x.1)) := by
    unfold ExKept; simp
  have hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
      (l, s, T1) ∈ ExKept → ∃ T0, (l, s, T0) ∈ ExBranches := by
    intro l s T1 hKept
    unfold ExKept at hKept
    simp at hKept
    obtain ⟨rfl, rfl, rfl⟩ := hKept
    exact ⟨ExBranch, by unfold ExBranches; simp⟩
  have hkept : ExT1 = SessionType.externalChoice "p" ExKept := rfl
  exact ⟨mon_tr_yes_exist.pfxExt hne hneq hkept hall hNodupKept hkey,
    @mon_tr_yes_max_deriv.pfxExt "p" ExBranches ExKept "q" "l" "s"
      ExT1 hne hneq hkept hall hNodupKept hkey
      hallMax hcover horder⟩

/-- The diamond join is well-formed. -/
theorem ExT1WF : ExT1.WellFormed := by
  unfold ExT1 ExKept
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.externalChoice
    · simp
    · simp
    · intro x hx
      simp at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact SessionType.NoDupl.end
  · unfold SessionType.IsClosed
    simp [SessionType.fv, SessionType.fv.goExt]
  · apply SessionType.Contractive.externalChoice
    intro x hx
    simp at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact SessionType.Contractive.end
