import Nest.MonitorCo
import Nest.MonitorCoFun
import Nest.SessionUtils

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# MonitorCo corpus test: every script transition is real, and the script is
complete for the finite fragment.

This file mechanises the cross-check between the executable monitor
(`scripts-monitor-co/compute-monitor-co-transitions.py`) and the Lean
formalisation (`mon_tr_yes_co` in `Nest/MonitorCo.lean`,
`mon_tr_yes` in `Nest/MonitorLTS.lean`).

## Corpus

Ten session types (`scripts-monitor-co/t01.txt` … `t10.txt`), chosen to
cover all clauses of `mon_tr_yes_max_deriv_co`
(`base`, `pfxInt`, `pfxExt`, `recL`, `recR`), with a mixture of
internal and external choices, with and without recursive branches.
Sorts default to `"S"` (the script's default; the paper omits payloads).

| file   | type                              | script output (tags → targets)              | clauses covered              |
|--------|-----------------------------------|---------------------------------------------|------------------------------|
| t01    | `end`                             | *(none)*                                    | vacuous (anchor)             |
| t02    | `!{p!a : end}`                    | `p!a → end`                                 | `base` (`intC`)              |
| t03    | `q?x.end`                         | `q?x → end`                                 | `base` (`extC`)              |
| t04    | `!{p!a : q?x.end, r!b : end}`     | `q?x → p!a.end`; `p!a → q?x.end`; `r!b → end` | `base`, `pfxInt`           |
| t05    | `r?{a : q?x.end, b : end}`        | `q?x → r?a.end`; `r?a → q?x.end`; `r?b → end` | `base`, `pfxExt`           |
| t06    | `μX. r?{a : end, b : X}`          | `r?a → end`; `r?b → T06`                    | `base`, `recL`          |
| t07    | `μX. r?{a : q?x.end, b : X}`      | `q?x → μY. r?{a : end, b : Y}`; `r?a → q?x.end`; `r?b → T07` | `base`, `pfxExt`, `recL`, `recR` (coinductive loop) |
| t08    | `μX. !{p!a : q?x.end, r!b : X}`   | `q?x → μY. !{p!a : end, r!b : Y}`; `p!a → q?x.end`; `r!b → T08` | `base`, `pfxInt`, `recL`, `recR` (coinductive loop) |
| t09    | `μX. p!a.X`                       | `p!a → T09`                                 | `base` under recursion (`tRec`) |
| t10    | `μY. r?{a : end, b : Y}`          | `r?a → end`; `r?b → T10`                    | `base`, `recL` (loop target shape) |

## What is proved here

* **Soundness (part 1).** Every transition printed by the script is a real
  `mon_tr_yes_co` transition (`tNN_sound_*`, 19 theorems). Finite ones by
  direct constructors (`base`, `recL` + `base`, `pfxInt`/`pfxExt` with
  explicit maximal kept-lists); the two looping targets (`t07`, `t08` under
  `q?x`) by coinduction (  `mon_tr_yes_max_deriv_co.coinduct`), following the coinductive
  pattern used below (the b-branch corecursive call is the guarded
  finite-acceptable branch).
* **Finite exactness (part 2a, inductive fragment — future work).** For
  every corpus type, `mon_tr_yes` holds exactly for the script-listed rows
  *minus the two looping targets*. Foundations are in place below
  (`no_exist_end`, `ta_exist_iff` in `FinHelpers`); the per-type iff proofs
  (induction on `mon_tr_yes_exist`/`mon_tr_yes_max_deriv`, kept-list pinning
  via `hcover`, `List.Sublist` order/nodup arguments).
* **Degenerate gap (part 2b, coinductive side — future work).** The
  coinductive relation admits strictly more than the script: `recR`
  self-loops prove `mon_tr_yes_co T γ (μY. Y)` for *every* `T` and `γ`,
  so literal co-completeness is FALSE.
-/

-- ================================================================
-- Corpus: the ten script inputs as Lean types.
-- ================================================================

section Corpus

/-- t01: `end` — the script reports no transitions. -/
def T01 : SessionType := SessionType.tEnd

/-- Shared branch `q?x.end` (sorts default to `"S"`, as in the script). -/
def CoT_branch : SessionType :=
  SessionType.externalChoice "q" [("x", "S", SessionType.tEnd)]

/-- t02: `!{p!a : end}`. -/
def T02 : SessionType :=
  SessionType.internalChoice [("p", "a", "S", SessionType.tEnd)]

/-- t03: `q?x.end`. -/
def T03 : SessionType := CoT_branch

/-- t04: `!{p!a : q?x.end, r!b : end}`. -/
def T04 : SessionType :=
  SessionType.internalChoice
    [("p", "a", "S", CoT_branch), ("r", "b", "S", SessionType.tEnd)]

/-- t04, `q?x`-target `p!a.end` (singleton kept list). -/
def T04_qx : SessionType :=
  SessionType.internalChoice [("p", "a", "S", SessionType.tEnd)]

/-- t05: `r?{a : q?x.end, b : end}`. -/
def T05 : SessionType :=
  SessionType.externalChoice "r" [("a", "S", CoT_branch), ("b", "S", SessionType.tEnd)]

/-- t05, `q?x`-target `r?a.end` (singleton kept list). -/
def T05_qx : SessionType :=
  SessionType.externalChoice "r" [("a", "S", SessionType.tEnd)]

/-- t06 body: `r?{a : end, b : X}`. -/
def T06body : SessionType :=
  SessionType.externalChoice "r" [("a", "S", SessionType.tEnd), ("b", "S", SessionType.tVar "X")]

/-- t06: `μX. r?{a : end, b : X}`. -/
def T06 : SessionType := SessionType.tRec "X" T06body

/-- t06 unfolded once: `r?{a : end, b : T06}`. -/
def T06unfold : SessionType :=
  SessionType.externalChoice "r" [("a", "S", SessionType.tEnd), ("b", "S", T06)]

/-- t07 body: `r?{a : q?x.end, b : X}`. -/
def T07body : SessionType :=
  SessionType.externalChoice "r" [("a", "S", CoT_branch), ("b", "S", SessionType.tVar "X")]

/-- t07: `μX. r?{a : q?x.end, b : X}`. -/
def T07 : SessionType := SessionType.tRec "X" T07body

/-- t07 unfolded once. -/
def T07unfold : SessionType :=
  SessionType.externalChoice "r" [("a", "S", CoT_branch), ("b", "S", T07)]

/-- t07 loop target body. -/
def T07Cbody : SessionType :=
  SessionType.externalChoice "r" [("a", "S", SessionType.tEnd), ("b", "S", SessionType.tVar "Y")]

/-- t07, `q?x`-target `μY. r?{a : end, b : Y}` (script output: loop target). -/
def T07U : SessionType := SessionType.tRec "Y" T07Cbody

/-- t07 loop target unfolded once. -/
def T07Cunfold : SessionType :=
  SessionType.externalChoice "r" [("a", "S", SessionType.tEnd), ("b", "S", T07U)]

/-- t08 body: `!{p!a : q?x.end, r!b : X}`. -/
def T08body : SessionType :=
  SessionType.internalChoice [("p", "a", "S", CoT_branch), ("r", "b", "S", SessionType.tVar "X")]

/-- t08: `μX. !{p!a : q?x.end, r!b : X}`. -/
def T08 : SessionType := SessionType.tRec "X" T08body

/-- t08 unfolded once. -/
def T08unfold : SessionType :=
  SessionType.internalChoice [("p", "a", "S", CoT_branch), ("r", "b", "S", T08)]

/-- t08 loop target body. -/
def T08Cbody : SessionType :=
  SessionType.internalChoice [("p", "a", "S", SessionType.tEnd), ("r", "b", "S", SessionType.tVar "Y")]

/-- t08, `q?x`-target `μY. !{p!a : end, r!b : Y}` (script output: loop target). -/
def T08U : SessionType := SessionType.tRec "Y" T08Cbody

/-- t08 loop target unfolded once. -/
def T08Cunfold : SessionType :=
  SessionType.internalChoice [("p", "a", "S", SessionType.tEnd), ("r", "b", "S", T08U)]

/-- t09 body: `p!a.X`. -/
def T09body : SessionType :=
  SessionType.internalChoice [("p", "a", "S", SessionType.tVar "X")]

/-- t09: `μX. p!a.X`. -/
def T09 : SessionType := SessionType.tRec "X" T09body

/-- t09 unfolded once. -/
def T09unfold : SessionType :=
  SessionType.internalChoice [("p", "a", "S", T09)]

/-- t10 body: `r?{a : end, b : Y}` (same shape as the t07 loop target). -/
def T10body : SessionType :=
  SessionType.externalChoice "r" [("a", "S", SessionType.tEnd), ("b", "S", SessionType.tVar "Y")]

/-- t10: `μY. r?{a : end, b : Y}`. -/
def T10 : SessionType := SessionType.tRec "Y" T10body

/-- t10 unfolded once. -/
def T10unfold : SessionType :=
  SessionType.externalChoice "r" [("a", "S", SessionType.tEnd), ("b", "S", T10)]

/-- Tags used by the script outputs. -/
def gSndPA : ext_tag := ext_tag.send "p" "a" "S"
def gSndRB : ext_tag := ext_tag.send "r" "b" "S"
def gQx : ext_tag := ext_tag.recv "q" "x" "S"
def gRa : ext_tag := ext_tag.recv "r" "a" "S"
def gRb : ext_tag := ext_tag.recv "r" "b" "S"

end Corpus

-- ================================================================
-- Well-formedness of the corpus types (checked by computation).
-- ================================================================

section CorpusWF

private theorem T01_wf : T01.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem CoT_branch_wf : CoT_branch.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T02_wf : T02.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T03_wf : T03.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T04_wf : T04.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T04_qx_wf : T04_qx.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T05_wf : T05.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T05_qx_wf : T05_qx.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T06_wf : T06.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T06unfold_wf : T06unfold.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T07_wf : T07.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T07unfold_wf : T07unfold.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T07U_wf : T07U.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T07Cunfold_wf : T07Cunfold.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T08_wf : T08.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T08unfold_wf : T08unfold.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T08U_wf : T08U.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T08Cunfold_wf : T08Cunfold.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T09_wf : T09.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T09unfold_wf : T09unfold.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T10_wf : T10.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem T10unfold_wf : T10unfold.WellFormed := SessionType.wfCheck_sound (by decide)
private theorem tEnd_wf : SessionType.tEnd.WellFormed := SessionType.wfCheck_sound (by decide)

end CorpusWF

-- ================================================================
-- Unfolding computations (one-step unfold equations).
-- ================================================================

section UnfoldLemmas

private lemma T06_unfold_eq :
    substSessionType T06body "X" (SessionType.tRec "X" T06body) = T06unfold := by
  simp only [T06body, T06unfold, T06, substSessionType, go_ext_eq_map, List.map_cons,
    List.map_nil]
  simp

private lemma T07_unfold_eq :
    substSessionType T07body "X" (SessionType.tRec "X" T07body) = T07unfold := by
  simp only [T07body, T07unfold, T07, CoT_branch, substSessionType, go_ext_eq_map,
    List.map_cons, List.map_nil]
  simp

private lemma T07Cbody_unfold_eq :
    substSessionType T07Cbody "Y" T07U = T07Cunfold := by
  simp only [T07Cbody, T07Cunfold, T07U, substSessionType, go_ext_eq_map, List.map_cons,
    List.map_nil]
  simp

private lemma T08_unfold_eq :
    substSessionType T08body "X" (SessionType.tRec "X" T08body) = T08unfold := by
  simp only [T08body, T08unfold, T08, CoT_branch, substSessionType, go_ext_eq_map, go_int_eq_map,
    List.map_cons, List.map_nil]
  simp

private lemma T08Cbody_unfold_eq :
    substSessionType T08Cbody "Y" T08U = T08Cunfold := by
  simp only [T08Cbody, T08Cunfold, T08U, substSessionType, go_int_eq_map, List.map_cons,
    List.map_nil]
  simp

private lemma T09_unfold_eq :
    substSessionType T09body "X" (SessionType.tRec "X" T09body) = T09unfold := by
  simp only [T09body, T09unfold, T09, substSessionType, go_int_eq_map, List.map_cons,
    List.map_nil]
  simp

private lemma T10_unfold_eq :
    substSessionType T10body "Y" (SessionType.tRec "Y" T10body) = T10unfold := by
  simp only [T10body, T10unfold, T10, substSessionType, go_ext_eq_map, List.map_cons,
    List.map_nil]
  simp

end UnfoldLemmas

-- ================================================================
-- Finite-exist helpers: acceptability (`hcover`) is decidable per branch
-- because `mon_tr_yes_exist` is inductive (unlike `mon_tr_yes_co`).
-- `end` accepts nothing; `Ta` accepts exactly `q?x → end`.
-- ================================================================

section FinHelpers

/-- `end` admits no finite existential transition (all constructors need
    a choice or `tRec` head, so `cases` closes every branch). -/
private theorem no_exist_end : ∀ (γ : ext_tag) (V : SessionType),
    mon_tr_yes_exist SessionType.tEnd γ V → False := by
  intro γ V h
  cases h with
  | base hb => cases hb

/-- `Ta = q?x.end` accepts exactly `q?x → end` (finite version).
    The only possible derivation is the base rule: `pfxExt` would need a
    kept entry whose key matches the single source key `(x, S)`, forcing a
    finite derivation from `end` — impossible (`no_exist_end`). -/
theorem ta_exist_iff (γ : ext_tag) (V : SessionType)
    (h : mon_tr_yes_exist CoT_branch γ V) : γ = gQx ∧ V = SessionType.tEnd := by
  unfold CoT_branch at h
  cases h with
  | base hb =>
    cases hb with
    | extC huniq hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact ⟨rfl, rfl⟩
  | pfxExt hne hneq hkept hall hNK hkey =>
    -- `kept` is nonempty: name its head entry `(l, s, T1)`.
    obtain ⟨hd, tl, rfl⟩ := List.exists_cons_of_ne_nil hne.2
    obtain ⟨l, s, T1⟩ := hd
    -- By `hkey` that entry's key comes from the single source branch,
    -- so it must be `(x, S)` with continuation `end`.
    obtain ⟨T0, hmemB⟩ := hkey l s T1 (by simp)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemB
    obtain ⟨rfl, rfl, rfl⟩ := hmemB
    -- `hall` then demands a finite derivation from `end`: impossible.
    have hmemB' : ((("x", "S", SessionType.tEnd) : Lab × DataSort × SessionType) ∈
        [("x", "S", SessionType.tEnd)]) := by simp
    have hmemK' : (("x", "S", T1) : Lab × DataSort × SessionType) ∈
        (("x", "S", T1) :: tl) := by simp
    exact False.elim (no_exist_end _ _ (hall _ _ _ _ hmemB' hmemK'))

end FinHelpers

-- ================================================================
-- Part (1): every script transition is a genuine `mon_tr_yes_co` transition.
-- t01 has no script outputs (vacuous). Finite ones first; the two
-- coinductive loop targets afterwards.
-- ================================================================

section SoundFin

/-- t02: `p!a → end` (script output; `base` `intC`). -/
theorem t02_sound : mon_tr_yes_co T02 gSndPA SessionType.tEnd T02_wf tEnd_wf := by
  unfold T02 gSndPA
  apply mon_tr_yes_max_deriv_co.base T02_wf
  apply mon_tr_yes_base.intC
  · decide
  · simp

/-- t03: `q?x → end` (script output; `base` `extC`). -/
theorem t03_sound : mon_tr_yes_co CoT_branch gQx SessionType.tEnd CoT_branch_wf tEnd_wf := by
  unfold CoT_branch gQx
  apply mon_tr_yes_max_deriv_co.base CoT_branch_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp

/-- t04: `p!a → q?x.end` (script output; `base` `intC`). -/
theorem t04_sound_sndP : mon_tr_yes_co T04 gSndPA CoT_branch T04_wf CoT_branch_wf := by
  unfold T04 gSndPA
  apply mon_tr_yes_max_deriv_co.base T04_wf
  apply mon_tr_yes_base.intC
  · decide
  · simp

/-- t04: `r!b → end` (script output; `base` `intC`). -/
theorem t04_sound_sndR : mon_tr_yes_co T04 gSndRB SessionType.tEnd T04_wf tEnd_wf := by
  unfold T04 gSndRB
  apply mon_tr_yes_max_deriv_co.base T04_wf
  apply mon_tr_yes_base.intC
  · decide
  · simp

/-- t04: `q?x → p!a.end` (script output; `pfxInt` with maximal kept list). -/
theorem t04_sound_qx : mon_tr_yes_co T04 gQx T04_qx T04_wf T04_qx_wf := by
  unfold T04 T04_qx gQx
  refine mon_tr_yes_max_deriv_co.pfxInt T04_wf ⟨by decide, by decide⟩ ?hno ?hall ?hkey ?hcover ?horder
  · intro p' lab' S' T0 hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
  · intro T0 T1 r l s hB hK
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      rcases hK with ⟨rfl, rfl, rfl, rfl⟩
      apply mon_tr_yes_max_deriv_co.base CoT_branch_wf
      unfold CoT_branch
      apply mon_tr_yes_base.extC
      · decide
      · simp
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      simp at hK
  · intro r l s T1 hK
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hK
    refine ⟨CoT_branch, by simp, SessionType.tEnd, ?_⟩
    unfold CoT_branch
    exact mon_tr_yes_exist.base (mon_tr_yes_base.extC (by decide) (by simp))
  · intro r l s T0 hB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB ⊢
    rcases hB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨SessionType.tEnd, by simp⟩
    · obtain ⟨T1, hT1⟩ := hex
      exact False.elim (no_exist_end _ _ hT1)
  · simp only [List.map_cons, List.map_nil]
    exact List.Sublist.cons_cons _ (List.Sublist.cons _ (List.Sublist.refl _))

/-- t05: `r?a → q?x.end` (script output; `base` `extC`). -/
theorem t05_sound_ra : mon_tr_yes_co T05 gRa CoT_branch T05_wf CoT_branch_wf := by
  unfold T05 gRa
  apply mon_tr_yes_max_deriv_co.base T05_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp

/-- t05: `r?b → end` (script output; `base` `extC`). -/
theorem t05_sound_rb : mon_tr_yes_co T05 gRb SessionType.tEnd T05_wf tEnd_wf := by
  unfold T05 gRb
  apply mon_tr_yes_max_deriv_co.base T05_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp

/-- t05: `q?x → r?a.end` (script output; `pfxExt` with maximal kept list). -/
theorem t05_sound_qx : mon_tr_yes_co T05 gQx T05_qx T05_wf T05_qx_wf := by
  unfold T05 T05_qx gQx
  refine mon_tr_yes_max_deriv_co.pfxExt T05_wf ⟨by decide, by decide⟩ (by decide) ?hall ?hkey ?hcover ?horder
  · intro T0 T1 l s hB hK
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB
    rcases hB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      rcases hK with ⟨rfl, rfl, rfl⟩
      apply mon_tr_yes_max_deriv_co.base CoT_branch_wf
      unfold CoT_branch
      apply mon_tr_yes_base.extC
      · decide
      · simp
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      simp at hK
  · intro l s T1 hK
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
    obtain ⟨rfl, rfl, rfl⟩ := hK
    refine ⟨CoT_branch, by simp, SessionType.tEnd, ?_⟩
    exact mon_tr_yes_exist.base (mon_tr_yes_base.extC (by decide) (by simp))
  · intro l s T0 hB hex
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB ⊢
    rcases hB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨SessionType.tEnd, by simp⟩
    · -- `b`-branch: no finite transition from `end`.
      obtain ⟨T1, hT1⟩ := hex
      exact False.elim (no_exist_end _ _ hT1)
  · simp only [List.map_cons, List.map_nil]
    exact List.Sublist.cons_cons _ (List.Sublist.cons _ (List.Sublist.refl _))

end SoundFin

-- ================================================================
-- Finite unfolding + base targets (recursive types, non-loop tags).
-- ================================================================

section SoundFinRec

/-- t06: `r?a → end`. -/
theorem t06_sound_ra : mon_tr_yes_co T06 gRa SessionType.tEnd T06_wf tEnd_wf := by
  unfold T06
  apply mon_tr_yes_max_deriv_co.recL T06_wf
  rw [T06_unfold_eq]
  unfold T06unfold gRa
  apply mon_tr_yes_max_deriv_co.base T06unfold_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp

/-- t06: `r?b → T06` (self-loop target via unfolding + base). -/
theorem t06_sound_rb : mon_tr_yes_co T06 gRb T06 T06_wf T06_wf := by
  unfold T06
  apply mon_tr_yes_max_deriv_co.recL T06_wf
  rw [T06_unfold_eq]
  unfold T06unfold gRb T06
  apply mon_tr_yes_max_deriv_co.base T06unfold_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp [T06]

/-- t07: `r?a → q?x.end` (finite row). -/
theorem t07_sound_ra : mon_tr_yes_co T07 gRa CoT_branch T07_wf CoT_branch_wf := by
  unfold T07
  apply mon_tr_yes_max_deriv_co.recL T07_wf
  rw [T07_unfold_eq]
  unfold T07unfold gRa CoT_branch
  apply mon_tr_yes_max_deriv_co.base T07unfold_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp [CoT_branch]

/-- t07: `r?b → T07` (finite row). -/
theorem t07_sound_rb : mon_tr_yes_co T07 gRb T07 T07_wf T07_wf := by
  unfold T07
  apply mon_tr_yes_max_deriv_co.recL T07_wf
  rw [T07_unfold_eq]
  unfold T07unfold gRb T07
  apply mon_tr_yes_max_deriv_co.base T07unfold_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp [T07]

/-- t08: `p!a → q?x.end` (finite row). -/
theorem t08_sound_sndP : mon_tr_yes_co T08 gSndPA CoT_branch T08_wf CoT_branch_wf := by
  unfold T08
  apply mon_tr_yes_max_deriv_co.recL T08_wf
  rw [T08_unfold_eq]
  unfold T08unfold gSndPA CoT_branch
  apply mon_tr_yes_max_deriv_co.base T08unfold_wf
  apply mon_tr_yes_base.intC
  · decide
  · simp [CoT_branch]

/-- t08: `r!b → T08` (finite row). -/
theorem t08_sound_sndR : mon_tr_yes_co T08 gSndRB T08 T08_wf T08_wf := by
  unfold T08
  apply mon_tr_yes_max_deriv_co.recL T08_wf
  rw [T08_unfold_eq]
  unfold T08unfold gSndRB T08
  apply mon_tr_yes_max_deriv_co.base T08unfold_wf
  apply mon_tr_yes_base.intC
  · decide
  · simp [T08]

/-- t09: `p!a → T09` (self-loop via unfolding + base). -/
theorem t09_sound : mon_tr_yes_co T09 gSndPA T09 T09_wf T09_wf := by
  unfold T09
  apply mon_tr_yes_max_deriv_co.recL T09_wf
  rw [T09_unfold_eq]
  unfold T09unfold gSndPA T09
  apply mon_tr_yes_max_deriv_co.base T09unfold_wf
  apply mon_tr_yes_base.intC
  · decide
  · simp [T09]

/-- t10: `r?a → end` (finite row). -/
theorem t10_sound_ra : mon_tr_yes_co T10 gRa SessionType.tEnd T10_wf tEnd_wf := by
  unfold T10
  apply mon_tr_yes_max_deriv_co.recL T10_wf
  rw [T10_unfold_eq]
  unfold T10unfold gRa
  apply mon_tr_yes_max_deriv_co.base T10unfold_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp

/-- t10: `r?b → T10` (self-loop target via unfolding + base). -/
theorem t10_sound_rb : mon_tr_yes_co T10 gRb T10 T10_wf T10_wf := by
  unfold T10
  apply mon_tr_yes_max_deriv_co.recL T10_wf
  rw [T10_unfold_eq]
  unfold T10unfold gRb T10
  apply mon_tr_yes_max_deriv_co.base T10unfold_wf
  apply mon_tr_yes_base.extC
  · decide
  · simp [T10]

end SoundFinRec

-- ================================================================
-- Part (1), coinductive loops: the script's recursive targets.
-- t07 `q?x → μY. r?{a : end, b : Y}` and t08 `q?x → μY. !{p!a : end, r!b : Y}`
-- need genuine coinduction (finite `max_deriv` cannot close the loop:
-- `kept=[a]` fails `hcover`, while a full kept list needs maximality
-- of the loop branch itself).  We mirror the same pattern: a 4-point
-- invariant on the productive spine
-- `(T,γ,U)`, `(Bunfold,γ,U)`, `(Bunfold,γ,Cunfold)`, `(Ta,γ,end)`,
-- closed by `recL`, `recR`, full-kept `pfxExt`/`pfxInt`,
-- and the base step.
-- ================================================================

section SoundCoLoop

/-- t07, `q?x` invariant: the four points on the productive spine. -/
private def t07Inv : SessionType → ext_tag → SessionType → Prop :=
  fun T' γ' V' =>
    (T' = T07 ∧ γ' = gQx ∧ V' = T07U) ∨
    (T' = T07unfold ∧ γ' = gQx ∧ V' = T07U) ∨
    (T' = T07unfold ∧ γ' = gQx ∧ V' = T07Cunfold) ∨
    (T' = CoT_branch ∧ γ' = gQx ∧ V' = SessionType.tEnd)

/-- t07, `q?x` target (script output; the coinductive loop). -/
theorem t07_sound_qx : mon_tr_yes_co T07 gQx T07U T07_wf T07U_wf :=
  mon_tr_yes_max_deriv_co.coinduct t07Inv t07Inv_closed T07 gQx T07U (Or.inl ⟨rfl, rfl, rfl⟩)
where
  t07Inv_closed : ∀ a a_1 a_2, t07Inv a a_1 a_2 →
    a.WellFormed ∧ mon_tr_yes_base a a_1 a_2 ∨
    (∃ branches kept q lab S, (SessionType.internalChoice branches).WellFormed ∧
      (branches ≠ [] ∧ kept ≠ [])
      ∧ (∀ p' lab' S' T0, (p', lab', S', T0) ∈ branches → q ≠ p')
        ∧ (∀ T0 T1 r l s, (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
            t07Inv T0 (ext_tag.recv q lab S) T1)
        ∧ (∀ r l s T1, (r, l, s, T1) ∈ kept →
            ∃ T0, (r, l, s, T0) ∈ branches ∧
              ∃ V, mon_tr_yes_exist T0 (ext_tag.recv q lab S) V)
        ∧ (∀ r l s T0, (r, l, s, T0) ∈ branches →
            (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) → ∃ T1, (r, l, s, T1) ∈ kept)
        ∧ List.Sublist (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
          (branches.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
        ∧ a = SessionType.internalChoice branches ∧ a_1 = ext_tag.recv q lab S ∧
          a_2 = SessionType.internalChoice kept) ∨
      (∃ p branches kept q lab S, (SessionType.externalChoice p branches).WellFormed ∧
      (branches ≠ [] ∧ kept ≠ []) ∧ q ≠ p ∧
        (∀ T0 T1 l s, (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
          t07Inv T0 (ext_tag.recv q lab S) T1) ∧
        (∀ l s T1, (l, s, T1) ∈ kept →
          ∃ T0, (l, s, T0) ∈ branches ∧
            ∃ V, mon_tr_yes_exist T0 (ext_tag.recv q lab S) V) ∧
        (∀ l s T0, (l, s, T0) ∈ branches →
          (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) → ∃ T1, (l, s, T1) ∈ kept) ∧
        List.Sublist (kept.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
          (branches.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) ∧
        a = SessionType.externalChoice p branches ∧ a_1 = ext_tag.recv q lab S ∧
        a_2 = SessionType.externalChoice p kept) ∨
    (∃ X B, (SessionType.tRec X B).WellFormed ∧
      t07Inv (substSessionType B X (SessionType.tRec X B)) a_1 a_2 ∧
      a = SessionType.tRec X B) ∨
    ∃ Y C, a.WellFormed ∧
      t07Inv a a_1 (substSessionType C Y (SessionType.tRec Y C)) ∧
      a_2 = SessionType.tRec Y C := by
    intro a a_1 a_2 h
    unfold t07Inv at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- P0: `T --q?x--> U` via `recL`; needs `(Bunfold, γ, U)`.
      right; right; right; left
      refine ⟨"X", T07body, T07_wf, ?_, rfl⟩
      have hsub : substSessionType T07body "X" (SessionType.tRec "X" T07body) = T07unfold :=
        T07_unfold_eq
      have hmem : t07Inv T07unfold gQx T07U := by
        unfold t07Inv
        exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      rw [hsub]
      exact hmem
    · -- P1: `(Bunfold, γ, U)` via `recR`; needs `(Bunfold, γ, Cunfold)`.
      right; right; right; right
      refine ⟨"Y", T07Cbody, T07unfold_wf, ?_, rfl⟩
      have hsub : substSessionType T07Cbody "Y" (SessionType.tRec "Y" T07Cbody) = T07Cunfold :=
        T07Cbody_unfold_eq
      have hmem : t07Inv T07unfold gQx T07Cunfold := by
        unfold t07Inv
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      rw [hsub]
      exact hmem
    · -- P2: `(Bunfold, γ, Cunfold)` via `pfxExt` with full kept list.
      right; right; left
      refine ⟨"r",
        [("a", "S", CoT_branch), ("b", "S", T07)],
        [("a", "S", SessionType.tEnd), ("b", "S", T07U)],
        "q", "x", "S", T07unfold_wf,
        ⟨by decide, by decide⟩, by decide, ?hall, ?hkey, ?hcover, ?horder,
        rfl, rfl, rfl⟩
      · intro T0 T1 l s hB hK
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB
        rcases hB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
          simp at hK
          subst hK
          unfold t07Inv CoT_branch gQx
          exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
          simp at hK
          subst hK
          unfold t07Inv
          exact Or.inl ⟨rfl, rfl, rfl⟩
      · intro l s T1 hK
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
        rcases hK with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · refine ⟨CoT_branch, by simp, SessionType.tEnd, ?_⟩
          exact mon_tr_yes_exist.base (mon_tr_yes_base.extC (by decide) (by simp))
        · refine ⟨T07, by simp, SessionType.externalChoice "r" [("a", "S", SessionType.tEnd)], ?_⟩
          apply mon_tr_yes_exist.unfold
          show mon_tr_yes_exist (SessionType.externalChoice "r"
            [("a", "S", CoT_branch), ("b", "S", T07)])
            (ext_tag.recv "q" "x" "S")
            (SessionType.externalChoice "r" [("a", "S", SessionType.tEnd)])
          apply mon_tr_yes_exist.pfxExt (hkept := rfl)
          · exact ⟨by decide, by decide⟩
          · decide
          · intro T0 T1 l s hB hK
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
            obtain ⟨rfl, rfl, rfl⟩ := hK
            simp at hB
            subst hB
            exact mon_tr_yes_exist.base (mon_tr_yes_base.extC (by decide) (by simp))
          · exact List.nodup_singleton _
          · intro l s T1 hK
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
            obtain ⟨rfl, rfl, rfl⟩ := hK
            exact ⟨CoT_branch, by simp⟩
      · intro l s T0 hB _
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB ⊢
        rcases hB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · exact ⟨SessionType.tEnd, by simp⟩
        · exact ⟨T07U, by simp⟩
      · simp only [List.map_cons, List.map_nil]
        exact List.Sublist.refl _
    · -- P3: `(Ta, γ, end)` via `base`.
      left
      refine ⟨CoT_branch_wf, ?_⟩
      unfold CoT_branch gQx
      apply mon_tr_yes_base.extC
      · decide
      · simp

/-- t08, `q?x` invariant: the four points on the productive spine. -/
private def t08Inv : SessionType → ext_tag → SessionType → Prop :=
  fun T' γ' V' =>
    (T' = T08 ∧ γ' = gQx ∧ V' = T08U) ∨
    (T' = T08unfold ∧ γ' = gQx ∧ V' = T08U) ∨
    (T' = T08unfold ∧ γ' = gQx ∧ V' = T08Cunfold) ∨
    (T' = CoT_branch ∧ γ' = gQx ∧ V' = SessionType.tEnd)

/-- t08, `q?x` target (script output; the coinductive loop). -/
theorem t08_sound_qx : mon_tr_yes_co T08 gQx T08U T08_wf T08U_wf :=
  mon_tr_yes_max_deriv_co.coinduct t08Inv t08Inv_closed T08 gQx T08U (Or.inl ⟨rfl, rfl, rfl⟩)
where
  t08Inv_closed : ∀ a a_1 a_2, t08Inv a a_1 a_2 →
    a.WellFormed ∧ mon_tr_yes_base a a_1 a_2 ∨
    (∃ branches kept q lab S, (SessionType.internalChoice branches).WellFormed ∧
      (branches ≠ [] ∧ kept ≠ [])
      ∧ (∀ p' lab' S' T0, (p', lab', S', T0) ∈ branches → q ≠ p')
        ∧ (∀ T0 T1 r l s, (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
            t08Inv T0 (ext_tag.recv q lab S) T1)
        ∧ (∀ r l s T1, (r, l, s, T1) ∈ kept →
            ∃ T0, (r, l, s, T0) ∈ branches ∧
              ∃ V, mon_tr_yes_exist T0 (ext_tag.recv q lab S) V)
        ∧ (∀ r l s T0, (r, l, s, T0) ∈ branches →
            (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) → ∃ T1, (r, l, s, T1) ∈ kept)
        ∧ List.Sublist (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
          (branches.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
        ∧ a = SessionType.internalChoice branches ∧ a_1 = ext_tag.recv q lab S ∧
          a_2 = SessionType.internalChoice kept) ∨
      (∃ p branches kept q lab S, (SessionType.externalChoice p branches).WellFormed ∧
      (branches ≠ [] ∧ kept ≠ []) ∧ q ≠ p ∧
        (∀ T0 T1 l s, (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
          t08Inv T0 (ext_tag.recv q lab S) T1) ∧
        (∀ l s T1, (l, s, T1) ∈ kept →
          ∃ T0, (l, s, T0) ∈ branches ∧
            ∃ V, mon_tr_yes_exist T0 (ext_tag.recv q lab S) V) ∧
        (∀ l s T0, (l, s, T0) ∈ branches →
          (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) → ∃ T1, (l, s, T1) ∈ kept) ∧
        List.Sublist (kept.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
          (branches.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) ∧
        a = SessionType.externalChoice p branches ∧ a_1 = ext_tag.recv q lab S ∧
        a_2 = SessionType.externalChoice p kept) ∨
    (∃ X B, (SessionType.tRec X B).WellFormed ∧
      t08Inv (substSessionType B X (SessionType.tRec X B)) a_1 a_2 ∧
      a = SessionType.tRec X B) ∨
    ∃ Y C, a.WellFormed ∧
      t08Inv a a_1 (substSessionType C Y (SessionType.tRec Y C)) ∧
      a_2 = SessionType.tRec Y C := by
    intro a a_1 a_2 h
    unfold t08Inv at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · -- P0: `T --q?x--> U` via `recL`; needs `(Bunfold, γ, U)`.
      right; right; right; left
      refine ⟨"X", T08body, T08_wf, ?_, rfl⟩
      have hsub : substSessionType T08body "X" (SessionType.tRec "X" T08body) = T08unfold :=
        T08_unfold_eq
      have hmem : t08Inv T08unfold gQx T08U := by
        unfold t08Inv
        exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      rw [hsub]
      exact hmem
    · -- P1: `(Bunfold, γ, U)` via `recR`; needs `(Bunfold, γ, Cunfold)`.
      right; right; right; right
      refine ⟨"Y", T08Cbody, T08unfold_wf, ?_, rfl⟩
      have hsub : substSessionType T08Cbody "Y" (SessionType.tRec "Y" T08Cbody) = T08Cunfold :=
        T08Cbody_unfold_eq
      have hmem : t08Inv T08unfold gQx T08Cunfold := by
        unfold t08Inv
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      rw [hsub]
      exact hmem
    · -- P2: `(Bunfold, γ, Cunfold)` via `pfxInt` with full kept list.
      right; left
      refine ⟨[("p", "a", "S", CoT_branch), ("r", "b", "S", T08)],
        [("p", "a", "S", SessionType.tEnd), ("r", "b", "S", T08U)],
        "q", "x", "S", T08unfold_wf,
        ⟨by decide, by decide⟩, ?hno, ?hall, ?hkey, ?hcover, ?horder,
        rfl, rfl, rfl⟩
      · intro p' lab' S' T0 hmem
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
      · intro T0 T1 r l s hB hK
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB
        rcases hB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
          simp at hK
          subst hK
          unfold t08Inv CoT_branch gQx
          exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
          simp at hK
          subst hK
          unfold t08Inv
          exact Or.inl ⟨rfl, rfl, rfl⟩
      · intro r l s T1 hK
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
        rcases hK with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · refine ⟨CoT_branch, by simp, SessionType.tEnd, ?_⟩
          exact mon_tr_yes_exist.base (mon_tr_yes_base.extC (by decide) (by simp))
        · refine ⟨T08, by simp, SessionType.internalChoice [("p", "a", "S", SessionType.tEnd)], ?_⟩
          apply mon_tr_yes_exist.unfold
          show mon_tr_yes_exist (SessionType.internalChoice
            [("p", "a", "S", CoT_branch), ("r", "b", "S", T08)])
            (ext_tag.recv "q" "x" "S")
            (SessionType.internalChoice [("p", "a", "S", SessionType.tEnd)])
          apply mon_tr_yes_exist.pfxInt (hkept := rfl)
          · exact ⟨by decide, by decide⟩
          · intro p' lab' S' T0 hmem
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
            rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
          · intro T0 T1 r l s hB hK
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hK
            simp at hB
            subst hB
            exact mon_tr_yes_exist.base (mon_tr_yes_base.extC (by decide) (by simp))
          · exact List.nodup_singleton _
          · intro r l s T1 hK
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hK
            exact ⟨CoT_branch, by simp⟩
      · intro r l s T0 hB _
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB ⊢
        rcases hB with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · exact ⟨SessionType.tEnd, by simp⟩
        · exact ⟨T08U, by simp⟩
      · simp only [List.map_cons, List.map_nil]
        exact List.Sublist.refl _
    · -- P3: `(Ta, γ, end)` via `base`.
      left
      refine ⟨CoT_branch_wf, ?_⟩
      unfold CoT_branch gQx
      apply mon_tr_yes_base.extC
      · decide
      · simp

end SoundCoLoop
