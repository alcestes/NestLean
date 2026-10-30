import Nest.NetworkLTS

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# MonitorLTS: Monitor encoder and monitored networks.

Monitor-state encoder (`mon_tr_yes`/`mon_tr_no`/`monitor_fold`), monitored session and
network LTSs, consistent instrumentation, and internal bisimilarity.
-/

-- ================================================================
-- Monitor state (encoder) from session type
-- ================================================================

/-- Labels for the encoder (monitor state) LTS.
    ::= γ✓  |  γ✗   where γ = p!lab(S) | p?lab(S) -/
inductive mon_verdict : Type where
  | yes : ext_tag → mon_verdict
  | no : ext_tag → mon_verdict
  deriving DecidableEq

/-- Base yes-transitions: `intC`, `extC`, `tRec` only (well-behaved for `inductive`).
    The `intPfx`/`extPfx` rules are added via a separate `def` below to avoid
    kernel positivity restrictions. -/
inductive mon_tr_yes_base : SessionType → ext_tag → SessionType → Prop where
  | intC {branches : List (Role × Lab × DataSort × SessionType)}
      (h_unique : List.Nodup (List.map (λ x => (x.1, x.2.1, x.2.2.1)) branches))
      {p : Role} {lab : Lab} {S : DataSort} {T : SessionType}
      (h : (p, lab, S, T) ∈ branches) :
    mon_tr_yes_base (SessionType.internalChoice branches) (ext_tag.send p lab S) T
  | extC {branches : List (Lab × DataSort × SessionType)}
      (h_unique : List.Nodup (List.map (λ x => (x.1, x.2.1)) branches))
      {p : Role} {lab : Lab} {S : DataSort} {T : SessionType}
      (h : (lab, S, T) ∈ branches) :
    mon_tr_yes_base (SessionType.externalChoice p branches) (ext_tag.recv p lab S) T
  | tRec {X : String} {T T' : SessionType} {γ : ext_tag}
      (h : mon_tr_yes_base (substSessionType T X (SessionType.tRec X T)) γ T') :
    mon_tr_yes_base (SessionType.tRec X T) γ T'

/-- All-closed branch targets have empty concatenated free variables (internal choices). -/
private lemma fv_goInt_nil_of_all_closed (l : List (Role × Lab × DataSort × SessionType))
    (h : ∀ x ∈ l, SessionType.IsClosed x.2.2.2) : SessionType.fv.goInt l = [] := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      rcases hd with ⟨p, lab, S, T0⟩
      simp [SessionType.fv.goInt, List.append_eq_nil_iff]
      constructor
      · have hT0 : T0.fv = [] := by
          have := h (p, lab, S, T0) (by simp)
          simpa [SessionType.IsClosed] using this
        exact hT0
      · apply ih
        intro x hx
        exact h x (List.mem_cons_of_mem (p, lab, S, T0) hx)

/-- All-closed branch targets have empty concatenated free variables (external choices). -/
private lemma fv_goExt_nil_of_all_closed (l : List (Lab × DataSort × SessionType))
    (h : ∀ x ∈ l, SessionType.IsClosed x.2.2) : SessionType.fv.goExt l = [] := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      rcases hd with ⟨lab, S, T0⟩
      simp [SessionType.fv.goExt, List.append_eq_nil_iff]
      constructor
      · have := h (lab, S, T0) (by simp)
        simpa [SessionType.IsClosed] using this
      · apply ih
        intro x hx
        exact h x (List.mem_cons_of_mem (lab, S, T0) hx)

/-- A branch of a `NoDupl` internal choice is `NoDupl`. -/
lemma noDupl_of_mem_intBranches {branches : List (Role × Lab × DataSort × SessionType)}
    (hND : SessionType.NoDupl (SessionType.internalChoice branches)) {x : Role × Lab × DataSort × SessionType}
    (hmem : x ∈ branches) : SessionType.NoDupl x.2.2.2 := by
  cases hND with
  | internalChoice h_nodup h_nonempty h_branches => exact h_branches x hmem

/-- A branch of a recursion-free internal choice is recursion-free. -/
lemma noRec_of_mem_intBranches {branches : List (Role × Lab × DataSort × SessionType)}
    (hNR : SessionType.NoRec (SessionType.internalChoice branches)) {x : Role × Lab × DataSort × SessionType}
    (hmem : x ∈ branches) : SessionType.NoRec x.2.2.2 := by
  cases hNR with
  | internalChoice h_branches => exact h_branches x hmem

/-- A branch of a closed internal choice is closed. -/
lemma isClosed_of_mem_intBranches {branches : List (Role × Lab × DataSort × SessionType)}
    (hCl : SessionType.IsClosed (SessionType.internalChoice branches)) {x : Role × Lab × DataSort × SessionType}
    (hmem : x ∈ branches) : SessionType.IsClosed x.2.2.2 := by
  unfold SessionType.IsClosed at hCl ⊢
  simp [SessionType.fv] at hCl
  exact fv_nil_of_goInt_nil branches hCl x hmem

/-- A branch of a contractive internal choice is contractive. -/
lemma isContractive_of_mem_intBranches {branches : List (Role × Lab × DataSort × SessionType)}
    (hCo : SessionType.Contractive (SessionType.internalChoice branches)) {x : Role × Lab × DataSort × SessionType}
    (hmem : x ∈ branches) : SessionType.Contractive x.2.2.2 := by
  cases hCo with
  | internalChoice h_branches => exact h_branches x hmem

/-- A branch of a `NoDupl` external choice is `NoDupl`. -/
lemma noDupl_of_mem_extBranches {branches : List (Lab × DataSort × SessionType)}
    (hND : SessionType.NoDupl (SessionType.externalChoice r branches)) {x : Lab × DataSort × SessionType}
    (hmem : x ∈ branches) : SessionType.NoDupl x.2.2 := by
  cases hND with
  | externalChoice h_nodup h_nonempty h_branches => exact h_branches x hmem

/-- A branch of a recursion-free external choice is recursion-free. -/
lemma noRec_of_mem_extBranches {branches : List (Lab × DataSort × SessionType)}
    (hNR : SessionType.NoRec (SessionType.externalChoice r branches)) {x : Lab × DataSort × SessionType}
    (hmem : x ∈ branches) : SessionType.NoRec x.2.2 := by
  cases hNR with
  | externalChoice h_branches => exact h_branches x hmem

/-- A branch of a closed external choice is closed. -/
lemma isClosed_of_mem_extBranches {branches : List (Lab × DataSort × SessionType)}
    (hCl : SessionType.IsClosed (SessionType.externalChoice r branches)) {x : Lab × DataSort × SessionType}
    (hmem : x ∈ branches) : SessionType.IsClosed x.2.2 := by
  unfold SessionType.IsClosed at hCl ⊢
  simp [SessionType.fv] at hCl
  exact fv_nil_of_goExt_nil branches hCl x hmem

/-- A branch of a contractive external choice is contractive. -/
lemma isContractive_of_mem_extBranches {branches : List (Lab × DataSort × SessionType)}
    (hCo : SessionType.Contractive (SessionType.externalChoice r branches)) {x : Lab × DataSort × SessionType}
    (hmem : x ∈ branches) : SessionType.Contractive x.2.2 := by
  cases hCo with
  | externalChoice h_branches => exact h_branches x hmem

-- ================================================================
-- Balanced API + uniformity consequences used by the recursive prune
-- correspondence.
-- ================================================================

/-- If `mon_tr_yes_base T γ T'` and `T` is well-formed, then `T'` is well-formed. -/
lemma mon_tr_yes_base_preserves_wf {T T' : SessionType} {γ : ext_tag}
    (h_enc : mon_tr_yes_base T γ T') (h_wf : SessionType.WellFormed T) : SessionType.WellFormed T' := by
  induction h_enc with
  | intC h_unique h_mem =>
      rename_i branches p lab S T0
      rcases h_wf with ⟨hND, hCl, hCo⟩
      unfold SessionType.WellFormed
      constructor
      · simpa using noDupl_of_mem_intBranches hND h_mem
      · constructor
        · exact isClosed_of_mem_intBranches hCl h_mem
        · simpa using isContractive_of_mem_intBranches hCo h_mem
  | extC h_unique h_mem =>
      rename_i branches p lab S T0
      rcases h_wf with ⟨hND, hCl, hCo⟩
      unfold SessionType.WellFormed
      constructor
      · simpa using noDupl_of_mem_extBranches hND h_mem
      · constructor
        · exact isClosed_of_mem_extBranches hCl h_mem
        · simpa using isContractive_of_mem_extBranches hCo h_mem
  | tRec h_enc' ih =>
      rename_i X T0 T1 γ0
      rcases h_wf with ⟨hND, hCl, hCo⟩
      have hWF_sub : (substSessionType T0 X (SessionType.tRec X T0)).WellFormed := by
        unfold SessionType.WellFormed
        constructor
        · cases hND with
          | tRec hND0 => exact NoDupl_subst hND0 (SessionType.NoDupl.tRec hND0)
        · constructor
          · unfold SessionType.IsClosed
            rw [fv_subst_aux T0 X (SessionType.tRec X T0) hCl]
            simpa [SessionType.IsClosed, SessionType.fv] using hCl
          · cases hCo with
            | tRec hCo0 hG0 =>
                exact IsContractive_subst hCo0 (SessionType.Contractive.tRec hCo0 hG0) hCl
      exact ih hWF_sub

-- ================================================================
-- Unfold normal forms for STMon-Rec.
-- A single top-level unfold is functional; chains that reach a non-`tRec`
-- head agree (no termination needed for uniqueness) and exist for closed
-- contractive types (`unfoldStar_normal_exists`). Placed here (ahead of
-- `mon_tr_yes`/`mon_tr_no`, which need it).
-- ================================================================

/-- Single top-level `tRec` unfold (paper `STMon-Rec` direction, session side). -/
inductive Unfold1 : SessionType → SessionType → Prop where
  | tRec {X : String} {B : SessionType} :
      Unfold1 (SessionType.tRec X B) (substSessionType B X (SessionType.tRec X B))

/-- Reflexive-transitive unfold closure (custom induction-friendly form, like `st_seq`). -/
inductive UnfoldStar : SessionType → SessionType → Prop where
  | refl (T : SessionType) : UnfoldStar T T
  | step {T U V : SessionType} (h1 : Unfold1 T U) (h2 : UnfoldStar U V) :
      UnfoldStar T V

/-- Head-normal: not `tRec`-headed (positive form, cases-friendly). -/
def IsHeadNF : SessionType → Prop
  | .tEnd => True
  | .tVar _ => True
  | .internalChoice _ => True
  | .externalChoice _ _ => True
  | .tRec _ _ => False

/-- Existential (non-maximal) yes-transition helper: paper `STMon-Rec` unfolds at any
    depth, so the prefix rules take full (deep) premises on branches instead
    of the rigid kept-computation. Existential kept-lists (no maximality):
    kept entries pair to sources by key-membership, no `choose`, no filterMap.
    This helper is deliberately nondeterministic (strict subsets allowed) and
    exists only as induction infrastructure for the maximal version below.
    `hNodupKept` + `hkey` are load-bearing for preservation (see below).
    `hkey` uses `∃` over locals only (no `mon_tr_yes_exist`) to respect
    the kernel's nested-inductive restriction (`∃` + `∧` + self is rejected). -/
inductive mon_tr_yes_exist : SessionType → ext_tag → SessionType → Prop where
  | base {T : SessionType} {γ : ext_tag} {V : SessionType}
      (h : mon_tr_yes_base T γ V) : mon_tr_yes_exist T γ V
  | pfxInt {branches kept : List (Role × Lab × DataSort × SessionType)}
      {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
      (hne : branches ≠ [] ∧ kept ≠ [])
      (hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ branches → q ≠ p')
      (hkept : T' = SessionType.internalChoice kept)
      (hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
        (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1)
      (hNodupKept : List.Nodup (kept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))))
      (hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
        (r, l, s, T1) ∈ kept → ∃ T0, (r, l, s, T0) ∈ branches) :
      mon_tr_yes_exist (SessionType.internalChoice branches) (ext_tag.recv q lab S) T'
  | pfxExt {p : Role} {branches kept : List (Lab × DataSort × SessionType)}
      {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
      (hne : branches ≠ [] ∧ kept ≠ [])
      (hneq : q ≠ p)
      (hkept : T' = SessionType.externalChoice p kept)
      (hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
        (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1)
      (hNodupKept : List.Nodup (kept.map (λ x : Lab × DataSort × SessionType => x.1)))
      (hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
        (l, s, T1) ∈ kept → ∃ T0, (l, s, T0) ∈ branches) :
      mon_tr_yes_exist (SessionType.externalChoice p branches) (ext_tag.recv q lab S) T'
  | unfold {X : String} {B : SessionType} {γ : ext_tag} {V : SessionType}
      (h : mon_tr_yes_exist (substSessionType B X (SessionType.tRec X B)) γ V) :
      mon_tr_yes_exist (SessionType.tRec X B) γ V

/-- Maximal-derivation predicate over `mon_tr_yes_exist` proofs (paper
    `STMon-IntPfx` / `STMon-ExtPfx` maximal `K`, `def:monitor-state-st`):
    hereditary maximality (every subderivation maximal) + coverage (every
    acceptable source branch kept) + source-order preservation (kept keys form
    a sublist of source keys, so the maximal kept list is unique as a list).
    Defined as a separate inductive indexed by existential proofs to respect
    the kernel's strict positivity (maximality mentions `mon_tr_yes_exist`,
    a different inductive, negatively — allowed; self-occurrences for
    subderivations are positive). -/
inductive mon_tr_yes_max_deriv : ∀ {T : SessionType} {γ : ext_tag} {V : SessionType},
    mon_tr_yes_exist T γ V → Prop where
  | base {T : SessionType} {γ : ext_tag} {V : SessionType}
      {h : mon_tr_yes_base T γ V} : mon_tr_yes_max_deriv (mon_tr_yes_exist.base h)
  | pfxInt {branches kept : List (Role × Lab × DataSort × SessionType)}
      {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
      {hne : branches ≠ [] ∧ kept ≠ []}
      {hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ branches → q ≠ p'}
      {hkept : T' = SessionType.internalChoice kept}
      {hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
        (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1}
      {hNodupKept : List.Nodup (kept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)))}
      {hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
        (r, l, s, T1) ∈ kept → ∃ T0, (r, l, s, T0) ∈ branches}
      (hallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort)
        (hmemB : (r, l, s, T0) ∈ branches) (hmemK : (r, l, s, T1) ∈ kept)
        (hsub : mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1),
        mon_tr_yes_max_deriv hsub)
      (hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
        (r, l, s, T0) ∈ branches → (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) →
          ∃ T1, (r, l, s, T1) ∈ kept)
      (horder : List.Sublist (kept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
        (branches.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))) :
      mon_tr_yes_max_deriv (mon_tr_yes_exist.pfxInt hne hno hkept hall hNodupKept hkey)
  | pfxExt {p : Role} {branches kept : List (Lab × DataSort × SessionType)}
      {q : Role} {lab : Lab} {S : DataSort} {T' : SessionType}
      {hne : branches ≠ [] ∧ kept ≠ []}
      {hneq : q ≠ p}
      {hkept : T' = SessionType.externalChoice p kept}
      {hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
        (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1}
      {hNodupKept : List.Nodup (kept.map (λ x : Lab × DataSort × SessionType => x.1))}
      {hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
        (l, s, T1) ∈ kept → ∃ T0, (l, s, T0) ∈ branches}
      (hallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
        (hmemB : (l, s, T0) ∈ branches) (hmemK : (l, s, T1) ∈ kept)
        (hsub : mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1),
        mon_tr_yes_max_deriv hsub)
      (hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
        (l, s, T0) ∈ branches → (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) →
          ∃ T1, (l, s, T1) ∈ kept)
      (horder : List.Sublist (kept.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)))
        (branches.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)))) :
      mon_tr_yes_max_deriv (mon_tr_yes_exist.pfxExt hne hneq hkept hall hNodupKept hkey)
  | unfold {X : String} {B : SessionType} {γ : ext_tag} {V : SessionType}
      {h : mon_tr_yes_exist (substSessionType B X (SessionType.tRec X B)) γ V}
      (hmax : mon_tr_yes_max_deriv h) :
      mon_tr_yes_max_deriv (mon_tr_yes_exist.unfold h)

/-- Maximal yes-transition (paper `def:monitor-state-st`): `STMon-IntC` /
    `STMon-ExtC` via `base`, `STMon-IntPfx` / `STMon-ExtPfx` via maximal
    `pfxInt` / `pfxExt` (maximal nonempty `K ⊆ I`, off-role side condition,
    every kept branch has a transition, every acceptable source branch kept,
    source order preserved, hence the target is unique), `STMon-Rec` via
    `unfold`. `STMon-Bad` is `mon_tr_no` below (no maximal `yes` derivation).
    Defined as an existential maximal derivation (deterministic, see
    `mon_tr_yes_target_unique` in `Nest.MonitorToolkit`); the underlying
    `mon_tr_yes_exist` retains induction infrastructure. -/
def mon_tr_yes (T : SessionType) (γ : ext_tag) (V : SessionType) : Prop :=
  ∃ h : mon_tr_yes_exist T γ V, mon_tr_yes_max_deriv h

-- Exist helpers (induction infrastructure for the maximal version).
/-- Existential yes-derivations invert at `tRec` heads into derivations from the unfolded body. -/
lemma mon_tr_yes_exist_trec_inv {X : String} {B : SessionType} {γ : ext_tag} {V : SessionType}
    (h : mon_tr_yes_exist (SessionType.tRec X B) γ V) :
    mon_tr_yes_exist (substSessionType B X (SessionType.tRec X B)) γ V := by
  cases h with
  | base hb =>
    cases hb with
    | tRec hsub => exact mon_tr_yes_exist.base hsub
  | unfold hsub => exact hsub

/-- Maximal yes-derivations invert at `tRec` heads into derivations from the unfolded body. -/
lemma mon_tr_yes_trec_inv {X : String} {B : SessionType} {γ : ext_tag} {V : SessionType}
    (h : mon_tr_yes (SessionType.tRec X B) γ V) :
    mon_tr_yes (substSessionType B X (SessionType.tRec X B)) γ V := by
  rcases h with ⟨hE, hM⟩
  cases hM with
  | @base _ _ _ hb =>
    cases hb with
    | tRec hsub =>
      exact ⟨mon_tr_yes_exist.base hsub, @mon_tr_yes_max_deriv.base _ _ _ hsub⟩
  | @unfold _ _ _ _ hsub hmax =>
    exact ⟨hsub, hmax⟩

/-- Existential yes-derivations lift backward along `UnfoldStar` chains (`Rec`-lifting per step,
   then transitivity; same proof shape as `st_trans_unfold_chain`). -/
lemma mon_tr_yes_unfold_lift {T U V : SessionType} {γ : ext_tag}
    (hS : UnfoldStar T U) (hD : mon_tr_yes U γ V) : mon_tr_yes T γ V := by
  induction hS with
  | refl => exact hD
  | step g _ ih =>
    cases g with
    | @tRec X B =>
      rcases ih hD with ⟨hE, hM⟩
      -- ih gives maximal for U; lift one unfold step preserves maximality
      -- via `MaxDeriv.unfold` (hereditary maximality comes from hM).
      exact ⟨mon_tr_yes_exist.unfold hE, mon_tr_yes_max_deriv.unfold hM⟩

/-- No-transitions for the monitor state ⟦T⟧ (STMon-Bad):
    deep-faithful absence — no `mon_tr_yesD` derivation. Cannot be part of
    mon_tr_yes due to the non-positive occurrence of the negation. -/
inductive mon_tr_no : SessionType → ext_tag → SessionType → Prop where
  | bad {T : SessionType} {γ : ext_tag}
      (h : ∀ V : SessionType, ¬ mon_tr_yes T γ V) :
    mon_tr_no T γ T

/-- Combined yes/no LTS for the monitor state ⟦T⟧ with botched support for recursion. -/
def mon_tr (T : SessionType) (ℓ : mon_verdict) (T' : SessionType) : Prop :=
  match ℓ with
  | mon_verdict.yes γ => mon_tr_yes T γ T'
  | mon_verdict.no γ => mon_tr_no T γ T'

/-- If `mon_tr_yes_exist T γ T'` and `T` is well-formed, then `T'` is well-formed
    (induction infrastructure for the maximal version below). -/
lemma mon_tr_yes_exist_preserves_wf {T T' : SessionType} {γ : ext_tag}
    (h_enc : mon_tr_yes_exist T γ T') (h_wf : SessionType.WellFormed T) : SessionType.WellFormed T' := by
  revert h_wf
  induction h_enc with
  | base hb =>
    intro h_wf
    exact mon_tr_yes_base_preserves_wf hb h_wf
  | @pfxInt branches kept q lab S T' hne hno hkept hall hNodupKept hkey ih =>
    intro h_wf
    subst hkept
    rcases h_wf with ⟨hND, hCl, hCo⟩
    refine ⟨?_, ?_, ?_⟩
    · apply SessionType.NoDupl.internalChoice hNodupKept hne.2 ?_
      intro x hx
      rcases x with ⟨r, l, s, T1⟩
      obtain ⟨T0, hmem0⟩ := hkey r l s T1 hx
      have hWF0 : SessionType.WellFormed T0 :=
        ⟨noDupl_of_mem_intBranches hND hmem0,
          isClosed_of_mem_intBranches hCl hmem0,
          isContractive_of_mem_intBranches hCo hmem0⟩
      have hWF1 := ih T0 T1 r l s hmem0 hx hWF0
      exact hWF1.1
    · show SessionType.IsClosed (SessionType.internalChoice kept)
      unfold SessionType.IsClosed
      simp only [SessionType.fv]
      exact fv_goInt_nil_of_all_closed kept (by
        intro x hx
        rcases x with ⟨r, l, s, T1⟩
        obtain ⟨T0, hmem0⟩ := hkey r l s T1 hx
        have hWF0 : SessionType.WellFormed T0 :=
          ⟨noDupl_of_mem_intBranches hND hmem0,
            isClosed_of_mem_intBranches hCl hmem0,
            isContractive_of_mem_intBranches hCo hmem0⟩
        have hWF1 := ih T0 T1 r l s hmem0 hx hWF0
        simpa [SessionType.IsClosed] using hWF1.2.1)
    · apply SessionType.Contractive.internalChoice ?_
      intro x hx
      rcases x with ⟨r, l, s, T1⟩
      obtain ⟨T0, hmem0⟩ := hkey r l s T1 hx
      have hWF0 : SessionType.WellFormed T0 :=
        ⟨noDupl_of_mem_intBranches hND hmem0,
          isClosed_of_mem_intBranches hCl hmem0,
          isContractive_of_mem_intBranches hCo hmem0⟩
      have hWF1 := ih T0 T1 r l s hmem0 hx hWF0
      exact hWF1.2.2
  | @pfxExt p branches kept q lab S T' hne hneq hkept hall hNodupKept hkey ih =>
    intro h_wf
    subst hkept
    rcases h_wf with ⟨hND, hCl, hCo⟩
    refine ⟨?_, ?_, ?_⟩
    · apply SessionType.NoDupl.externalChoice hNodupKept hne.2 ?_
      intro x hx
      rcases x with ⟨l, s, T1⟩
      obtain ⟨T0, hmem0⟩ := hkey l s T1 hx
      have hWF0 : SessionType.WellFormed T0 :=
        ⟨noDupl_of_mem_extBranches hND hmem0,
          isClosed_of_mem_extBranches hCl hmem0,
          isContractive_of_mem_extBranches hCo hmem0⟩
      have hWF1 := ih T0 T1 l s hmem0 hx hWF0
      exact hWF1.1
    · show SessionType.IsClosed (SessionType.externalChoice p kept)
      unfold SessionType.IsClosed
      simp only [SessionType.fv]
      exact fv_goExt_nil_of_all_closed kept (by
        intro x hx
        rcases x with ⟨l, s, T1⟩
        obtain ⟨T0, hmem0⟩ := hkey l s T1 hx
        have hWF0 : SessionType.WellFormed T0 :=
          ⟨noDupl_of_mem_extBranches hND hmem0,
            isClosed_of_mem_extBranches hCl hmem0,
            isContractive_of_mem_extBranches hCo hmem0⟩
        have hWF1 := ih T0 T1 l s hmem0 hx hWF0
        simpa [SessionType.IsClosed] using hWF1.2.1)
    · apply SessionType.Contractive.externalChoice ?_
      intro x hx
      rcases x with ⟨l, s, T1⟩
      obtain ⟨T0, hmem0⟩ := hkey l s T1 hx
      have hWF0 : SessionType.WellFormed T0 :=
        ⟨noDupl_of_mem_extBranches hND hmem0,
          isClosed_of_mem_extBranches hCl hmem0,
          isContractive_of_mem_extBranches hCo hmem0⟩
      have hWF1 := ih T0 T1 l s hmem0 hx hWF0
      exact hWF1.2.2
  | @unfold X B γ V hsub ih =>
    intro h_wf
    rcases h_wf with ⟨hND, hCl, hCo⟩
    have hWF_sub : (substSessionType B X (SessionType.tRec X B)).WellFormed := by
      refine ⟨?_, ?_, ?_⟩
      · cases hND with
        | tRec hND0 => exact NoDupl_subst hND0 (SessionType.NoDupl.tRec hND0)
      · unfold SessionType.IsClosed
        rw [fv_subst_aux B X (SessionType.tRec X B) hCl]
        simpa [SessionType.IsClosed, SessionType.fv] using hCl
      · cases hCo with
        | tRec hCo0 hG0 =>
          exact IsContractive_subst hCo0 (SessionType.Contractive.tRec hCo0 hG0) hCl
    exact ih hWF_sub

/-- If `mon_tr_yes T γ T'` (maximal, paper `def:monitor-state-st`) and `T` is
    well-formed, then `T'` is well-formed (via the existential version). -/
lemma mon_tr_yes_preserves_wf {T T' : SessionType} {γ : ext_tag}
    (h_enc : mon_tr_yes T γ T') (h_wf : SessionType.WellFormed T) : SessionType.WellFormed T' := by
  rcases h_enc with ⟨hE, _⟩
  exact mon_tr_yes_exist_preserves_wf hE h_wf

-- ================================================================
-- Encoder confluence and queue processing
-- (kept here so they can be used without an import cycle)
-- ================================================================

/-- Branch determinism under triple-key nodup: equal `(role, label, sort)` keys in one internal
   choice select the same target. -/
lemma unique_target_of_nodup_int {branches : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} {T1 T2 : SessionType}
    (h_nodup : List.Nodup (List.map (λ x => (x.1, x.2.1, x.2.2.1)) branches))
    (h1 : (p, lab, S, T1) ∈ branches) (h2 : (p, lab, S, T2) ∈ branches) : T1 = T2 := by
  induction branches generalizing T1 T2 with
  | nil => simp at h1
  | cons hd tl ih =>
    cases h_nodup
    rename_i h_tl_nodup h_head_notin
    simp at h1 h2
    rcases h1 with (⟨rfl, rfl, rfl, rfl⟩ | h1)
    · rcases h2 with (⟨rfl, rfl, rfl, rfl⟩ | h2)
      · rfl
      · exfalso
        have hkey_mem : (p, lab, S) ∈ List.map (λ x => (x.1, x.2.1, x.2.2.1)) tl := by
          apply List.mem_map.mpr
          exact ⟨(p, lab, S, T2), h2, rfl⟩
        apply h_head_notin (p, lab, S) hkey_mem
        rfl
    · rcases h2 with (⟨rfl, rfl, rfl, rfl⟩ | h2)
      · exfalso
        have hkey_mem : (p, lab, S) ∈ List.map (λ x => (x.1, x.2.1, x.2.2.1)) tl := by
          apply List.mem_map.mpr
          exact ⟨(p, lab, S, T1), h1, rfl⟩
        apply h_head_notin (p, lab, S) hkey_mem
        rfl
      · exact ih h_tl_nodup h1 h2

/-- Branch determinism under pair-key nodup: equal `(label, sort)` keys in one external choice
   select the same target. -/
lemma unique_target_of_nodup_ext {branches : List (Lab × DataSort × SessionType)}
    {lab : Lab} {S : DataSort} {T1 T2 : SessionType}
    (h_nodup : List.Nodup (List.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches))
    (h1 : (lab, S, T1) ∈ branches) (h2 : (lab, S, T2) ∈ branches) : T1 = T2 := by
  induction branches generalizing T1 T2 with
  | nil => simp at h1
  | cons hd tl ih =>
    cases h_nodup
    rename_i h_tl_nodup h_head_notin
    simp at h1 h2
    rcases h1 with (⟨rfl, rfl, rfl⟩ | h1)
    · rcases h2 with (⟨rfl, rfl, rfl⟩ | h2)
      · rfl
      · exfalso
        have hkey_mem : (lab, S) ∈ List.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)) tl := by
          apply List.mem_map.mpr
          exact ⟨(lab, S, T2), h2, rfl⟩
        apply h_head_notin (lab, S) hkey_mem
        rfl
    · rcases h2 with (⟨rfl, rfl, rfl⟩ | h2)
      · exfalso
        have hkey_mem : (lab, S) ∈ List.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)) tl := by
          apply List.mem_map.mpr
          exact ⟨(lab, S, T1), h1, rfl⟩
        apply h_head_notin (lab, S) hkey_mem
        rfl
      · exact ih h_tl_nodup h1 h2


-- ================================================================
-- `st_trans` input lifting to the encoder
-- ================================================================

-- `NoDupl.externalChoice` gives pairwise-distinct labels; `mon_tr_yes_base.extC` needs
-- pairwise-distinct (label, data-sort) pairs. Distinct labels imply distinct pairs.
/-- Label-nodup implies pair-nodup: distinct labels give distinct `(label, sort)` keys. -/
lemma nodup_of_nodup_labels {branches : List (Lab × DataSort × SessionType)}
    (h : List.Nodup (List.map (λ x : Lab × DataSort × SessionType => x.1) branches)) :
    List.Nodup (List.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches) := by
  induction branches with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨lab, S, T0⟩
    cases h
    rename_i h_tl_nodup h_head_notin
    constructor
    · intro hp hpm h_eq
      have hmem : hp.1 ∈ List.map (λ x : Lab × DataSort × SessionType => x.1) tl := by
        simpa using (List.mem_map.mpr ⟨hp, hpm, rfl⟩ :
          Prod.fst hp ∈ List.map Prod.fst
            (List.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)) tl))
      exact (h_head_notin hp.1 hmem) (by simpa using (congrArg Prod.fst h_eq))
    · exact ih h_tl_nodup

/-- Auxiliary version of `st_trans_inp_imp_mon_tr_yes_base` that is general in the transition
    label, so that the `st_trans` induction can run (the index `inp p lab S` is not a variable). -/
private lemma st_trans_inp_imp_mon_tr_yes_base_aux : ∀ {T T' : SessionType} {α : st_label},
    st_trans T α T' →
    (∀ (p : Role) (lab : Lab) (S : DataSort),
      α = st_label.inp p lab S → SessionType.WellFormed T →
        mon_tr_yes_base T (ext_tag.recv p lab S) T') := by
  intro T T' α hST
  induction hST
  case intC =>
    intro p' lab' S' hEq hwf
    cases hEq
  case extC =>
    rename_i branches p lab S T h_mem
    intro p' lab' S' hEq hwf
    cases hEq
    apply mon_tr_yes_base.extC
    · rcases hwf with ⟨h_nd, _, _⟩
      cases h_nd with
      | externalChoice h_nl h_ne h_br =>
          exact nodup_of_nodup_labels h_nl
    · exact h_mem
  case tRec =>
    rename_i X T T' α h' ih
    intro p' lab' S' hEq hwf
    apply mon_tr_yes_base.tRec
    exact ih p' lab' S' hEq (by
      rcases hwf with ⟨h_nd, h_cl, h_cv⟩
      cases h_nd with
      | tRec h_nd_body =>
          have h_nd_subst : SessionType.NoDupl (substSessionType T X (SessionType.tRec X T)) :=
            NoDupl_subst h_nd_body (SessionType.NoDupl.tRec h_nd_body)
          have h_cl_subst : (substSessionType T X (SessionType.tRec X T)).IsClosed := by
            unfold SessionType.IsClosed
            rw [fv_subst_aux T X (SessionType.tRec X T) h_cl]
            simpa [SessionType.IsClosed, SessionType.fv] using h_cl
          have h_cv_subst : (substSessionType T X (SessionType.tRec X T)).Contractive := by
            cases h_cv with
            | tRec h_cv_body h_cv_guard =>
                exact IsContractive_subst h_cv_body
                  (SessionType.Contractive.tRec h_cv_body h_cv_guard) h_cl
          exact ⟨h_nd_subst, h_cl_subst, h_cv_subst⟩)

/-- A `st_trans` input transition of a well-formed session type lifts to a base "yes"
    encoder transition with the same target (S-ExtC + S-Rec). -/
lemma st_trans_inp_imp_mon_tr_yes_base {T T' : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (hST : st_trans T (st_label.inp p lab S) T') (h_wf : SessionType.WellFormed T) :
    mon_tr_yes_base T (ext_tag.recv p lab S) T' := by
  exact st_trans_inp_imp_mon_tr_yes_base_aux hST p lab S rfl h_wf

/-- A `st_trans` input transition of a well-formed session type lifts to a "yes" encoder
    transition with the same target. -/
lemma st_trans_inp_imp_mon_tr_yes {T T' : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (hST : st_trans T (st_label.inp p lab S) T') (h_wf : SessionType.WellFormed T) :
    mon_tr_yes T (ext_tag.recv p lab S) T' := by
  have hb : mon_tr_yes_base T (ext_tag.recv p lab S) T' :=
    st_trans_inp_imp_mon_tr_yes_base hST h_wf
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- Monitor state for session type with queue: ⟦(T, σ)⟧ = ⟦T'⟧ iff
    ⟦T⟧ can accept all messages in σ (in order) and reaches ⟦T'⟧. -/
def monitor_fold_aux : Queue → SessionType → SessionType → Prop
  | .nil, T, T' => T' = T
  | .cons (QueueMessage.msg p lab S) rest, T, T' =>
    ∃ (T_mid : SessionType),
      mon_tr_yes T (ext_tag.recv p lab S) T_mid ∧
      monitor_fold_aux rest T_mid T'

/-- Monitor acceptance for a queued session: folding the queue into the session reaches the target
   type. -/
def monitor_fold (stq : SessionTypeWithQueue) (T' : SessionType) : Prop :=
  monitor_fold_aux stq.2 stq.1 T'

-- Queue absorbs preserve well-formedness (via `mon_tr_yes_preserves_wf`).
/-- Queue absorbs preserve well-formedness (via `mon_tr_yes_preserves_wf`). -/
lemma monitor_fold_aux_wf : ∀ (Q : Queue) (T M : SessionType),
    T.WellFormed → monitor_fold_aux Q T M → M.WellFormed := by
  intro Q
  induction Q with
  | nil =>
    intro T M hWF hEnc
    simp only [monitor_fold_aux] at hEnc
    subst hEnc
    exact hWF
  | cons msg rest ih =>
    intro T M hWF hEnc
    rcases msg with ⟨p, lab, S⟩
    simp only [monitor_fold_aux] at hEnc
    obtain ⟨T_mid, hYes, hRest⟩ := hEnc
    exact ih _ _ (mon_tr_yes_preserves_wf hYes hWF) hRest

/-- `Option` version of `encQueueVal`: returns `some M` iff the queue can be fully
    processed from the session type (reaching `M`), and `none` otherwise.
    This is defined compatibly with `encQueueVal` (they share the same witness). -/
noncomputable def monitor_fold_val_partial (stq : SessionTypeWithQueue) : Option SessionType := by
  classical
  if h : ∃ T', monitor_fold stq T' then
    exact some h.choose
  else
    exact none

-- ================================================================
-- Monitored session type
-- ================================================================

/-- Monitored session type (with input queue): ⟨T̈ | M⟩. -/
abbrev MonitoredSessionType : Type := SessionTypeWithQueue × SessionType

/-- A monitored session type ⟨T̈ | M⟩ is well-formed when both its session type and its monitor are closed and well-formed. -/
def MonitoredSessionType.WellFormed (mt : MonitoredSessionType) : Prop :=
  match mt with
  | ((T, _), M) => SessionType.WellFormed T ∧ SessionType.WellFormed M

/-- Labels for the monitored session type LTS.
    ::= γ✓  |  (p⊕lab(S))✗  |  (p&lab(S))✗  |  τ(p&lab(S)) -/
inductive mon_label : Type where
  | yes_send : Role → Lab → DataSort → mon_label
  | yes_recv : Role → Lab → DataSort → mon_label
  | no_out : Role → Lab → DataSort → mon_label
  | no_inp : Role → Lab → DataSort → mon_label
  | silent : Role → Lab → DataSort → mon_label
  deriving DecidableEq

/-- LTS for monitored session types.
    Rules: M-Good, M-BadOut, M-BadIn, M-Dequeue. -/
inductive mon_trans : MonitoredSessionType → mon_label → MonitoredSessionType → Prop where
  | good_send {stq stq' : SessionTypeWithQueue} {M M' : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hSQ : sq_trans stq (sq_action.send p lab S) stq')
      (hYes : mon_tr_yes M (ext_tag.send p lab S) M') :
    mon_trans (stq, M) (mon_label.yes_send p lab S) (stq', M')
  | good_recv {stq stq' : SessionTypeWithQueue} {M M' : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hSQ : sq_trans stq (sq_action.recv p lab S) stq')
      (hYes : mon_tr_yes M (ext_tag.recv p lab S) M') :
    mon_trans (stq, M) (mon_label.yes_recv p lab S) (stq', M')
  | badOut {stq stq' : SessionTypeWithQueue} {M M' : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hSQ : sq_trans stq (sq_action.send p lab S) stq')
      (hMon : mon_tr M (mon_verdict.no (ext_tag.send p lab S)) M') :
    mon_trans (stq, M) (mon_label.no_out p lab S) (stq', M')
  | badIn {stq : SessionTypeWithQueue} {M M' : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hMon : mon_tr M (mon_verdict.no (ext_tag.recv p lab S)) M') :
    mon_trans (stq, M) (mon_label.no_inp p lab S) (stq, M')
  | dequeue {stq stq' : SessionTypeWithQueue} {M : SessionType}
      {p : Role} {lab : Lab} {S : DataSort}
      (hSQ : sq_trans stq (sq_action.dequeue p lab S) stq') :
    mon_trans (stq, M) (mon_label.silent p lab S) (stq', M)

/-- If a monitored session type is well-formed and performs a transition,
    it remains well-formed. -/
lemma MonitoredSessionType.wellFormedPreserved (T : MonitoredSessionType) (α : mon_label) (T' : MonitoredSessionType)
  (hWF : T.WellFormed) (hTr : mon_trans T α T') : T'.WellFormed := by
  unfold MonitoredSessionType.WellFormed at hWF ⊢
  revert hWF
  induction hTr with
  | good_send hSQ hYes =>
      rename_i stq stq' M M' p lab S
      intro hWF
      exact ⟨SessionTypeWithQueue.wellFormedPreserved stq (sq_action.send p lab S) stq' hWF.1 hSQ,
        mon_tr_yes_preserves_wf hYes hWF.2⟩
  | good_recv hSQ hYes =>
      rename_i stq stq' M M' p lab S
      intro hWF
      exact ⟨SessionTypeWithQueue.wellFormedPreserved stq (sq_action.recv p lab S) stq' hWF.1 hSQ,
        mon_tr_yes_preserves_wf hYes hWF.2⟩
  | badOut hSQ hMon =>
      rename_i stq stq' M M' p lab S
      intro hWF
      cases hMon with
      | bad h_no =>
          exact ⟨SessionTypeWithQueue.wellFormedPreserved stq (sq_action.send p lab S) stq' hWF.1 hSQ,
            hWF.2⟩
  | badIn hMon =>
      rename_i stq M M' p lab S
      intro hWF
      cases hMon with
      | bad h_no =>
          exact ⟨hWF.1, hWF.2⟩
  | dequeue hSQ =>
      rename_i stq stq' M p lab S
      intro hWF
      exact ⟨SessionTypeWithQueue.wellFormedPreserved stq (sq_action.dequeue p lab S) stq' hWF.1 hSQ,
        hWF.2⟩

-- ================================================================
-- Monitored network
-- ================================================================

/-- Monitored network as a finite mapping from roles to monitored session types.
    N̂ ::= { p_i ↦ ⟨T̈_i | M_i⟩ }_{i∈I}   (flat-list representation) -/
abbrev MonitoredNetwork : Type := List (Role × MonitoredSessionType)

/-- Replace role r's monitored session type in MN (removes old entry for r). -/
def MonitoredNetwork.replace (MN : MonitoredNetwork) (r : Role) (mt : MonitoredSessionType) : MonitoredNetwork :=
  (r, mt) :: MN.filter (λ (x : Role × MonitoredSessionType) => x.1 != r)

/-- A monitored network is well-formed when there are no duplicate roles and each
    monitored session type is well-formed. -/
def MonitoredNetwork.WellFormed (MN : MonitoredNetwork) : Prop :=
  List.Nodup (List.map (λ (x : Role × MonitoredSessionType) => x.1) MN) ∧
  ∀ (x : Role × MonitoredSessionType), x ∈ MN → MonitoredSessionType.WellFormed x.2

/-- Labels for the monitored network LTS.
    η ::= p:γ✓  |  p:(q⊕lab(S))✗  |  p:(q&lab(S))✗
         |  τ(p:q&lab(S))  |  τ(p→q:lab(S)) -/
inductive mon_net_label : Type where
  | io_yes_send : Role → Role → Lab → DataSort → mon_net_label
  | io_yes_recv : Role → Role → Lab → DataSort → mon_net_label
  | io_no_out : Role → Role → Lab → DataSort → mon_net_label
  | io_no_inp : Role → Role → Lab → DataSort → mon_net_label
  | τ_dequeue : Role → Role → Lab → DataSort → mon_net_label
  | τ_comm : Role → Role → Lab → DataSort → mon_net_label
  deriving DecidableEq

/-- Embed a monitored-session-type label into a monitored-network label
    by prefixing the acting role. -/
def mon_net_label.ofmon_label (r : Role) : mon_label → mon_net_label
  | mon_label.yes_send p lab S => mon_net_label.io_yes_send r p lab S
  | mon_label.yes_recv p lab S => mon_net_label.io_yes_recv r p lab S
  | mon_label.no_out p lab S => mon_net_label.io_no_out r p lab S
  | mon_label.no_inp p lab S => mon_net_label.io_no_inp r p lab S
  | mon_label.silent p lab S => mon_net_label.τ_dequeue r p lab S

/-- LTS for monitored networks (flat-list representation).
    Rules: MNet-γ-Good, MNet-γ-Bad, MNet-Deq, MNet-Comm.
    The non-comm rules lift the monitored-session-type rules `mon_trans`
    to a role in the network; the par-left/par-right rules are eliminated. -/
inductive mon_net_trans : MonitoredNetwork → mon_net_label → MonitoredNetwork → Prop where
  | lift {r : Role} {mt mt' : MonitoredSessionType} {ℓ : mon_label}
      (h : mon_trans mt ℓ mt')
      (hmem : (r, mt) ∈ MN) :
    mon_net_trans MN (mon_net_label.ofmon_label r ℓ) (MonitoredNetwork.replace MN r mt')
  | comm {p q : Role} {lab : Lab} {S : DataSort}
      {mtp mtp' : MonitoredSessionType} {mtq mtq' : MonitoredSessionType}
      (h_send : mon_trans mtp (mon_label.yes_send q lab S) mtp')
      (h_recv : mon_trans mtq (mon_label.yes_recv p lab S) mtq')
      (hmem_p : (p, mtp) ∈ MN)
      (hmem_q : (q, mtq) ∈ MN) :
    mon_net_trans MN (mon_net_label.τ_comm p q lab S)
      ((MN.replace p mtp').replace q mtq')

/-- The monitored-network LTS: states are monitored networks, steps are `mon_net_trans`. -/
def mnetLTS : LTS MonitoredNetwork mon_net_label := LTS.mk mon_net_trans

-- ================================================================
-- Consistent instrumentation
-- ================================================================

/-- Given a network N = { p_i ↦ T̈_i }_{i∈I}, its consistent monitor instrumentation
    mon(N) = { p_i ↦ ⟨T̈_i | ⟦T̈_i⟧⟩ }, as a partial function.
    `consistentInstrumentation N` is `some` iff every session type with queue in `N`
    can be fully processed by the encoder, i.e. `monitor_fold_val_partial stq` returns
    `some st` for every `stq` occurring in `N`; it is `none` otherwise. -/
noncomputable def consistentInstrumentation : Network → Option MonitoredNetwork
  | [] => some []
  | (r, stq) :: rest =>
    match monitor_fold_val_partial stq, consistentInstrumentation rest with
    | some M, some MN => some ((r, (stq, M)) :: MN)
    | _, _ => none

-- ================================================================
-- Internal bisimulation
-- ================================================================

/-- An internal bisimulation is a relation R such that whenever (s, t) ∈ R,
    internal (τ) transitions can be matched with the same label. -/
def IsInternalBisimulation {S₁ S₂ L₁ L₂ : Type}
    (isLbl₁ : L₁ → Prop) (isLbl₂ : L₂ → Prop)
    (lblMap : L₁ → L₂)
    (lts₁ : LTS S₁ L₁) (lts₂ : LTS S₂ L₂)
    (r : S₁ → S₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ (μ₁ : L₁), isLbl₁ μ₁ → (
    (∀ s₁', lts₁.Tr s₁ μ₁ s₁' → ∃ s₂' μ₂, isLbl₂ μ₂ ∧ lblMap μ₁ = μ₂ ∧ lts₂.Tr s₂ μ₂ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂' μ₂, isLbl₂ μ₂ → lts₂.Tr s₂ μ₂ s₂' → ∃ s₁' μ₁', isLbl₁ μ₁' ∧ lblMap μ₁' = μ₂ ∧ lts₁.Tr s₁ μ₁' s₁' ∧ r s₁' s₂')
  )

/-- Internal τ-labels for monitored networks are τ_dequeue and τ_comm. -/
def is_internal_mon_net_label (η : mon_net_label) : Prop :=
  match η with
  | mon_net_label.τ_dequeue _ _ _ _ => True
  | mon_net_label.τ_comm _ _ _ _ => True
  | _ => False

/-- Map a net_label τ label to the corresponding mon_net_label τ label. -/
def netLabelToMonNetLabel (δ : net_label) : mon_net_label :=
  match δ with
  | net_label.τ_dequeue r p lab S => mon_net_label.τ_dequeue r p lab S
  | net_label.τ_comm p q lab S => mon_net_label.τ_comm p q lab S
  | net_label.io_send r p lab S => mon_net_label.io_yes_send r p lab S
  | net_label.io_recv r p lab S => mon_net_label.io_yes_recv r p lab S

/-- Two (monitored) networks are internally bisimilar if there exists an
    internal bisimulation relating them. -/
def InternallyBisimilar (N : Network) (MN : MonitoredNetwork) : Prop :=
  ∃ (r : Network → MonitoredNetwork → Prop), r N MN ∧
    IsInternalBisimulation is_internal_net_label is_internal_mon_net_label netLabelToMonNetLabel
      netLTS mnetLTS r

