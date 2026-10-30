import Nest.MonitorCo
import Nest.MonitorLTS
import Nest.Drainability
import Nest.SessionUtils
import Nest.SessionLTS

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-! # MonitorCoBase: shared session-type infrastructure for monitors.

Acceptability (`Ex`), `session_induction`, `PruneStep`, environments and
substitution, `traversalNodes` closure, and branch filtering
(`KRint`/`KRext`, int/ext keys).

Ports here are credited to Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and
Kristýna Petrlíková <auburn@kam.mff.cuni.cz>; see per-declaration doc-comments.
-/

/-- Acceptability: some finite-fragment yes-target exists (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def Ex (T : SessionType) (g : ext_tag) : Prop := ∃ V, mon_tr_yes_exist T g V

/-- Single kept branch suffices for internal acceptability (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem Ex_int_single {bs : List (Role × Lab × DataSort × SessionType)}
    {q r : Role} {lab l : Lab} {S s : DataSort} {U : SessionType}
    (wf : (SessionType.internalChoice bs).WellFormed)
    (off : ∀ p l s T, (p, l, s, T) ∈ bs → q ≠ p)
    (member : (r, l, s, U) ∈ bs) (accept : Ex U (.recv q lab S)) :
    Ex (.internalChoice bs) (.recv q lab S) := by
  obtain ⟨W, accept⟩ := accept
  refine ⟨.internalChoice [(r, l, s, W)],
    .pfxInt ⟨List.ne_nil_of_mem member, by simp⟩ off rfl ?_ (by simp) ?_⟩
  · intro T V p a b source kept
    have equal := List.mem_singleton.mp kept
    cases equal
    have eq := unique_target_of_nodup_int
      wf.1.triple_nodup_of_internalChoice member source
    subst T
    exact accept
  · intro p a b V kept
    have equal := List.mem_singleton.mp kept
    cases equal
    exact ⟨U, member⟩

/-- Single kept branch suffices for external acceptability (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem Ex_ext_single {p q : Role} {bs : List (Lab × DataSort × SessionType)}
    {lab l : Lab} {S s : DataSort} {U : SessionType}
    (wf : (SessionType.externalChoice p bs).WellFormed) (off : q ≠ p)
    (member : (l, s, U) ∈ bs) (accept : Ex U (.recv q lab S)) :
    Ex (.externalChoice p bs) (.recv q lab S) := by
  obtain ⟨W, accept⟩ := accept
  have unique : (bs.map fun b => (b.1, b.2.1)).Nodup := by
    cases wf.1 with | externalChoice unique _ _ => exact nodup_of_nodup_labels unique
  refine ⟨.externalChoice p [(l, s, W)],
    .pfxExt ⟨List.ne_nil_of_mem member, by simp⟩ off rfl ?_ (by simp) ?_⟩
  · intro T V a b source kept
    have equal := List.mem_singleton.mp kept
    cases equal
    have eq := unique_target_of_nodup_ext unique member source
    subst T
    exact accept
  · intro a b V kept
    have equal := List.mem_singleton.mp kept
    cases equal
    exact ⟨U, member⟩

/-- Nested-type induction principle via explicit `.rec` (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem session_induction {P : SessionType → Prop}
    (intC : ∀ bs, (∀ b ∈ bs, P b.2.2.2) → P (.internalChoice bs))
    (extC : ∀ p bs, (∀ b ∈ bs, P b.2.2) → P (.externalChoice p bs))
    (done : P .tEnd) (rec : ∀ X B, P B → P (.tRec X B))
    (var : ∀ X, P (.tVar X)) : ∀ T, P T :=
  @SessionType.rec (fun T => P T) (fun bs => ∀ b ∈ bs, P b.2.2.2)
    (fun bs => ∀ b ∈ bs, P b.2.2) (fun b => P b.2.2.2) (fun b => P b.2.2)
    (fun b => P b.2) intC extC done rec var
    (by simp) (by intros b bs hb hbs x hx; rcases List.mem_cons.mp hx with rfl | hx; exact hb; exact hbs x hx)
    (by simp) (by intros b bs hb hbs x hx; rcases List.mem_cons.mp hx with rfl | hx; exact hb; exact hbs x hx)
    (fun _ _ ih => ih) (fun _ _ ih => ih) (fun _ _ ih => ih)

/-- Pruning reachability (port): branch descent into choice targets,
and recursion unfolding. `tEnd`/`tVar` have no steps.
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
inductive PruneStep : SessionType → SessionType → Prop where
  | intC {branches : List (Role × Lab × DataSort × SessionType)}
      {x : Role × Lab × DataSort × SessionType} (hmem : x ∈ branches) :
      PruneStep (SessionType.internalChoice branches) x.2.2.2
  | extC {p : Role} {branches : List (Lab × DataSort × SessionType)}
      {x : Lab × DataSort × SessionType} (hmem : x ∈ branches) :
      PruneStep (SessionType.externalChoice p branches) x.2.2
  | trec {X : String} {B : SessionType} :
      PruneStep (SessionType.tRec X B)
        (substSessionType B X (SessionType.tRec X B))

/-- Substitution environments (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
abbrev env := List (String × SessionType)

/-- Environment lookup (port; see `env` for credit). -/
abbrev elookup (ρ : env) (x : String) := ρ.lookup x

/-- Environment removal (port; see `env` for credit). -/
def eremove (x : String) (ρ : env) : env := ρ.filter fun p => p.1 != x

/-- Closed environments (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def env_closed (ρ : env) : Prop := ∀ x v, (x, v) ∈ ρ → v.IsClosed

/-- Simultaneous substitution (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def ssubst (ρ : env) : SessionType → SessionType
  | .tVar X => (elookup ρ X).getD (.tVar X)
  | .tEnd => .tEnd
  | .internalChoice bs => .internalChoice (bs.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ b.2.2.2))
  | .externalChoice p bs => .externalChoice p (bs.map fun b => (b.1, b.2.1, ssubst ρ b.2.2))
  | .tRec X B => .tRec X (ssubst (eremove X ρ) B)
termination_by T => sizeOf T
decreasing_by
  · exact sizeOf_SessionType_lt_sizeOf_internalChoice ‹_›
  · exact sizeOf_SessionType_lt_sizeOf_externalChoice ‹_›
  · simp_wf

/-- Free variables distribute over internal choice (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
@[simp] theorem fv_int (bs : List (Role × Lab × DataSort × SessionType)) :
    SessionType.fv (.internalChoice bs) = bs.flatMap (fun b => b.2.2.2.fv) := by
  change SessionType.fv.goInt bs = _
  induction bs with
  | nil => rfl
  | cons b bs ih => obtain ⟨p, l, s, T⟩ := b; simpa [SessionType.fv.goInt] using congrArg (T.fv ++ ·) ih

/-- Free variables distribute over external choice (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
@[simp] theorem fv_ext (p : Role) (bs : List (Lab × DataSort × SessionType)) :
    SessionType.fv (.externalChoice p bs) = bs.flatMap (fun b => b.2.2.fv) := by
  change SessionType.fv.goExt bs = _
  induction bs with
  | nil => rfl
  | cons b bs ih => obtain ⟨l, s, T⟩ := b; simpa [SessionType.fv.goExt] using congrArg (T.fv ++ ·) ih

/-- Lookup success is membership (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem elookup_In {ρ : env} {x : String} {v : SessionType}
    (found : elookup ρ x = some v) : (x, v) ∈ ρ := by
  obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

/-- Lookup in a closed environment yields closed types (port; see `elookup_In` for credit). -/
theorem elookup_closed {ρ : env} {x : String} {v : SessionType}
    (closed : env_closed ρ) (found : elookup ρ x = some v) : v.IsClosed := closed x v (elookup_In found)

/-- Removal hides the variable (port; see `elookup_In` for credit). -/
@[simp] theorem elookup_eremove_same (ρ : env) (x : String) : elookup (eremove x ρ) x = none := by
  apply List.lookup_eq_none_iff.mpr
  intro p member
  simp only [eremove, List.mem_filter] at member
  simpa [beq_iff_eq, ne_comm] using member.2

/-- Removal preserves other lookups (port; see `elookup_In` for credit). -/
theorem elookup_eremove_other (ρ : env) {x y : String} (apart : x ≠ y) :
    elookup (eremove x ρ) y = elookup ρ y := by
  induction ρ with
  | nil => rfl
  | cons entry ρ ih =>
      obtain ⟨z, v⟩ := entry
      by_cases zx : z = x <;> by_cases zy : z = y <;>
        simp_all [eremove, elookup, List.lookup_cons, Ne.symm apart]
      all_goals simp [show (y == x) = false from beq_eq_false_iff_ne.mpr (Ne.symm apart)]

/-- Removal preserves closedness (port; see `elookup_In` for credit). -/
theorem env_closed_eremove {ρ : env} (x : String) (closed : env_closed ρ) : env_closed (eremove x ρ) := by
  intro y v member
  exact closed y v (List.mem_filter.mp member).1

/-- Extension by a closed type preserves closedness (port; see `elookup_In` for credit). -/
theorem env_closed_cons {ρ : env} {x : String} {v : SessionType}
    (closed : env_closed ρ) (value : v.IsClosed) : env_closed ((x, v) :: ρ) := by
  intro y w member
  rcases List.mem_cons.mp member with same | member
  · cases same; exact value
  · exact closed y w member

/-- Simultaneous substitution agrees on equal environments (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem ssubst_ext (T : SessionType) (ρ₁ ρ₂ : env)
    (same : ∀ x ∈ T.fv, elookup ρ₁ x = elookup ρ₂ x) : ssubst ρ₁ T = ssubst ρ₂ T := by
  induction T using session_induction generalizing ρ₁ ρ₂ with
  | intC bs ih =>
      simp only [ssubst]
      congr 1
      apply List.map_congr_left
      intro b member
      have hsub : ssubst ρ₁ b.2.2.2 = ssubst ρ₂ b.2.2.2 := ih b member ρ₁ ρ₂ (by
        intro x hx
        exact same x (by simp only [fv_int, List.mem_flatMap]; exact ⟨b, member, hx⟩))
      rw [hsub]
  | extC p bs ih =>
      simp only [ssubst]
      congr 1
      apply List.map_congr_left
      intro b member
      have hsub : ssubst ρ₁ b.2.2 = ssubst ρ₂ b.2.2 := ih b member ρ₁ ρ₂ (by
        intro x hx
        exact same x (by simp only [fv_ext, List.mem_flatMap]; exact ⟨b, member, hx⟩))
      rw [hsub]
  | done => simp only [ssubst]
  | rec X B ih =>
      simp only [ssubst]
      congr 1
      apply ih
      intro x hx
      by_cases heq : x = X
      · subst heq
        rw [elookup_eremove_same, elookup_eremove_same]
      · have hmem : x ∈ (SessionType.tRec X B).fv :=
          List.mem_filter.mpr ⟨hx, bne_iff_ne.mpr heq⟩
        have e1 := same x hmem
        have e2 : elookup (eremove X ρ₁) x = elookup ρ₁ x :=
          elookup_eremove_other ρ₁ (Ne.symm heq)
        have e3 : elookup (eremove X ρ₂) x = elookup ρ₂ x :=
          elookup_eremove_other ρ₂ (Ne.symm heq)
        rw [e2, e3]; exact e1
  | var X =>
      simp only [ssubst]
      rw [same X (by simp [SessionType.fv])]

/-- Empty substitution is the identity (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem ssubst_nil (T : SessionType) : ssubst [] T = T := by
  induction T using session_induction with
  | intC bs ih =>
      simp only [ssubst]
      congr 1
      conv_rhs => rw [← List.map_id bs]
      apply List.map_congr_left
      intro b member
      obtain ⟨p, l, s, T⟩ := b
      simp [ih _ member]
  | extC p bs ih =>
      simp only [ssubst]
      congr 1
      conv_rhs => rw [← List.map_id bs]
      apply List.map_congr_left
      intro b member
      obtain ⟨l, s, T⟩ := b
      simp [ih _ member]
  | done => simp [ssubst]
  | rec X B ih => simpa [ssubst, eremove] using congrArg (SessionType.tRec X) ih
  | var X => simp [ssubst, elookup]

/-- Substitution through simultaneous substitution (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem subst_ssubst_fresh (B : SessionType) (ρ : env) (X : String) (U : SessionType)
    (closed : env_closed ρ) (_cu : U.IsClosed) (fresh : elookup ρ X = none) :
    substSessionType (ssubst ρ B) X U = ssubst ((X, U) :: ρ) B := by
  induction B using session_induction generalizing ρ with
  | intC bs ih =>
      simp only [ssubst, substSessionType, go_int_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro b member
      obtain ⟨p, l, s, T⟩ := b
      simp only [Function.comp_apply]
      congr 3
      exact ih _ member ρ closed fresh
  | extC p bs ih =>
      simp only [ssubst, substSessionType, go_ext_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro b member
      obtain ⟨l, s, T⟩ := b
      simp only [Function.comp_apply]
      congr 2
      exact ih _ member ρ closed fresh
  | done => simp [ssubst, substSessionType]
  | rec Y C ih =>
      by_cases eq : X = Y
      · subst Y
        simp [ssubst, substSessionType, eremove]
      · simp only [ssubst, substSessionType, ite_eq_right eq]
        have remove : eremove Y ((X, U) :: ρ) = (X, U) :: eremove Y ρ := by simp [eremove, eq]
        rw [remove]
        congr 1
        exact ih (eremove Y ρ) (env_closed_eremove Y closed)
          (by rw [elookup_eremove_other ρ (Ne.symm eq)]; exact fresh)
  | var Y =>
      by_cases eq : X = Y
      · subst Y
        simp [ssubst, elookup, fresh, substSessionType]
      · have lookup : elookup ((X, U) :: ρ) Y = elookup ρ Y := by
          simp [elookup, List.lookup_cons, show (Y == X) = false from beq_eq_false_iff_ne.mpr (Ne.symm eq)]
        rw [ssubst, ssubst, lookup]
        cases found : elookup ρ Y with
        | none => simp [substSessionType, eq]
        | some V =>
            simp only [Option.getD_some]
            have hcl : V.fv = [] := elookup_closed closed found
            exact subst_noop V X U (by simp [hcl])

/-- Unfold substitution as environment extension (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem subst_ssubst_cons (B : SessionType) (ρ : env) (X : String) (U : SessionType)
    (closed : env_closed ρ) (cu : U.IsClosed) :
    substSessionType (ssubst (eremove X ρ) B) X U = ssubst ((X, U) :: ρ) B := by
  rw [subst_ssubst_fresh B (eremove X ρ) X U (env_closed_eremove X closed) cu (elookup_eremove_same ρ X)]
  apply ssubst_ext
  intro y _
  by_cases eq : X = y
  · subst y; simp [elookup]
  · simp only [elookup, List.lookup_cons, show (y == X) = false from beq_eq_false_iff_ne.mpr (Ne.symm eq)]
    exact elookup_eremove_other ρ eq

/-- Free variables of a simultaneous substitution (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem fv_ssubst (T : SessionType) (ρ : env) (y : String)
    (closed : env_closed ρ) (member : y ∈ (ssubst ρ T).fv) : y ∈ T.fv ∧ elookup ρ y = none := by
  induction T using session_induction generalizing ρ y with
  | intC bs ih =>
      simp only [ssubst, fv_int, List.flatMap_map, List.mem_flatMap] at member
      obtain ⟨b, hb, hy⟩ := member
      obtain ⟨hy, absent⟩ := ih b hb ρ y closed hy
      exact ⟨by simp only [fv_int, List.mem_flatMap]; exact ⟨b, hb, hy⟩, absent⟩
  | extC p bs ih =>
      simp only [ssubst, fv_ext, List.flatMap_map, List.mem_flatMap] at member
      obtain ⟨b, hb, hy⟩ := member
      obtain ⟨hy, absent⟩ := ih b hb ρ y closed hy
      exact ⟨by simp only [fv_ext, List.mem_flatMap]; exact ⟨b, hb, hy⟩, absent⟩
  | done => simp [ssubst, SessionType.fv] at member
  | rec X B ih =>
      simp only [ssubst, SessionType.fv, List.mem_filter, bne_iff_ne] at member
      obtain ⟨hy, apart⟩ := member
      obtain ⟨hy, absent⟩ := ih _ _ (env_closed_eremove X closed) hy
      rw [elookup_eremove_other ρ (Ne.symm apart)] at absent
      exact ⟨by simp [SessionType.fv, hy, apart], absent⟩
  | var X =>
      cases found : elookup ρ X with
      | none =>
          simp [ssubst, found, SessionType.fv] at member
          subst y
          exact ⟨by simp [SessionType.fv], found⟩
      | some V =>
          have empty := elookup_closed closed found
          simp [ssubst, found, SessionType.IsClosed] at member empty
          simp [empty] at member

/-- Simultaneous substitution into a covered type is closed (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem ssubst_closed (T : SessionType) (ρ : env) (closed : env_closed ρ)
    (covered : ∀ x ∈ T.fv, elookup ρ x ≠ none) : (ssubst ρ T).IsClosed := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro y member
  obtain ⟨hy, absent⟩ := fv_ssubst T ρ y closed member
  exact covered y hy absent

/-- All `PruneStep`-reachable nodes, listed (port).
Terminates: under `tRec` we recurse into the (smaller) body with an
extended environment instead of unfolding.
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def traversalNodes (ρ : env) (T : SessionType) : List SessionType :=
  ssubst ρ T :: match T with
  | .tEnd | .tVar _ => []
  | .internalChoice bs => bs.flatMap fun b => traversalNodes ρ b.2.2.2
  | .externalChoice _ bs => bs.flatMap fun b => traversalNodes ρ b.2.2
  | .tRec X B => traversalNodes ((X, ssubst ρ T) :: ρ) B
termination_by sizeOf T
decreasing_by
  · exact sizeOf_SessionType_lt_sizeOf_internalChoice ‹_›
  · exact sizeOf_SessionType_lt_sizeOf_externalChoice ‹_›
  · simp_wf

/-- The substituted root is listed (port; see `traversalNodes` for credit). -/
theorem traversalNodes_root (T : SessionType) (ρ : env) :
    ssubst ρ T ∈ traversalNodes ρ T := by
  rw [traversalNodes.eq_def]
  exact List.mem_cons_self

/-- Unfold target lands back in the node list (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
private theorem rec_traversal_target (B : SessionType) (X : String) (ρ : env)
    (closed : env_closed ρ) (closedRec : (ssubst ρ (.tRec X B)).IsClosed)
    {V : SessionType} (step : PruneStep (ssubst ρ (.tRec X B)) V) :
    V = ssubst ((X, ssubst ρ (.tRec X B)) :: ρ) B := by
  simp only [ssubst] at step
  cases step
  simpa only [ssubst] using subst_ssubst_cons B ρ X _ closed closedRec

/-- Node lists are closed under prune steps up to environment back-edges (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem traversalNodes_step (T : SessionType) (ρ : env)
    (closed : env_closed ρ) (covered : ∀ x ∈ T.fv, elookup ρ x ≠ none)
    {U V : SessionType} (member : U ∈ traversalNodes ρ T)
    (step : PruneStep U V) :
    V ∈ traversalNodes ρ T ∨ ∃ x, (x, U) ∈ ρ := by
  induction T using session_induction generalizing ρ U V with
  | done =>
      simp only [traversalNodes, ssubst, List.mem_cons, List.not_mem_nil, or_false] at member
      subst U
      cases step
  | var X =>
      simp only [traversalNodes, List.mem_cons, List.not_mem_nil, or_false] at member
      subst U
      cases found : elookup ρ X with
      | none => simp only [ssubst, found, Option.getD_none] at step; cases step
      | some R =>
          apply Or.inr
          refine ⟨X, ?_⟩
          simpa [ssubst, found] using elookup_In found
  | intC bs ih =>
      simp only [traversalNodes, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [ssubst] at step
        cases step with
        | intC branch =>
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp branch
            apply Or.inl
            rw [traversalNodes]
            exact List.mem_cons_of_mem _
              (List.mem_flatMap.mpr ⟨b, hb, traversalNodes_root _ _⟩)
      · obtain ⟨b, hb, member⟩ := List.mem_flatMap.mp member
        have covered' : ∀ x ∈ b.2.2.2.fv, elookup ρ x ≠ none := by
          intro x hx
          exact covered x (by rw [fv_int]; exact List.mem_flatMap.mpr ⟨b, hb, hx⟩)
        rcases ih b hb ρ closed covered' member step with next | ancestor
        · apply Or.inl
          rw [traversalNodes]
          exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b, hb, next⟩)
        · exact Or.inr ancestor
  | extC p bs ih =>
      simp only [traversalNodes, List.mem_cons] at member
      rcases member with rfl | member
      · simp only [ssubst] at step
        cases step with
        | extC branch =>
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp branch
            apply Or.inl
            rw [traversalNodes]
            exact List.mem_cons_of_mem _
              (List.mem_flatMap.mpr ⟨b, hb, traversalNodes_root _ _⟩)
      · obtain ⟨b, hb, member⟩ := List.mem_flatMap.mp member
        have covered' : ∀ x ∈ b.2.2.fv, elookup ρ x ≠ none := by
          intro x hx
          exact covered x (by rw [fv_ext]; exact List.mem_flatMap.mpr ⟨b, hb, hx⟩)
        rcases ih b hb ρ closed covered' member step with next | ancestor
        · apply Or.inl
          rw [traversalNodes]
          exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨b, hb, next⟩)
        · exact Or.inr ancestor
  | rec X B ih =>
      let R := ssubst ρ (.tRec X B)
      have closedR : R.IsClosed := ssubst_closed _ _ closed covered
      have bodyRoot : ssubst ((X, R) :: ρ) B ∈ traversalNodes ρ (.tRec X B) := by
        rw [traversalNodes]
        exact List.mem_cons_of_mem _ (traversalNodes_root _ _)
      have rootStep {V : SessionType} (step : PruneStep R V) :
          V ∈ traversalNodes ρ (.tRec X B) := by
        rw [rec_traversal_target B X ρ closed closedR step]
        exact bodyRoot
      simp only [traversalNodes, List.mem_cons] at member
      rcases member with rfl | member
      · exact Or.inl (rootStep step)
      · have covered' : ∀ x ∈ B.fv, elookup ((X, R) :: ρ) x ≠ none := by
          intro x hx
          by_cases same : x = X
          · subst x; simp [elookup]
          · have lookup : elookup ((X, R) :: ρ) x = elookup ρ x := by
              simp only [elookup, List.lookup_cons, beq_eq_false_iff_ne.mpr same]
            rw [lookup]
            exact covered x (by simp [SessionType.fv, hx, same])
        rcases ih ((X, R) :: ρ) (env_closed_cons closed closedR) covered' member step with
          next | ⟨x, ancestor⟩
        · apply Or.inl
          rw [traversalNodes]
          exact List.mem_cons_of_mem _ next
        · rcases List.mem_cons.mp ancestor with same | old
          · have sameU : U = R := congrArg Prod.snd same
            exact Or.inl (rootStep (sameU ▸ step))
          · exact Or.inr ⟨x, old⟩

/-- Internal branch key (role, label) (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def int_key (b : Role × Lab × DataSort × SessionType) := (b.1, b.2.1)

/-- Internal branch key (role, label, sort) (port; see `int_key` for credit). -/
def int_key3 (b : Role × Lab × DataSort × SessionType) := (b.1, b.2.1, b.2.2.1)

/-- External branch key (label) (port; see `int_key` for credit). -/
def ext_key (b : Lab × DataSort × SessionType) := b.1

/-- External branch key (label, sort) (port; see `int_key` for credit). -/
def ext_key2 (b : Lab × DataSort × SessionType) := (b.1, b.2.1)

/-- Keep/drop retention for internal branches (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
inductive KRint (E : SessionType → Prop) (P : SessionType → SessionType → Prop) :
    List (Role × Lab × DataSort × SessionType) →
    List (Role × Lab × DataSort × SessionType) → Prop where
  | nil : KRint E P [] []
  | keep {p l s T U bs kept} (eligible : E T) (next : P T U) (rest : KRint E P bs kept) :
      KRint E P ((p, l, s, T) :: bs) ((p, l, s, U) :: kept)
  | drop {p l s T bs kept} (ineligible : ¬ E T) (rest : KRint E P bs kept) :
      KRint E P ((p, l, s, T) :: bs) kept

/-- Keep/drop retention for external branches (port; see `KRint` for credit). -/
inductive KRext (E : SessionType → Prop) (P : SessionType → SessionType → Prop) :
    List (Lab × DataSort × SessionType) → List (Lab × DataSort × SessionType) → Prop where
  | nil : KRext E P [] []
  | keep {l s T U bs kept} (eligible : E T) (next : P T U) (rest : KRext E P bs kept) :
      KRext E P ((l, s, T) :: bs) ((l, s, U) :: kept)
  | drop {l s T bs kept} (ineligible : ¬ E T) (rest : KRext E P bs kept) :
      KRext E P ((l, s, T) :: bs) kept

/-- Retained triple keys form a sublist (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem KRint_sublist3 {E P bs kept} (h : KRint E P bs kept) :
    (kept.map int_key3).Sublist (bs.map int_key3) := by
  induction h with
  | nil => exact .slnil
  | keep he hp h ih => exact .cons_cons _ ih
  | drop he h ih => exact .cons _ ih

/-- Retained pair keys form a sublist (port; see `KRint_sublist3` for credit). -/
theorem KRint_sublist2 {E P bs kept} (h : KRint E P bs kept) :
    (kept.map int_key).Sublist (bs.map int_key) := by
  induction h with
  | nil => exact .slnil
  | keep he hp h ih => exact .cons_cons _ ih
  | drop he h ih => exact .cons _ ih

/-- Retained ext pair keys form a sublist (port; see `KRint_sublist3` for credit). -/
theorem KRext_sublist2 {E P bs kept} (h : KRext E P bs kept) :
    (kept.map ext_key2).Sublist (bs.map ext_key2) := by
  induction h with
  | nil => exact .slnil
  | keep he hp h ih => exact .cons_cons _ ih
  | drop he h ih => exact .cons _ ih

/-- Retained ext singleton keys form a sublist (port; see `KRint_sublist3` for credit). -/
theorem KRext_sublist1 {E P bs kept} (h : KRext E P bs kept) :
    (kept.map ext_key).Sublist (bs.map ext_key) := by
  induction h with
  | nil => exact .slnil
  | keep he hp h ih => exact .cons_cons _ ih
  | drop he h ih => exact .cons _ ih

/-- Kept entries come from eligible sources (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem KRint_kept_mem {E P bs kept r l s T1} (h : KRint E P bs kept)
    (hin : (r, l, s, T1) ∈ kept) : ∃ T0, (r, l, s, T0) ∈ bs ∧ E T0 ∧ P T0 T1 := by
  induction h with
  | nil => simp at hin
  | keep he hp h ih =>
      rcases List.mem_cons.mp hin with eq | hin
      · cases eq; exact ⟨_, List.mem_cons_self, he, hp⟩
      · obtain ⟨T0, hm, he, hp⟩ := ih hin
        exact ⟨T0, List.mem_cons_of_mem _ hm, he, hp⟩
  | drop he h ih =>
      obtain ⟨T0, hm, he, hp⟩ := ih hin
      exact ⟨T0, List.mem_cons_of_mem _ hm, he, hp⟩

/-- Kept ext entries come from eligible sources (port; see `KRint_kept_mem` for credit). -/
theorem KRext_kept_mem {E P bs kept l s T1} (h : KRext E P bs kept)
    (hin : (l, s, T1) ∈ kept) : ∃ T0, (l, s, T0) ∈ bs ∧ E T0 ∧ P T0 T1 := by
  induction h with
  | nil => simp at hin
  | keep he hp h ih =>
      rcases List.mem_cons.mp hin with eq | hin
      · cases eq; exact ⟨_, List.mem_cons_self, he, hp⟩
      · obtain ⟨T0, hm, he, hp⟩ := ih hin
        exact ⟨T0, List.mem_cons_of_mem _ hm, he, hp⟩
  | drop he h ih =>
      obtain ⟨T0, hm, he, hp⟩ := ih hin
      exact ⟨T0, List.mem_cons_of_mem _ hm, he, hp⟩

/-- Every eligible branch gets a kept entry (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem KRint_cover {E P bs kept r l s T0} (h : KRint E P bs kept)
    (hin : (r, l, s, T0) ∈ bs) (hE : E T0) : ∃ T1, (r, l, s, T1) ∈ kept ∧ P T0 T1 := by
  induction h with
  | nil => simp at hin
  | keep he hp h ih =>
      rcases List.mem_cons.mp hin with eq | hin
      · cases eq; exact ⟨_, List.mem_cons_self, hp⟩
      · obtain ⟨T1, hm, hp⟩ := ih hin
        exact ⟨T1, List.mem_cons_of_mem _ hm, hp⟩
  | drop he h ih =>
      rcases List.mem_cons.mp hin with eq | hin
      · cases eq; exact (he hE).elim
      · exact ih hin

/-- Every eligible ext branch gets a kept entry (port; see `KRint_cover` for credit). -/
theorem KRext_cover {E P bs kept l s T0} (h : KRext E P bs kept)
    (hin : (l, s, T0) ∈ bs) (hE : E T0) : ∃ T1, (l, s, T1) ∈ kept ∧ P T0 T1 := by
  induction h with
  | nil => simp at hin
  | keep he hp h ih =>
      rcases List.mem_cons.mp hin with eq | hin
      · cases eq; exact ⟨_, List.mem_cons_self, hp⟩
      · obtain ⟨T1, hm, hp⟩ := ih hin
        exact ⟨T1, List.mem_cons_of_mem _ hm, hp⟩
  | drop he h ih =>
      rcases List.mem_cons.mp hin with eq | hin
      · cases eq; exact (he hE).elim
      · exact ih hin

/-- Retention exists whenever sub-witnesses do (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem KRint_build (E : SessionType → Prop) (P : SessionType → SessionType → Prop)
    (bs : List (Role × Lab × DataSort × SessionType))
    (h : ∀ r l s T0, (r, l, s, T0) ∈ bs → E T0 → ∃ T1, P T0 T1) :
    ∃ kept, KRint E P bs kept := by
  classical
  induction bs with
  | nil => exact ⟨[], .nil⟩
  | cons b bs ih =>
      rcases b with ⟨r, l, s, T0⟩
      obtain ⟨kept, hk⟩ := ih (fun r l s T hm => h r l s T (List.mem_cons_of_mem _ hm))
      by_cases he : E T0
      · obtain ⟨T1, hp⟩ := h r l s T0 List.mem_cons_self he
        exact ⟨(r, l, s, T1) :: kept, .keep he hp hk⟩
      · exact ⟨kept, .drop he hk⟩

/-- Ext retention exists whenever sub-witnesses do (port; see `KRint_build` for credit). -/
theorem KRext_build (E : SessionType → Prop) (P : SessionType → SessionType → Prop)
    (bs : List (Lab × DataSort × SessionType))
    (h : ∀ l s T0, (l, s, T0) ∈ bs → E T0 → ∃ T1, P T0 T1) :
    ∃ kept, KRext E P bs kept := by
  classical
  induction bs with
  | nil => exact ⟨[], .nil⟩
  | cons b bs ih =>
      rcases b with ⟨l, s, T0⟩
      obtain ⟨kept, hk⟩ := ih (fun l s T hm => h l s T (List.mem_cons_of_mem _ hm))
      by_cases he : E T0
      · obtain ⟨T1, hp⟩ := h l s T0 List.mem_cons_self he
        exact ⟨(l, s, T1) :: kept, .keep he hp hk⟩
      · exact ⟨kept, .drop he hk⟩

