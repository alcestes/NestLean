import Cslib

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# SessionSyntax: Session syntax and well-formedness.

Core session-type grammar, substitution, free variables, and well-formedness
predicates. Root of the import chain: every other `Nest` module transitively
depends on this file.
-/

-- ================================================================
-- Basic types: DataSorts, Roles, Labels
-- ================================================================

/-- Data sorts (message payload types), represented as strings. -/
abbrev DataSort : Type := String
/-- Roles (protocol participants), represented as strings. -/
abbrev Role : Type := String
/-- Labels (message labels), represented as strings. -/
abbrev Lab : Type := String

namespace DataSort
end DataSort

namespace Role
end Role

namespace Lab
end Lab

-- ================================================================
-- Session types (End host model)
-- ================================================================

/--
  Session types with multi-input queues (grammar).
    T ::= ⊕_{i∈I} p_i?lab_i(S_i).T_i
         | &_{i∈I} p?lab_i(S_i).T_i
         | end
         | μt.T
         | t
 -/
inductive SessionType : Type where
  | internalChoice : List (Role × Lab × DataSort × SessionType) → SessionType
  | externalChoice : Role → List (Lab × DataSort × SessionType) → SessionType
  | tEnd : SessionType
  | tRec : String → SessionType → SessionType
  | tVar : String → SessionType

/-- Substitution T{X ↦ U} (capture-avoiding by position). -/
def substSessionType (T : SessionType) (X : String) (U : SessionType) : SessionType :=
  match T with
  | .tVar Y => if X = Y then U else T
  | .tEnd => .tEnd
  | .internalChoice branches =>
    let rec goInt : List (Role × Lab × DataSort × SessionType) → List (Role × Lab × DataSort × SessionType)
      | [] => []
      | ((p, lab, S, T') :: rest) => (p, lab, S, substSessionType T' X U) :: goInt rest
    .internalChoice (goInt branches)
  | .externalChoice p branches =>
    let rec goExt : List (Lab × DataSort × SessionType) → List (Lab × DataSort × SessionType)
      | [] => []
      | ((lab, S, T') :: rest) => (lab, S, substSessionType T' X U) :: goExt rest
    .externalChoice p (goExt branches)
  | .tRec Y T' =>
    if X = Y then T else .tRec Y (substSessionType T' X U)

/-- `substSessionType.goInt` maps the substitution pointwise over internal-choice branch targets. -/
lemma go_int_eq_map (X : String) (U : SessionType) (l : List (Role × Lab × DataSort × SessionType)) :
    substSessionType.goInt X U l = l.map (λ (p, lab, S, T') => (p, lab, S, substSessionType T' X U)) := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rcases h with ⟨p, lab, S, T'⟩
    simp [substSessionType.goInt, ih]

/-- `substSessionType.goExt` maps the substitution pointwise over external-choice branch targets. -/
lemma go_ext_eq_map (X : String) (U : SessionType) (l : List (Lab × DataSort × SessionType)) :
    substSessionType.goExt X U l = l.map (λ (lab, S, T') => (lab, S, substSessionType T' X U)) := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rcases h with ⟨lab, S, T'⟩
    simp [substSessionType.goExt, ih]

/-- Free type variables of a session type. -/
def SessionType.fv : SessionType → List String
  | tEnd => []
  | SessionType.tVar X => [X]
  | SessionType.tRec X T => (SessionType.fv T).filter (λ x => x != X)
  | SessionType.internalChoice branches => goInt branches
  | SessionType.externalChoice p branches => goExt branches
where
  goInt : List (Role × Lab × DataSort × SessionType) → List String
    | [] => []
    | ((_, _, _, T) :: rest) => SessionType.fv T ++ goInt rest
  goExt : List (Lab × DataSort × SessionType) → List String
    | [] => []
    | ((_, _, T) :: rest) => SessionType.fv T ++ goExt rest

/-- A session type is closed when it has no free type variables. -/
def SessionType.IsClosed (T : SessionType) : Prop :=
  T.fv = []

/-- A session type is NoDupl if all its internal/external choices are
    non-empty, have no duplicate pairs of role/label (for internal choice) or labels
    (for external choice), and all their branch targets are recursively NoDupl. -/
inductive SessionType.NoDupl : SessionType → Prop where
  | end : NoDupl tEnd
  | tVar (X : String) : NoDupl (SessionType.tVar X)
  | internalChoice {branches : List (Role × Lab × DataSort × SessionType)}
      (h_nodup : List.Nodup (List.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) branches))
      (h_nonempty : branches ≠ [])
      (h_branches : ∀ (x : Role × Lab × DataSort × SessionType), x ∈ branches → NoDupl x.2.2.2) :
    NoDupl (SessionType.internalChoice branches)
  | externalChoice {r : Role} {branches : List (Lab × DataSort × SessionType)}
      (h_nodup : List.Nodup (List.map (λ x : Lab × DataSort × SessionType => x.1) branches))
      (h_nonempty : branches ≠ [])
      (h_branches : ∀ (x : Lab × DataSort × SessionType), x ∈ branches → NoDupl x.2.2) :
    NoDupl (SessionType.externalChoice r branches)
  | tRec {X : String} {T : SessionType} (h : NoDupl T) : NoDupl (SessionType.tRec X T)

/-- `Guarded X T` holds when every free occurrence of `tVar X` in `T`
    appears under at least one `internalChoice` or `externalChoice`. -/
def SessionType.Guarded (X : String) : SessionType → Prop
  | tEnd => True
  | SessionType.tVar Y => X ≠ Y
  | SessionType.internalChoice _ => True
  | SessionType.externalChoice _ _ => True
  | SessionType.tRec Y T' => SessionType.Guarded X T'

/-- A session type is contractive when every `tRec X T` has a body `T` that is
    itself contractive and guarded for `X` (i.e., all free `tVar X` in `T` are
    under a choice).  This rules out ill‑formed terms like `tRec X (tVar X)`. -/
inductive SessionType.Contractive : SessionType → Prop where
  | end : Contractive tEnd
  | tVar (X : String) : Contractive (SessionType.tVar X)
  | internalChoice {branches : List (Role × Lab × DataSort × SessionType)}
      (h_branches : ∀ (x : Role × Lab × DataSort × SessionType), x ∈ branches → Contractive x.2.2.2) :
    Contractive (SessionType.internalChoice branches)
  | externalChoice {r : Role} {branches : List (Lab × DataSort × SessionType)}
      (h_branches : ∀ (x : Lab × DataSort × SessionType), x ∈ branches → Contractive x.2.2) :
    Contractive (SessionType.externalChoice r branches)
  | tRec {X : String} {T : SessionType}
      (h_contractive : Contractive T)
      (h_guarded : Guarded X T) :
    Contractive (SessionType.tRec X T)

/-- A session type is well-formed when it has no duplicate labels (`NoDupl`), no free variables
   (`IsClosed`), and is contractive (`Contractive`). -/
def SessionType.WellFormed (T : SessionType) := T.NoDupl ∧ T.IsClosed ∧ T.Contractive

/-- A session type is recursion-free (`NoRec`) when it contains no `tRec`
    anywhere. Stepping stone for the maximal-determinism program
    (`mon_tr_yes_target_unique` in `Nest.MonitorToolkit`): without `tRec`,
    substitution-duplication and unfold-cycles vanish — every
    `mon_tr_yes_max_deriv` case
    either is vacuous (`unfold`/`base-tRec` pruned by `ne_tRec`) or goes to
    strictly smaller branch targets, so plain size induction closes.
    Recursive types are first head-normalised instead (substitution-free
    head-normal forms, no duplication blowup). -/
inductive SessionType.NoRec : SessionType → Prop where
  | end : NoRec tEnd
  | tVar (X : String) : NoRec (SessionType.tVar X)
  | internalChoice {branches : List (Role × Lab × DataSort × SessionType)}
      (h_branches : ∀ (x : Role × Lab × DataSort × SessionType), x ∈ branches → NoRec x.2.2.2) :
    NoRec (SessionType.internalChoice branches)
  | externalChoice {r : Role} {branches : List (Lab × DataSort × SessionType)}
      (h_branches : ∀ (x : Lab × DataSort × SessionType), x ∈ branches → NoRec x.2.2) :
    NoRec (SessionType.externalChoice r branches)

namespace SessionType
/-- Unfold-equivalence of session types (`UnfoldEquiv T T'`): coinductive
    bisimilarity modulo top-level recursion unfolding (`recL`, `recR`) and
    structural congruence on choices (`intC`, `extC`), `tEnd`, and `tVar`.
    Equates session types that have the same infinite unfolding tree
    (including vacuous `tRec` wrappers, alpha-renamed binders, folded vs
    unfolded recursive targets, and `k`-fold unrollings). -/
coinductive UnfoldEquiv : SessionType → SessionType → Prop where
  | end : UnfoldEquiv tEnd tEnd
  | var (X : String) : UnfoldEquiv (SessionType.tVar X) (SessionType.tVar X)
  | intC {branches branches' : List (Role × Lab × DataSort × SessionType)}
      (hkeys : branches.map (fun x ↦ (x.1, x.2.1, x.2.2.1)) =
        branches'.map (fun x ↦ (x.1, x.2.1, x.2.2.1)))
      (hrel : ∀ (a b : Role × Lab × DataSort × SessionType),
        (a, b) ∈ branches.zip branches' → UnfoldEquiv a.2.2.2 b.2.2.2) :
    UnfoldEquiv (SessionType.internalChoice branches) (SessionType.internalChoice branches')
  | extC {p : Role} {branches branches' : List (Lab × DataSort × SessionType)}
      (hkeys : branches.map (fun x ↦ (x.1, x.2.1)) =
        branches'.map (fun x ↦ (x.1, x.2.1)))
      (hrel : ∀ (a b : Lab × DataSort × SessionType),
        (a, b) ∈ branches.zip branches' → UnfoldEquiv a.2.2 b.2.2) :
    UnfoldEquiv (SessionType.externalChoice p branches) (SessionType.externalChoice p branches')
  | recL {X : String} {B U : SessionType}
      (h : UnfoldEquiv (substSessionType B X (SessionType.tRec X B)) U) :
    UnfoldEquiv (SessionType.tRec X B) U
  | recR {Y : String} {T C : SessionType}
      (h : UnfoldEquiv T (substSessionType C Y (SessionType.tRec Y C))) :
    UnfoldEquiv T (SessionType.tRec Y C)
end SessionType

/-- Two participant lists denote the same set of roles (extensional equality). -/
def SessionType.SameParticipants (S1 S2 : List Role) : Prop :=
  ∀ r : Role, r ∈ S1 ↔ r ∈ S2

/-- An external-choice path to the recursion variable: `LeadsTo X T S`
    holds when following branches of `T` reaches `tVar X`, collecting the
    owners of the traversed external choices in `S`. Internal choices are
    traversed transparently (they contribute no participants); `tRec`
    binders are traversed transparently unless they rebind `X`, in which
    case paths to the shadowed variable do not count. -/
inductive SessionType.LeadsTo (X : String) : SessionType → List Role → Prop where
  | var : LeadsTo X (SessionType.tVar X) []
  | intC {branches : List (Role × Lab × DataSort × SessionType)}
      {p : Role} {lab : Lab} {S : DataSort} {T0 : SessionType} {Ss : List Role}
      (hmem : (p, lab, S, T0) ∈ branches) (h : LeadsTo X T0 Ss) :
    LeadsTo X (SessionType.internalChoice branches) Ss
  | extC {p : Role} {branches : List (Lab × DataSort × SessionType)}
      {lab : Lab} {S : DataSort} {T0 : SessionType} {Ss : List Role}
      (hmem : (lab, S, T0) ∈ branches) (h : LeadsTo X T0 Ss) :
    LeadsTo X (SessionType.externalChoice p branches) (p :: Ss)
  | trec {Y : String} {B : SessionType} {Ss : List Role}
      (hne : Y ≠ X) (h : LeadsTo X B Ss) :
    LeadsTo X (SessionType.tRec Y B) Ss


/-- Role occurrence in a session type (paper `formal-model.tex:405`:
    networks require "roleP does not occur in stqT"). Inductive shape
    (rather than structural recursion into branch lists) so no termination
    proof is needed; only constructors are ever used. -/
inductive SessionType.Occurs (r : Role) : SessionType → Prop where
  | intSender {branches : List (Role × Lab × DataSort × SessionType)}
      {p : Role} {lab : Lab} {S : DataSort} {T0 : SessionType}
      (hmem : (p, lab, S, T0) ∈ branches) (heq : p = r) :
    Occurs r (SessionType.internalChoice branches)
  | intTarget {branches : List (Role × Lab × DataSort × SessionType)}
      {p : Role} {lab : Lab} {S : DataSort} {T0 : SessionType}
      (hmem : (p, lab, S, T0) ∈ branches) (h : Occurs r T0) :
    Occurs r (SessionType.internalChoice branches)
  | extOwner {p : Role} {branches : List (Lab × DataSort × SessionType)}
      (heq : p = r) :
    Occurs r (SessionType.externalChoice p branches)
  | extTarget {p : Role} {branches : List (Lab × DataSort × SessionType)}
      {lab : Lab} {S : DataSort} {T0 : SessionType}
      (hmem : (lab, S, T0) ∈ branches) (h : Occurs r T0) :
    Occurs r (SessionType.externalChoice p branches)
  | recBody {X : String} {B : SessionType} (h : Occurs r B) :
    Occurs r (SessionType.tRec X B)


/-- Pairwise-distinct (role, label) pairs imply pairwise-distinct (role, label, sort)
    triples. -/
lemma nodup_triple_of_nodup_pair {branches : List (Role × Lab × DataSort × SessionType)}
    (h : List.Nodup (List.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) branches)) :
    List.Nodup (List.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) branches) := by
  induction branches with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨p, lab, S, T0⟩
    cases h
    rename_i h_tl_nodup h_head_notin
    constructor
    · intro hp hpm h_eq
      have hmem : (hp.1, hp.2.1) ∈ tl.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) := by
        rcases (List.mem_map.mp hpm) with ⟨u, hu, huEq⟩
        refine List.mem_map.mpr ⟨u, hu, ?_⟩
        exact congrArg (λ z : Role × Lab × DataSort => (z.1, z.2.1)) huEq
      exact (h_head_notin (hp.1, hp.2.1) hmem)
        (by simpa using (congrArg (λ z : Role × Lab × DataSort => (z.1, z.2.1)) h_eq))
    · exact ih h_tl_nodup

/-- Non-emptiness projections: `NoDupl` (hence `WellFormed`) already requires
    non-empty choices, so empty-branch cases discharge by inversion instead of
    threading `≠ []` hypotheses. -/
lemma SessionType.NoDupl.ne_of_internalChoice
    {branches : List (Role × Lab × DataSort × SessionType)}
    (h : NoDupl (SessionType.internalChoice branches)) : branches ≠ [] := by
  cases h with
  | internalChoice _ hne _ => exact hne

/-- Non-emptiness from external-choice `NoDupl`: external choices are non-empty, so empty-branch
   cases discharge by inversion. -/
lemma SessionType.NoDupl.ne_of_externalChoice
    {r : Role} {branches : List (Lab × DataSort × SessionType)}
    (h : NoDupl (SessionType.externalChoice r branches)) : branches ≠ [] := by
  cases h with
  | externalChoice _ hne _ => exact hne

/-- Triple-key nodup from choice `NoDupl` (pair-nodup implies triple-nodup). -/
lemma SessionType.NoDupl.triple_nodup_of_internalChoice
    {branches : List (Role × Lab × DataSort × SessionType)}
    (h : NoDupl (SessionType.internalChoice branches)) :
    List.Nodup (List.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))
      branches) := by
  cases h with
  | internalChoice hpair _ _ => exact nodup_triple_of_nodup_pair hpair

/-- `WellFormed` conveniences (rewrite the type equation, then project). -/
lemma SessionType.WellFormed.ne_of_internalChoice {T : SessionType}
    {branches : List (Role × Lab × DataSort × SessionType)}
    (hTq : T = SessionType.internalChoice branches) (hWF : T.WellFormed) :
    branches ≠ [] := by
  subst hTq
  exact hWF.1.ne_of_internalChoice

