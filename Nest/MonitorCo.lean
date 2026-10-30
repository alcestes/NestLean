import Nest.MonitorLTS

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# MonitorCo: coinductive maximal monitor transitions.

Coinductive twin of `mon_tr_yes_max_deriv` (`Nest/MonitorLTS.lean:254`).
Finite `max_deriv` rejects looping prefix types such as
`μX. r?{a : q?x.end, b : X}` under `q?x` (see `notes/mon_tr_yes_max_deriv_co.md`):
`kept=[a]` fails coverage, `kept∋b` needs maximality of the same `T`.
`mon_tr_yes_max_deriv_co` keeps coverage/order but replaces the universal
`hallMax : ∀ hsub, max hsub` by one corecursive call per branch pair and adds
target folding, so the loop is productive instead of ill-founded.
-/

/-- Coinductive maximal derivation: one corecursive call per kept branch
    (not `∀ hsub`), plus source unfold and target fold. -/
coinductive mon_tr_yes_max_deriv_co
    : SessionType → ext_tag → SessionType → Prop where
  | base {T : SessionType} {γ : ext_tag} {V : SessionType}
      (hT : T.WellFormed)
      (h : mon_tr_yes_base T γ V) :
      mon_tr_yes_max_deriv_co T γ V
  | pfxInt {branches kept : List (Role × Lab × DataSort × SessionType)}
      {q : Role} {lab : Lab} {S : DataSort}
      (hWF : (SessionType.internalChoice branches).WellFormed)
      (hne : branches ≠ [] ∧ kept ≠ [])
      (hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ branches → q ≠ p')
      (hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
        (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
          mon_tr_yes_max_deriv_co T0 (ext_tag.recv q lab S) T1)
      (hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
        (r, l, s, T1) ∈ kept →
          ∃ T0, (r, l, s, T0) ∈ branches ∧
            ∃ V, mon_tr_yes_exist T0 (ext_tag.recv q lab S) V)
      (hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
        (r, l, s, T0) ∈ branches →
          (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) →
          ∃ T1, (r, l, s, T1) ∈ kept)
      (horder : List.Sublist
        (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
        (branches.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))) :
      mon_tr_yes_max_deriv_co
        (SessionType.internalChoice branches) (ext_tag.recv q lab S)
        (SessionType.internalChoice kept)
  | pfxExt {p : Role} {branches kept : List (Lab × DataSort × SessionType)}
      {q : Role} {lab : Lab} {S : DataSort}
      (hWF : (SessionType.externalChoice p branches).WellFormed)
      (hne : branches ≠ [] ∧ kept ≠ [])
      (hneq : q ≠ p)
      (hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
        (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
          mon_tr_yes_max_deriv_co T0 (ext_tag.recv q lab S) T1)
      (hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
        (l, s, T1) ∈ kept →
          ∃ T0, (l, s, T0) ∈ branches ∧
            ∃ V, mon_tr_yes_exist T0 (ext_tag.recv q lab S) V)
      (hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
        (l, s, T0) ∈ branches →
          (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) →
          ∃ T1, (l, s, T1) ∈ kept)
      (horder : List.Sublist
        (kept.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
        (branches.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))) :
      mon_tr_yes_max_deriv_co
        (SessionType.externalChoice p branches) (ext_tag.recv q lab S)
        (SessionType.externalChoice p kept)
  | recL {X : String} {B : SessionType} {γ : ext_tag} {V : SessionType}
      (hWF : (SessionType.tRec X B).WellFormed)
      (h : mon_tr_yes_max_deriv_co (substSessionType B X (SessionType.tRec X B)) γ V) :
      mon_tr_yes_max_deriv_co (SessionType.tRec X B) γ V
  | recR {Y : String} {C : SessionType} {T : SessionType} {γ : ext_tag}
      (hWF : T.WellFormed)
      (h : mon_tr_yes_max_deriv_co T γ (substSessionType C Y (SessionType.tRec Y C))) :
      mon_tr_yes_max_deriv_co T γ (SessionType.tRec Y C)

/-- Coinductive yes-transition (allows recursive targets). Requires
well-formed source and target. -/
abbrev mon_tr_yes_co (T : SessionType) (γ : ext_tag) (V : SessionType)
    (hT : T.WellFormed) (hV : V.WellFormed) : Prop :=
  mon_tr_yes_max_deriv_co T γ V

/-- Coinductive single-step reachability: target of a `mon_tr_yes_co`
    transition (existentially packing the label and the well-formedness
    proofs that `mon_tr_yes_co` requires). -/
def CoStep : SessionType → SessionType → Prop :=
  fun T U => ∃ γ : ext_tag, ∃ hT : T.WellFormed, ∃ hU : U.WellFormed,
    mon_tr_yes_co T γ U hT hU

/-- A session type is co-monitorable when it is well-formed and its
    `mon_tr_yes_co`-reachability closure is finite up to `UnfoldEquiv`:
    finitely many representatives cover every reachable state. This is the
    coinductive analogue of `Monitorable` (`Nest/Drainability.lean`), which
    uses the single-step `PruneStep` relation instead. -/
def MonitorableCo (T : SessionType) : Prop :=
  T.WellFormed ∧ ∃ F : Finset SessionType, ∀ U : SessionType,
    Relation.ReflTransGen CoStep T U → ∃ V ∈ F, U.UnfoldEquiv V

/-- Every `CoStep`-reachable state is well-formed (`CoStep` packs the target
    proof, and the source is well-formed by hypothesis). -/
theorem coStep_reachable_wf {T U : SessionType} (hT : T.WellFormed)
    (h : Relation.ReflTransGen CoStep T U) : U.WellFormed := by
  induction h with
  | refl => exact hT
  | tail _ hStep _ =>
    unfold CoStep at hStep
    obtain ⟨_, _, hU, _⟩ := hStep
    exact hU

/-- Co-monitorability transports down reachability: the closure of a reachable
    state is contained in the closure of the source (by transitivity). -/
theorem MonitorableCo.mono {T U : SessionType}
    (h : Relation.ReflTransGen CoStep T U) (hFin : MonitorableCo T) :
    MonitorableCo U := by
  obtain ⟨hWT, F, hCov⟩ := hFin
  exact ⟨coStep_reachable_wf hWT h, F, fun W hW => hCov W (h.trans hW)⟩
