import Nest.MonitorCoRel
import Nest.MonitorCoBase
import Nest.FoldExistsCo
import Nest.MonitorLTSCo

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-! # SemFoldCo: semantic fold layer for the `Co` soundness chain.

Coinductive twins of the head-normalisation, base, alignment, and
pruning-congruence helpers (`hnf_wf_co`, `hnf_exists_co`,
`base_eqv_co`, `alignInt_mem_r_co`, `alignInt_wf_co`,
`alignExt_wf_co`, `Ex_eqv_co`, `KRint_left_co`, `KRext_left_co`,
`PruneN_eqv_l_co`, `Prune_eqv_l_co`, `Prune_base_co`), feeding the
`SemFoldCo` alignment invariant below.

Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>.

`SemFoldCo T Q M` (via `Prune` + `Eqv`) is the alignment invariant:
forward progress steps the fold (`SemFoldCo_send`,
`SemFoldCo_recv_accept`), the backward direction replays any observed
step (`SemFoldCo_send_any`, `SemFoldCo_recv_any`), and dequeue leaves
the monitor state unchanged (`SemFoldCo_dequeue`). Uniqueness is up to
`Eqv` (`SemFoldCo_unique`, via `Prune_unique`), never syntactic.
-/

-- ================================================================
-- Equivalence helpers (see header for credit).
-- ================================================================

/-- Head-normal unfolding preserves well-formedness. -/
theorem hnf_wf_co {T H : SessionType} (wf : T.WellFormed) (head : hnf T H) :
    H.WellFormed :=
  SessionType.wellFormedUnfold wf head.1

/-- Every well-formed type has a head-normal unfolding. -/
theorem hnf_exists_co {T : SessionType} (wf : T.WellFormed) : ∃ H, hnf T H :=
  unfoldStar_normal_exists T wf.2.2 wf.2.1

/-- The depth-1 equivalence class of a type has a head-normal form. -/
theorem teqN_1_hnf_co {T U : SessionType} (same : teqN 1 T U) : ∃ H, hnf U H := by
  obtain ⟨_, H, _, head, _⟩ := same
  exact ⟨H, head⟩

/-- Rightward internal alignment lookup (mirror of `alignInt_mem`). -/
theorem alignInt_mem_r_co {Q : SessionType → SessionType → Prop}
    {bs cs : List (Role × Lab × DataSort × SessionType)} {p : Role} {l : Lab} {s : DataSort}
    {U : SessionType} (aligned : alignInt Q bs cs) (member : (p, l, s, U) ∈ cs) :
    ∃ T, (p, l, s, T) ∈ bs ∧ Q T U := by
  exact alignInt_mem (Q := fun U T => Q T U) (Forall2_sym (fun _ _ h =>
    ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2⟩) aligned) member

/-- A base encoder step transports along equivalence. -/
theorem base_eqv_co {T U V : SessionType} {g : ext_tag}
    (base : mon_tr_yes_base T g V) (same : Eqv T U) :
    ∃ W, mon_tr_yes_base U g W ∧ Eqv V W := by
  obtain ⟨H, head, direct⟩ := base_hnf base
  obtain ⟨HU, head'⟩ := teqN_1_hnf_co (same 1)
  have aligned := Eqv_shape same head head'
  cases g <;> cases H <;> cases HU <;>
    simp only [base_direct, shapeEq] at direct aligned <;> try contradiction
  · obtain ⟨W, member, next⟩ := alignInt_mem aligned direct.2
    refine ⟨W, base_of_hnf head' ⟨?_, member⟩, next⟩
    rw [← alignInt_keys aligned]
    exact direct.1
  · obtain ⟨rfl, unique, member⟩ := direct
    obtain ⟨rfl, aligned⟩ := aligned
    obtain ⟨W, member', next⟩ := alignExt_mem aligned member
    refine ⟨W, base_of_hnf head' ⟨rfl, ?_, member'⟩, next⟩
    rw [← alignExt_keys aligned]
    exact unique

/-- Alignment preserves well-formedness on both sides (internal). -/
theorem alignInt_wf_co {Q : SessionType → SessionType → Prop} {bs cs : List (Role × Lab × DataSort × SessionType)}
    (aligned : alignInt Q bs cs) (left : (SessionType.internalChoice bs).WellFormed)
    (right : (SessionType.internalChoice cs).WellFormed) :
    alignInt (fun T U => Q T U ∧ T.WellFormed ∧ U.WellFormed) bs cs :=
  Forall2_impl (fun _ hx _ hy h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2,
    wf_of_mem_int left hx, wf_of_mem_int right hy⟩) aligned

/-- Alignment preserves well-formedness on both sides (external). -/
theorem alignExt_wf_co {Q : SessionType → SessionType → Prop} {p q : Role} {bs cs : List (Lab × DataSort × SessionType)}
    (aligned : alignExt Q bs cs) (left : (SessionType.externalChoice p bs).WellFormed)
    (right : (SessionType.externalChoice q cs).WellFormed) :
    alignExt (fun T U => Q T U ∧ T.WellFormed ∧ U.WellFormed) bs cs :=
  Forall2_impl (fun _ hx _ hy h => ⟨h.1, h.2.1, h.2.2,
    wf_of_mem_ext left hx, wf_of_mem_ext right hy⟩) aligned

/-- Existential acceptance transports along equivalence. -/
theorem Ex_eqv_co {T U V : SessionType} {g : ext_tag}
    (accept : mon_tr_yes_exist T g V) (same : Eqv T U) (wf : U.WellFormed) : Ex U g := by
  induction accept generalizing U with
  | base base =>
      obtain ⟨W, base', _⟩ := base_eqv_co base same
      exact ⟨W, .base base'⟩
  | @pfxInt bs kept q lab S target nonempty off targetEq all unique keys ih =>
      obtain ⟨H, head⟩ := hnf_exists_co wf
      have hw := hnf_wf_co wf head
      have shape := Eqv_shape same (hnf_self trivial) head
      cases H <;> (simp only [shapeEq] at shape; try contradiction)
      rename_i cs
      obtain ⟨⟨r, l, s, W⟩, keptMem⟩ := List.exists_mem_of_ne_nil kept nonempty.2
      obtain ⟨T₀, member⟩ := keys r l s W keptMem
      obtain ⟨U₀, member', next⟩ := alignInt_mem shape member
      have accepted := ih T₀ W r l s member keptMem next (wf_of_mem_int hw member')
      apply (Ex_unfoldstar head.1).mpr
      apply Ex_int_single hw ?_ member' accepted
      intro p a b V member''
      obtain ⟨T', memberT, _⟩ := alignInt_mem_r_co shape member''
      exact off p a b T' memberT
  | @pfxExt p bs kept q lab S target nonempty off targetEq all unique keys ih =>
      obtain ⟨H, head⟩ := hnf_exists_co wf
      have hw := hnf_wf_co wf head
      have shape := Eqv_shape same (hnf_self trivial) head
      cases H <;> (simp only [shapeEq] at shape; try contradiction)
      rename_i p' cs
      obtain ⟨rfl, shape⟩ := shape
      obtain ⟨⟨l, s, W⟩, keptMem⟩ := List.exists_mem_of_ne_nil kept nonempty.2
      obtain ⟨T₀, member⟩ := keys l s W keptMem
      obtain ⟨U₀, member', next⟩ := alignExt_mem shape member
      have accepted := ih T₀ W l s member keptMem next (wf_of_mem_ext hw member')
      exact (Ex_unfoldstar head.1).mpr (Ex_ext_single hw off member' accepted)
  | unfold next ih =>
      exact ih (fun n => (teqN_unfold_l n).mp (same n)) wf

/-- Existential acceptance transports along equivalence (packed form). -/
theorem Ex_eqv'_co {T U : SessionType} {g : ext_tag}
    (accept : Ex T g) (same : Eqv T U) (wf : U.WellFormed) : Ex U g :=
  Ex_eqv_co accept.choose_spec same wf

/-- Left-alignment of internal retention. -/
theorem KRint_left_co {E : SessionType → Prop} {P Q : SessionType → SessionType → Prop}
    {bs cs kept : List (Role × Lab × DataSort × SessionType)}
    (aligned : alignInt Q bs cs) (pruned : KRint E P bs kept)
    (eligcond : ∀ T U, Q T U → (E T ↔ E U)) :
    KRint E (fun U V => ∃ T, Q T U ∧ P T V) cs kept := by
  induction aligned generalizing kept with
  | nil => cases pruned; exact .nil
  | @cons x y xs ys same rest ih =>
      rcases x with ⟨p, l, s, T⟩
      rcases y with ⟨p', l', s', U⟩
      rcases same with ⟨rfl, rfl, rfl, next⟩
      cases pruned with
      | keep eligible target tail =>
          exact .keep ((eligcond _ _ next).mp eligible) ⟨T, next, target⟩ (ih tail)
      | drop ineligible tail =>
          exact .drop (fun eligible => ineligible ((eligcond _ _ next).mpr eligible)) (ih tail)

/-- Left-alignment of external retention. -/
theorem KRext_left_co {E : SessionType → Prop} {P Q : SessionType → SessionType → Prop}
    {bs cs kept : List (Lab × DataSort × SessionType)}
    (aligned : alignExt Q bs cs) (pruned : KRext E P bs kept)
    (eligcond : ∀ T U, Q T U → (E T ↔ E U)) :
    KRext E (fun U V => ∃ T, Q T U ∧ P T V) cs kept := by
  induction aligned generalizing kept with
  | nil => cases pruned; exact .nil
  | @cons x y xs ys same rest ih =>
      rcases x with ⟨l, s, T⟩
      rcases y with ⟨l', s', U⟩
      rcases same with ⟨rfl, rfl, next⟩
      cases pruned with
      | keep eligible target tail =>
          exact .keep ((eligcond _ _ next).mp eligible) ⟨T, next, target⟩ (ih tail)
      | drop ineligible tail =>
          exact .drop (fun eligible => ineligible ((eligcond _ _ next).mpr eligible)) (ih tail)

/-- Stratified pruning transports along source equivalence. -/
theorem PruneN_eqv_l_co (n : Nat) {g : ext_tag} {T U R : SessionType}
    (same : Eqv T U) (wt : T.WellFormed) (wu : U.WellFormed)
    (pruned : PruneN n g T R) : PruneN n g U R := by
  induction n generalizing T U R with
  | zero => trivial
  | succ n ih =>
      rcases pruned with ⟨T₀, base, equal⟩ | ⟨H, HR, head, residual, next⟩
      · obtain ⟨U₀, base', equal'⟩ := base_eqv_co base same
        exact .inl ⟨U₀, base', teqN_trans (n + 1) (teqN_sym (n + 1) (equal' (n + 1))) equal⟩
      · obtain ⟨HU, head'⟩ := hnf_exists_co wu
        have shape := Eqv_shape same head head'
        have wh := hnf_wf_co wt head
        have whu := hnf_wf_co wu head'
        refine .inr ⟨HU, HR, head', residual, ?_⟩
        cases g <;> cases H <;> cases HR <;> (simp only [PfxStep] at next; try contradiction)
        all_goals cases HU <;> (simp only [shapeEq] at shape; try contradiction)
        · refine ⟨?_, next.2.1, ?_, ?_⟩
          · exact Forall2_nil_r shape next.1
          · intro p l s V member
            obtain ⟨W, member', _⟩ := alignInt_mem_r_co shape member
            exact next.2.2.1 p l s W member'
          · have kept := KRint_left_co (alignInt_wf_co shape wh whu) next.2.2.2
              (fun A B h => ⟨fun accept => Ex_eqv'_co accept h.1 h.2.2,
                fun accept => Ex_eqv'_co accept (Eqv_sym h.1) h.2.1⟩)
            exact KRint_impl (fun _ _ _ _ _ => Iff.rfl)
              (fun _ _ _ _ _ _ ⟨A, h, pruned⟩ => ih h.1 h.2.1 h.2.2 pruned) kept
        · obtain ⟨rfl, shape⟩ := shape
          refine ⟨next.1, next.2.1, Forall2_nil_r shape next.2.2.1, next.2.2.2.1, ?_⟩
          have kept := KRext_left_co (alignExt_wf_co shape wh whu) next.2.2.2.2
            (fun A B h => ⟨fun accept => Ex_eqv'_co accept h.1 h.2.2,
              fun accept => Ex_eqv'_co accept (Eqv_sym h.1) h.2.1⟩)
          exact KRext_impl (fun _ _ _ _ => Iff.rfl)
            (fun _ _ _ _ _ ⟨A, h, pruned⟩ => ih h.1 h.2.1 h.2.2 pruned) kept

/-- Pruning transports along source equivalence. -/
theorem Prune_eqv_l_co {g : ext_tag} {T U R : SessionType}
    (same : Eqv T U) (wt : T.WellFormed) (wu : U.WellFormed)
    (pruned : Prune g T R) : Prune g U R :=
  fun n => PruneN_eqv_l_co n same wt wu (pruned n)

/-- A base step is a pruning derivation. -/
theorem Prune_base_co {g : ext_tag} {T U : SessionType}
    (base : mon_tr_yes_base T g U) (wf : U.WellFormed) : Prune g T U := by
  intro n
  cases n with
  | zero => trivial
  | succ n => exact .inl ⟨U, base, teqN_refl (n + 1) wf⟩

/-- Internal retention holds at every depth uniformly. -/
theorem KRint_allDepths_co {E : SessionType → Prop} {P : Nat → SessionType → SessionType → Prop}
    {bs kept : List (Role × Lab × DataSort × SessionType)}
    (all : ∀ n, KRint E (P n) bs kept) :
    KRint E (fun T U => ∀ n, P n T U) bs kept := by
  have start := all 0
  induction start with
  | nil => exact .nil
  | @keep p l s T U bs kept eligible next rest ih =>
      have pieces : ∀ n, P n T U ∧ KRint E (P n) bs kept := by
        intro n
        cases all n with
        | keep _ next rest => exact ⟨next, rest⟩
        | drop absent _ => exact False.elim (absent eligible)
      exact .keep eligible (fun n => (pieces n).1) (ih (fun n => (pieces n).2))
  | @drop p l s T bs kept ineligible rest ih =>
      apply KRint.drop ineligible
      apply ih
      intro n
      cases all n with
      | keep eligible _ _ => exact False.elim (ineligible eligible)
      | drop _ rest => exact rest

/-- External retention holds at every depth uniformly. -/
theorem KRext_allDepths_co {E : SessionType → Prop} {P : Nat → SessionType → SessionType → Prop}
    {bs kept : List (Lab × DataSort × SessionType)}
    (all : ∀ n, KRext E (P n) bs kept) :
    KRext E (fun T U => ∀ n, P n T U) bs kept := by
  have start := all 0
  induction start with
  | nil => exact .nil
  | @keep l s T U bs kept eligible next rest ih =>
      have pieces : ∀ n, P n T U ∧ KRext E (P n) bs kept := by
        intro n
        cases all n with
        | keep _ next rest => exact ⟨next, rest⟩
        | drop absent _ => exact False.elim (absent eligible)
      exact .keep eligible (fun n => (pieces n).1) (ih (fun n => (pieces n).2))
  | @drop l s T bs kept ineligible rest ih =>
      apply KRext.drop ineligible
      apply ih
      intro n
      cases all n with
      | keep eligible _ _ => exact False.elim (ineligible eligible)
      | drop _ rest => exact rest

-- ================================================================
-- Semantic fold (ported; see header for credit).
-- ================================================================

/-- Semantic fold: folding queue `Q` into `T` yields `M`. The head case is
    equivalence (`Eqv`), the cons case goes through one `Prune` step. -/
def SemFoldCo (T : SessionType) : Queue → SessionType → Prop
  | [], M => Eqv M T ∧ M.WellFormed
  | .msg p l s :: Q, M => ∃ U, U.WellFormed ∧ Prune (.recv p l s) T U ∧ SemFoldCo U Q M

/-- Folded states are well-formed. -/
theorem SemFoldCo_wf {Q : Queue} {T M : SessionType} (h : SemFoldCo T Q M) :
    M.WellFormed := by
  induction Q generalizing T with
  | nil => exact h.2
  | cons msg Q ih => obtain ⟨U, _, _, rest⟩ := h; exact ih rest

/-- Session steps lift to head-normal-form steps. -/
theorem st_trans_hnf_co {T U : SessionType} {a : st_label} (step : st_trans T a U) :
    ∃ H, hnf T H ∧ st_trans H a U := by
  induction step with
  | intC member => exact ⟨_, hnf_self trivial, .intC member⟩
  | extC member => exact ⟨_, hnf_self trivial, .extC member⟩
  | tRec step ih => obtain ⟨H, head, next⟩ := ih; exact ⟨H, hnf_rec_iff'.mpr head, next⟩

/-- Head-normal-form steps replay at the source. -/
theorem st_trans_of_hnf_co {T H U : SessionType} {a : st_label}
    (head : hnf T H) (step : st_trans H a U) : st_trans T a U := by
  obtain ⟨steps, normal⟩ := head
  induction steps with
  | refl => exact step
  | step first rest ih => cases first; exact .tRec (ih step normal)

/-- An output step at a well-formed source is a base encoder step. -/
theorem base_of_st_out_co {T U : SessionType} {p l s : String}
    (wf : T.WellFormed) (step : st_trans T (.out p l s) U) :
    mon_tr_yes_base T (.send p l s) U := by
  obtain ⟨H, head, direct⟩ := st_trans_hnf_co step
  cases direct with
  | intC member => exact base_of_hnf head ⟨(hnf_wf_co wf head).1.triple_nodup_of_internalChoice, member⟩
  | tRec next => exact False.elim head.2

/-- Internal pruning inverts at an `internalChoice` head. -/
theorem Prune_int_inv_co {T R : SessionType} {bs : List (Role × Lab × DataSort × SessionType)}
    {q lab sv : String}
    (head : hnf T (.internalChoice bs)) (pruned : Prune (.recv q lab sv) T R) :
    ∃ kept, hnf R (.internalChoice kept) ∧
      (∀ p l s U, (p, l, s, U) ∈ bs → q ≠ p) ∧
      KRint (fun U => Ex U (.recv q lab sv)) (Prune (.recv q lab sv)) bs kept := by
  have step (n : Nat) : ∃ HR, hnf R HR ∧
      PfxStep (PruneN n (.recv q lab sv)) (.recv q lab sv) (.internalChoice bs) HR := by
    rcases pruned (n + 1) with ⟨U, base, _⟩ | ⟨H, HR, hT, hR, pfx⟩
    · obtain ⟨H, hH, direct⟩ := base_hnf base
      have same := hnf_unique hH head
      subst H
      exact False.elim direct
    · have same := hnf_unique hT head
      subst H
      exact ⟨HR, hR, pfx⟩
  obtain ⟨HR, hR, pfx⟩ := step 0
  cases HR <;> (simp only [PfxStep] at pfx; try contradiction)
  rename_i kept
  refine ⟨kept, hR, pfx.2.2.1, KRint_allDepths_co ?_⟩
  intro n
  obtain ⟨HR, hR', pfx'⟩ := step n
  have same := hnf_unique hR' hR
  subst HR
  exact pfx'.2.2.2

/-- Internal pruning inverts at an `externalChoice` head (non-matching owner). -/
theorem Prune_ext_inv_co {T R : SessionType} {bs : List (Lab × DataSort × SessionType)}
    {p q lab sv : String}
    (head : hnf T (.externalChoice p bs)) (apart : q ≠ p)
    (pruned : Prune (.recv q lab sv) T R) :
    ∃ kept, hnf R (.externalChoice p kept) ∧
      KRext (fun U => Ex U (.recv q lab sv)) (Prune (.recv q lab sv)) bs kept := by
  have step (n : Nat) : ∃ HR, hnf R HR ∧
      PfxStep (PruneN n (.recv q lab sv)) (.recv q lab sv) (.externalChoice p bs) HR := by
    rcases pruned (n + 1) with ⟨U, base, _⟩ | ⟨H, HR, hT, hR, pfx⟩
    · obtain ⟨H, hH, direct⟩ := base_hnf base
      have same := hnf_unique hH head
      subst H
      exact False.elim (apart direct.1.symm)
    · have same := hnf_unique hT head
      subst H
      exact ⟨HR, hR, pfx⟩
  obtain ⟨HR, hR, pfx⟩ := step 0
  cases HR <;> (simp only [PfxStep] at pfx; try contradiction)
  rename_i r kept
  obtain ⟨rfl, _, _, _, _⟩ := pfx
  refine ⟨kept, hR, KRext_allDepths_co ?_⟩
  intro n
  obtain ⟨HR, hR', pfx'⟩ := step n
  have same := hnf_unique hR' hR
  subst HR
  exact pfx'.2.2.2.2

/-- Pruning at a matching `externalChoice` head selects the branch target. -/
theorem Prune_ext_base_co {T R : SessionType} {bs : List (Lab × DataSort × SessionType)}
    {p lab sv : String}
    (head : hnf T (.externalChoice p bs)) (pruned : Prune (.recv p lab sv) T R) :
    ∃ U, (lab, sv, U) ∈ bs ∧ Eqv U R := by
  have step (n : Nat) : ∃ U, mon_tr_yes_base T (.recv p lab sv) U ∧ teqN (n + 1) U R := by
    rcases pruned (n + 1) with base | ⟨H, HR, hT, hR, pfx⟩
    · exact base
    · have same := hnf_unique hT head
      subst H
      cases HR <;> (simp only [PfxStep] at pfx; try contradiction)
      exact False.elim (pfx.2.1 rfl)
  obtain ⟨U, base, _⟩ := step 0
  refine ⟨U, ?_, ?_⟩
  · obtain ⟨H, hH, direct⟩ := base_hnf base
    have same := hnf_unique hH head
    subst H
    exact direct.2.2
  · intro n
    cases n with
    | zero => trivial
    | succ n =>
        obtain ⟨V, base', same⟩ := step n
        have eq := mon_tr_yes_base_target_unique base' base
        subst V
        exact same

/-- The fold respects source equivalence. -/
theorem SemFoldCo_eqv_src {Q : Queue} {T U M : SessionType}
    (wt : T.WellFormed) (wu : U.WellFormed) (same : Eqv T U) (fold : SemFoldCo T Q M) :
    SemFoldCo U Q M := by
  cases Q with
  | nil => exact ⟨Eqv_trans fold.1 same, fold.2⟩
  | cons msg Q => obtain ⟨V, wv, pu, ru⟩ := fold; exact ⟨V, wv, Prune_eqv_l_co same wt wu pu, ru⟩

/-- The fold respects target equivalence. -/
theorem SemFoldCo_eqv_tgt {Q : Queue} {T M M' : SessionType}
    (fold : SemFoldCo T Q M) (same : Eqv M M') (wf : M'.WellFormed) : SemFoldCo T Q M' := by
  induction Q generalizing T with
  | nil => exact ⟨Eqv_trans (Eqv_sym same) fold.1, wf⟩
  | cons msg Q ih => obtain ⟨V, wv, pu, ru⟩ := fold; exact ⟨V, wv, pu, ih ru⟩

/-- Folds of one queue are unique up to equivalence. -/
theorem SemFoldCo_unique {Q : Queue} {T M M' : SessionType}
    (wf : T.WellFormed) (first : SemFoldCo T Q M) (second : SemFoldCo T Q M') : Eqv M M' := by
  induction Q generalizing T with
  | nil => exact Eqv_trans first.1 (Eqv_sym second.1)
  | cons msg Q ih =>
      obtain ⟨U, wu, pu, ru⟩ := first
      obtain ⟨V, wv, pv, rv⟩ := second
      exact ih wu ru (SemFoldCo_eqv_src wv wu (Prune_unique wf pv pu) rv)

/-- Folding an appended message observes the folded state. -/
theorem SemFoldCo_snoc {Q : Queue} {T X M : SessionType} {p l s : String}
    (wt : T.WellFormed) (fold : SemFoldCo T Q X) (pruned : Prune (.recv p l s) X M)
    (wm : M.WellFormed) : SemFoldCo T (Q ++ [.msg p l s]) M := by
  induction Q generalizing T with
  | nil => exact ⟨M, wm, Prune_eqv_l_co fold.1 fold.2 wt pruned, Eqv_refl wm, wm⟩
  | cons msg Q ih => obtain ⟨U, wu, pu, ru⟩ := fold; exact ⟨U, wu, pu, ih wu ru⟩

/-- An appended-message fold splits off the last observation. -/
theorem SemFoldCo_snoc_inv {Q : Queue} {T M : SessionType} {p l s : String}
    (wt : T.WellFormed) (fold : SemFoldCo T (Q ++ [.msg p l s]) M) :
    ∃ X, X.WellFormed ∧ SemFoldCo T Q X ∧ Prune (.recv p l s) X M := by
  induction Q generalizing T with
  | nil =>
      obtain ⟨U, wu, pu, same, wm⟩ := fold
      exact ⟨T, wt, ⟨Eqv_refl wt, wt⟩, Prune_eqv_r pu (Eqv_sym same)⟩
  | cons msg Q ih =>
      obtain ⟨U, wu, pu, ru⟩ := fold
      obtain ⟨X, wx, fx, px⟩ := ih wu ru
      exact ⟨X, wx, ⟨U, wu, pu, fx⟩, px⟩

/-- A send step at the source replays at any folded state. -/
theorem SemFoldCo_send {Q : Queue} {T M T' : SessionType} {p l s : String}
    (wf : T.WellFormed) (fold : SemFoldCo T Q M) (step : st_trans T (.out p l s) T')
    (completion : ∃ M₁, SemFoldCo T' Q M₁) :
    ∃ M', mon_tr_yes_base M (.send p l s) M' ∧ SemFoldCo T' Q M' := by
  induction Q generalizing T T' with
  | nil =>
      obtain ⟨M', base, same⟩ := base_eqv_co (base_of_st_out_co wf step) (Eqv_sym fold.1)
      exact ⟨M', base, Eqv_sym same, mon_tr_yes_base_preserves_wf base fold.2⟩
  | cons msg Q ih =>
      obtain ⟨q, a, b⟩ := msg
      obtain ⟨U, wu, pu, ru⟩ := fold
      obtain ⟨H, head, direct⟩ := st_trans_hnf_co step
      cases direct with
      | tRec next => exact False.elim head.2
      | intC member =>
          obtain ⟨kept, hU, _, kr⟩ := Prune_int_inv_co head pu
          have wt' := SessionType.wellFormedPreserved T (.out p l s) T' wf step
          obtain ⟨M₁, X, wx, px, rx⟩ := completion
          obtain ⟨U', member', pu'⟩ := KRint_cover kr member (Ex_of_Prune wt' px)
          have stepU : st_trans U (.out p l s) U' := st_trans_of_hnf_co hU (.intC member')
          have wu' := SessionType.wellFormedPreserved U (.out p l s) U' wu stepU
          obtain ⟨M', base, rest⟩ := ih wu ru stepU
            ⟨M₁, SemFoldCo_eqv_src wx wu' (Prune_unique wt' px pu') rx⟩
          exact ⟨M', base, U', wu', pu', rest⟩

/-- Owner-presence: a folded queue with a pending message has the branch. -/
theorem SemFoldCo_owner_kept {seen : Queue} {T M : SessionType} {p l s : String}
    {bs : List (Lab × DataSort × SessionType)} {left : Queue} (wt : T.WellFormed)
    (head : hnf T (.externalChoice p bs)) (fresh : ∀ m ∈ seen, m.1 ≠ p)
    (fold : SemFoldCo T (seen ++ [.msg p l s] ++ left) M) : ∃ U, (l, s, U) ∈ bs := by
  induction seen generalizing T bs with
  | nil =>
      obtain ⟨U, _, pruned, _⟩ := fold
      obtain ⟨V, member, _⟩ := Prune_ext_base_co head pruned
      exact ⟨V, member⟩
  | cons msg seen ih =>
      obtain ⟨q, a, b⟩ := msg
      obtain ⟨U, wu, pruned, rest⟩ := fold
      obtain ⟨kept, hU, kr⟩ := Prune_ext_inv_co head (fresh _ List.mem_cons_self) pruned
      obtain ⟨V, member⟩ := ih wu hU (fun m member => fresh m (List.mem_cons_of_mem _ member)) rest
      obtain ⟨W, member, _, _⟩ := KRext_kept_mem kr member
      exact ⟨W, member⟩

/-- Dequeue advances the source past a pending message. -/
theorem SemFoldCo_dequeue_split {seen : Queue} {T M T' : SessionType} {p l s : String}
    {left : Queue} (wt : T.WellFormed) (fresh : ∀ m ∈ seen, m.1 ≠ p)
    (step : st_trans T (.inp p l s) T') (fold : SemFoldCo T (seen ++ [.msg p l s] ++ left) M) :
    SemFoldCo T' (seen ++ left) M := by
  induction seen generalizing T T' with
  | nil =>
      obtain ⟨U, wu, pruned, rest⟩ := fold
      have wt' := SessionType.wellFormedPreserved T (.inp p l s) T' wt step
      exact SemFoldCo_eqv_src wu wt'
        (Prune_unique wt pruned (Prune_base_co (st_trans_inp_imp_mon_tr_yes_base step wt) wt')) rest
  | cons msg seen ih =>
      obtain ⟨q, a, b⟩ := msg
      obtain ⟨W, ww, pw, rw⟩ := fold
      obtain ⟨H, head, direct⟩ := st_trans_hnf_co step
      cases direct with
      | tRec next => exact False.elim head.2
      | extC member =>
          obtain ⟨kept, hW, kr⟩ := Prune_ext_inv_co head (fresh _ List.mem_cons_self) pw
          have fresh' := fun m member => fresh m (List.mem_cons_of_mem _ member)
          obtain ⟨W', member'⟩ := SemFoldCo_owner_kept ww hW fresh' rw
          obtain ⟨T₀, member₀, _, pruned⟩ := KRext_kept_mem kr member'
          have wtH := hnf_wf_co wt head
          have eq : T₀ = T' := Drainability.ext_target_unique wtH.1 member₀ member
          subst T₀
          have stepW : st_trans W (.inp p l s) W' := st_trans_of_hnf_co hW (.extC member')
          exact ⟨W', SessionType.wellFormedPreserved W (.inp p l s) W' ww stepW,
            pruned, ih ww fresh' stepW rw⟩

/-- Dequeue (`sq_trans.dequeue`) preserves the fold. -/
theorem SemFoldCo_dequeue {T M T' : SessionType} {Q Q' : Queue} {p l s : String}
    (wt : T.WellFormed) (fold : SemFoldCo T Q M)
    (step : sq_trans (T, Q) (.dequeue p l s) (T', Q')) : SemFoldCo T' Q' M := by
  cases step with
  | dequeue st queue =>
      obtain ⟨seen, left, rfl, rfl, fresh⟩ := queue_dequeue_some_iff queue
      exact SemFoldCo_dequeue_split wt fresh st fold

-- ================================================================
-- Drainage interface (ported; see header for credit).
-- `Can` is `Drainability.CanAlwaysDrainInternalDeepRec`.
-- ================================================================

abbrev CanCo := Drainability.CanAlwaysDrainInternalDeepRec

/-- Unfolding lifts drainability. -/
theorem CanCo_unfoldstar_lift {T H : SessionType} {Q : Queue}
    (steps : UnfoldStar T H) (drain : CanCo H Q) : CanCo T Q := by
  cases Q with
  | nil => exact .drained_nil _
  | cons msg Q =>
      induction steps with
      | refl => exact drain
      | step first rest ih => cases first; exact .trec_step _ _ _ (by simp) (ih drain)

/-- Drainability respects source equivalence. -/
theorem CanCo_eqv {T U : SessionType} {Q : Queue} (drain : CanCo T Q)
    (same : Eqv T U) (wt : T.WellFormed) (wu : U.WellFormed) : CanCo U Q := by
  induction drain generalizing U with
  | drained_nil => exact .drained_nil _
  | intC_drain bs Q fresh all ih =>
      obtain ⟨H, head⟩ := hnf_exists_co wu
      have wh := hnf_wf_co wu head
      have shape := Eqv_shape same (hnf_self trivial) head
      cases H <;> (simp only [shapeEq] at shape; try contradiction)
      apply CanCo_unfoldstar_lift head.1
      apply Drainability.CanAlwaysDrainInternalDeepRec.intC_drain
      · intro p l s V member
        obtain ⟨W, memberW, _⟩ := alignInt_mem_r_co shape member
        exact fresh p l s W memberW
      · intro b member
        obtain ⟨p, l, s, V⟩ := b
        obtain ⟨W, memberW, eq⟩ := alignInt_mem_r_co shape member
        exact ih _ memberW eq (wf_of_mem_int wt memberW) (wf_of_mem_int wh member)
  | extC_spec p bs Q fresh b member drain ih =>
      obtain ⟨l, s, T⟩ := b
      obtain ⟨H, head⟩ := hnf_exists_co wu
      have wh := hnf_wf_co wu head
      have shape := Eqv_shape same (hnf_self trivial) head
      cases H <;> (simp only [shapeEq] at shape; try contradiction)
      obtain ⟨rfl, shape⟩ := shape
      obtain ⟨V, memberV, eq⟩ := alignExt_mem shape member
      exact CanCo_unfoldstar_lift head.1 (.extC_spec _ _ _ fresh _ memberV
        (ih eq (wf_of_mem_ext wt member) (wf_of_mem_ext wh memberV)))
  | extC_deq p bs Q Q' l s T member queue drain ih =>
      obtain ⟨H, head⟩ := hnf_exists_co wu
      have wh := hnf_wf_co wu head
      have shape := Eqv_shape same (hnf_self trivial) head
      cases H <;> (simp only [shapeEq] at shape; try contradiction)
      obtain ⟨rfl, shape⟩ := shape
      obtain ⟨V, memberV, eq⟩ := alignExt_mem shape member
      exact CanCo_unfoldstar_lift head.1 (.extC_deq _ _ _ _ _ _ _ memberV queue
        (ih eq (wf_of_mem_ext wt member) (wf_of_mem_ext wh memberV)))
  | trec_step X B Q nonempty drain ih =>
      exact ih (fun n => (teqN_unfold_l n).mp (same n))
        (SessionType.wellFormedUnfold wt (.step .tRec (.refl _))) wu

/-- A dequeue step splits into head-hit or blocking-prefix cases. -/
theorem dequeue_cons_co {m x : QueueMessage} {Q Q' : Queue}
    (dequeue : Queue.dequeue (m :: Q) x = some Q') :
    (m = x ∧ Q' = Q) ∨ (m.1 ≠ x.1 ∧ ∃ R, Q.dequeue x = some R ∧ Q' = m :: R) := by
  obtain ⟨seen, left, split, residual, fresh⟩ := queue_dequeue_some_iff dequeue
  cases seen with
  | nil =>
      simp only [List.nil_append, List.singleton_append, List.cons.injEq] at split residual
      obtain ⟨rfl, rfl⟩ := split
      exact .inl ⟨rfl, residual⟩
  | cons head seen =>
      simp only [List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      refine .inr ⟨fresh _ List.mem_cons_self, seen ++ left, ?_, ?_⟩
      · obtain ⟨p, l, s⟩ := x
        simpa [Queue.dequeue] using Drainability.dequeue_skip_seen (p := p) (lab := l) (S := s) (rest := left) (acc := []) (fun x hx => fresh x (List.mem_cons_of_mem _ hx))
      · simpa using residual

/-- Drainability of a non-empty queue yields `Ex` at the head. -/
theorem CanCo_Ex {T : SessionType} {Q : Queue} (drain : CanCo T Q) (wt : T.WellFormed)
    {p l s : String} {tail : Queue} (head : Q = .msg p l s :: tail) : Ex T (.recv p l s) := by
  induction drain generalizing p l s tail with
  | drained_nil => simp at head
  | intC_drain bs Q fresh all ih =>
      subst Q
      obtain ⟨⟨q, a, b, U⟩, member⟩ := List.exists_mem_of_ne_nil _ wt.1.ne_of_internalChoice
      exact Ex_int_single wt (fun q a b U member => fresh q a b U member _ List.mem_cons_self)
        member (ih _ member (wf_of_mem_int wt member) rfl)
  | extC_spec q bs Q fresh b member drain ih =>
      subst Q
      obtain ⟨a, b, U⟩ := b
      exact Ex_ext_single wt (fresh _ List.mem_cons_self) member
        (ih (wf_of_mem_ext wt member) rfl)
  | extC_deq q bs Q Q' a b U member queue drain ih =>
      subst Q
      rcases dequeue_cons_co queue with ⟨eq, rfl⟩ | ⟨apart, R, queue', rfl⟩
      · cases eq
        have unique : (bs.map fun b => (b.1, b.2.1)).Nodup := by
          cases wt.1 with | externalChoice unique _ _ => exact nodup_of_nodup_labels unique
        exact ⟨U, .base (.extC unique member)⟩
      · exact Ex_ext_single wt apart member (ih (wf_of_mem_ext wt member) rfl)
  | trec_step X B Q nonempty drain ih =>
      obtain ⟨V, accepted⟩ := ih (SessionType.wellFormedUnfold wt (.step .tRec (.refl _))) head
      exact ⟨V, .unfold accepted⟩

/-- Pruning preserves drainability of the tail. -/
theorem CanCo_after_prune {T : SessionType} {Q : Queue} (drain : CanCo T Q) (wt : T.WellFormed)
    {p l s : String} {tail : Queue} {U : SessionType} (head : Q = .msg p l s :: tail)
    (pruned : Prune (.recv p l s) T U) (wu : U.WellFormed) : CanCo U tail := by
  induction drain generalizing p l s tail U with
  | drained_nil => simp at head
  | intC_drain bs Q fresh all ih =>
      subst Q
      obtain ⟨kept, headU, _, kr⟩ := Prune_int_inv_co (hnf_self trivial) pruned
      have wh := hnf_wf_co wu headU
      apply CanCo_unfoldstar_lift headU.1
      apply Drainability.CanAlwaysDrainInternalDeepRec.intC_drain
      · intro q a b V member m hm
        obtain ⟨W, memberW, _, _⟩ := KRint_kept_mem kr member
        exact fresh q a b W memberW m (List.mem_cons_of_mem _ hm)
      · intro b member
        obtain ⟨q, a, b, V⟩ := b
        obtain ⟨W, memberW, _, pruned⟩ := KRint_kept_mem kr member
        exact ih _ memberW (wf_of_mem_int wt memberW) rfl pruned
          (wf_of_mem_int wh member)
  | extC_spec q bs Q fresh b member drain ih =>
      subst Q
      obtain ⟨a, b, T⟩ := b
      obtain ⟨kept, headU, kr⟩ := Prune_ext_inv_co (hnf_self trivial) (fresh _ List.mem_cons_self) pruned
      have wh := hnf_wf_co wu headU
      obtain ⟨V, memberV, pv⟩ := KRext_cover kr member (CanCo_Ex drain (wf_of_mem_ext wt member) rfl)
      exact CanCo_unfoldstar_lift headU.1 (.extC_spec _ _ _
        (fun m hm => fresh m (List.mem_cons_of_mem _ hm)) _ memberV
        (ih (wf_of_mem_ext wt member) rfl pv (wf_of_mem_ext wh memberV)))
  | extC_deq q bs Q Q' a b T member queue drain ih =>
      subst Q
      rcases dequeue_cons_co queue with ⟨eq, rfl⟩ | ⟨apart, R, queue', rfl⟩
      · cases eq
        obtain ⟨V, memberV, eq⟩ := Prune_ext_base_co (hnf_self trivial) pruned
        have same : V = T := Drainability.ext_target_unique wt.1 memberV member
        subst V
        exact CanCo_eqv drain eq (wf_of_mem_ext wt member) wu
      · obtain ⟨kept, headU, kr⟩ := Prune_ext_inv_co (hnf_self trivial) apart pruned
        have wh := hnf_wf_co wu headU
        obtain ⟨V, memberV, pv⟩ := KRext_cover kr member (CanCo_Ex drain (wf_of_mem_ext wt member) rfl)
        exact CanCo_unfoldstar_lift headU.1 (.extC_deq _ _ _ _ _ _ _ memberV queue'
          (ih (wf_of_mem_ext wt member) rfl pv (wf_of_mem_ext wh memberV)))
  | trec_step X B Q nonempty drain ih =>
      exact ih (SessionType.wellFormedUnfold wt (.step .tRec (.refl _))) head
        (fun n => (PruneN_unfold_l n).mp (pruned n)) wu

-- ================================================================
-- Queue runs and the monitor invariant (ported; see header).
-- ================================================================

/-- A queue run folds `Q` into `M` through one Fold step per message. -/
def QueueRunCo (accept : SessionType → ext_tag → SessionType → Prop) :
    SessionType → Queue → SessionType → Prop
  | T, [], M => M = T
  | T, .msg p l s :: Q, M => ∃ U, accept T (.recv p l s) U ∧ QueueRunCo accept U Q M

/-- A `Co` queue run is a semantic fold (targets via the functional pipeline). -/
theorem QueueRunCo_sem {Q : Queue} {T M : SessionType} (wf : T.WellFormed)
    (run : QueueRunCo (fun T g U => fmon [] T g U) T Q M) : SemFoldCo T Q M := by
  induction Q generalizing T with
  | nil => subst M; exact ⟨Eqv_refl wf, wf⟩
  | cons msg Q ih =>
      obtain ⟨U, accepted, rest⟩ := run
      have wu := fmon_preserves_wf wf accepted
      exact ⟨U, wu, fmon_spec wf accepted, ih wu rest⟩

/-- Existential acceptance yields a finite Fold derivation.
Instantiates `fmon_exists` (conclusion restated with `fmon []` since
`Nest`'s `mon_tr_yes` is the finite maximal relation).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
private theorem accepted_exists_co {T : SessionType} {g : ext_tag}
    (wf : T.WellFormed) (eligible : Ex T g) : ∃ U, fmon [] T g U :=
  fmon_exists wf eligible

/-- Drainability yields a queue run. -/
theorem QueueRunCo_exists_of_Can {Q : Queue} {T : SessionType}
    (wf : T.WellFormed) (drain : CanCo T Q) : ∃ M, QueueRunCo (fun T g U => fmon [] T g U) T Q M := by
  induction Q generalizing T with
  | nil => exact ⟨T, rfl⟩
  | cons msg Q ih =>
      obtain ⟨p, l, s⟩ := msg
      obtain ⟨U, accepted⟩ := accepted_exists_co wf (CanCo_Ex drain wf rfl)
      have wu := fmon_preserves_wf wf accepted
      obtain ⟨M, rest⟩ := ih wu (CanCo_after_prune drain wf rfl (fmon_spec wf accepted) wu)
      exact ⟨M, U, accepted, rest⟩

/-- Drainability yields a semantic fold. -/
theorem SemFoldCo_exists_of_Can {Q : Queue} {T : SessionType}
    (wf : T.WellFormed) (drain : CanCo T Q) : ∃ M, SemFoldCo T Q M := by
  obtain ⟨M, run⟩ := QueueRunCo_exists_of_Can wf drain
  exact ⟨M, QueueRunCo_sem wf run⟩

/-- Any accepted step at a folded state extends the fold over an appended message. -/
theorem SemFoldCo_recv_any {T M M' : SessionType} {Q : Queue} {p l s : String}
    (wf : T.WellFormed) (fold : SemFoldCo T Q M) (accepted : fmon [] M (.recv p l s) M') :
    SemFoldCo T (Q ++ [.msg p l s]) M' :=
  SemFoldCo_snoc wf fold (fmon_spec (SemFoldCo_wf fold) accepted)
    (fmon_preserves_wf (SemFoldCo_wf fold) accepted)

/-- A completed fold over an appended message factors through a Fold step. -/
theorem SemFoldCo_recv_accept {T M M₁ : SessionType} {Q : Queue} {p l s : String}
    (wf : T.WellFormed) (fold : SemFoldCo T Q M) (completion : SemFoldCo T (Q ++ [.msg p l s]) M₁) :
    ∃ M', fmon [] M (.recv p l s) M' ∧ SemFoldCo T (Q ++ [.msg p l s]) M' := by
  obtain ⟨X, wx, fx, px⟩ := SemFoldCo_snoc_inv wf completion
  have wm := SemFoldCo_wf fold
  have same := SemFoldCo_unique wf fold fx
  have eligible := Ex_of_Prune wm (Prune_eqv_l_co (Eqv_sym same) wx wm px)
  obtain ⟨M', accepted⟩ := accepted_exists_co wm eligible
  exact ⟨M', accepted, SemFoldCo_recv_any wf fold accepted⟩

/-- A completed `T'`-fold replays a source send at the folded state. -/
theorem SemFoldCo_send_any {T T' M M' : SessionType} {Q : Queue} {p l s : String}
    (wf : T.WellFormed) (fold : SemFoldCo T Q M) (step : st_trans T (.out p l s) T')
    (completion : ∃ M₁, SemFoldCo T' Q M₁) (accepted : fmon [] M (.send p l s) M') :
    SemFoldCo T' Q M' := by
  obtain ⟨Mc, base, fc⟩ := SemFoldCo_send wf fold step completion
  have wm := SemFoldCo_wf fold
  exact SemFoldCo_eqv_tgt fc
    (Prune_unique wm (Prune_base_co base (mon_tr_yes_base_preserves_wf base wm)) (fmon_spec wm accepted))
    (fmon_preserves_wf wm accepted)

/-- A relational coinductive queue fold is a semantic fold.
    The co-step already carries its target well-formedness, so the
    construction is direct (no existential choice). -/
theorem fold_co_to_SemFoldCo {Q : Queue} {T M : SessionType} (hT : T.WellFormed)
    (h : monitor_fold_co (T, Q) M) : SemFoldCo T Q M := by
  induction Q generalizing T M with
  | nil =>
    simp only [monitor_fold_co, monitor_fold_aux_co] at h
    subst h
    exact ⟨Eqv_refl hT, hT⟩
  | cons msg Q ih =>
    rcases msg with ⟨p, lab, S⟩
    simp only [monitor_fold_co, monitor_fold_aux_co] at h
    obtain ⟨T_mid, _hT, hM, hco, hRest⟩ := h
    exact ⟨T_mid, hM, co_implies_Prune hT hM hco, ih hM hRest⟩
