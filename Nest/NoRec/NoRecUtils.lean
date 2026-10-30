import Nest.SessionUtils

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# NoRecUtils: `LeadsTo` path utilities and graft chains for the NoRec development.

Relocated verbatim from `Nest/SessionUtils.lean`: these declarations are
unused toward the five monitor-correctness roots
(`monitor_soundness_norec`, `monitor_soundness`,
`monitor_soundness_co`, `mon_tr_yes_co_fun_sound`,
`mon_tr_yes_co_fun_complete`) but are used under `Nest/NoRec`
(`NoRecEncoder`, `NoRecToolkit`).
They live here — under `Nest/NoRec`, distinct from core
`Nest/SessionUtils.lean` — so those files keep compiling.
-/

/-- A free variable occurs in some internal branch target. -/
private theorem fv_goInt_exists_mem {l : List (Role × Lab × DataSort × SessionType)}
    {X : String} (h : X ∈ SessionType.fv.goInt l) :
    ∃ (p : Role) (lab : Lab) (S : DataSort) (T0 : SessionType),
      ((p, lab, S, T0) ∈ l) ∧ X ∈ T0.fv := by
  induction l with
  | nil => simp [SessionType.fv.goInt] at h
  | cons hd tl ih =>
    rcases hd with ⟨q0, l0, s0, T0⟩
    simp only [SessionType.fv.goInt, List.mem_append] at h
    rcases h with h | h
    · exact ⟨q0, l0, s0, T0, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨p, lab, S, T0', h1, h2⟩ := ih h
      exact ⟨p, lab, S, T0', List.mem_cons.mpr (Or.inr h1), h2⟩

/-- A free variable occurs in some external branch target. -/
private theorem fv_goExt_exists_mem {l : List (Lab × DataSort × SessionType)}
    {X : String} (h : X ∈ SessionType.fv.goExt l) :
    ∃ (lab : Lab) (S : DataSort) (T0 : SessionType),
      ((lab, S, T0) ∈ l) ∧ X ∈ T0.fv := by
  induction l with
  | nil => simp [SessionType.fv.goExt] at h
  | cons hd tl ih =>
    rcases hd with ⟨l0, s0, T0⟩
    simp only [SessionType.fv.goExt, List.mem_append] at h
    rcases h with h | h
    · exact ⟨l0, s0, T0, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨lab, S, T0', h1, h2⟩ := ih h
      exact ⟨lab, S, T0', List.mem_cons.mpr (Or.inr h1), h2⟩

/-- Every free variable is the endpoint of a `LeadsTo` path (shadowed
    binders excluded by construction: the `tRec` case extracts `X ≠ Y`
    from filter-membership). Path machinery for the adequacy regress:
    free `X`-leaves mark graft sites, and `LeadsTo` paths replay through
    derivations. By size induction. -/
theorem SessionType.LeadsTo_of_mem_fv {X : String} {B : SessionType}
    (hmem : X ∈ B.fv) : ∃ Ss : List Role, SessionType.LeadsTo X B Ss := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop :=
    fun U => X ∈ U.fv → ∃ Ss : List Role, SessionType.LeadsTo X U Ss
  have hC : ∀ U, C U := by
    intro U
    refine hwf.induction (α := SessionType) (C := C) (a := U) ?step
    intro U ih hmem
    cases U with
    | tEnd => simp [SessionType.fv] at hmem
    | tVar Y =>
      have hXY : X = Y := by
        simpa [SessionType.fv] using hmem
      subst hXY
      exact ⟨[], SessionType.LeadsTo.var⟩
    | internalChoice branches =>
      simp only [SessionType.fv] at hmem
      obtain ⟨q0, l0, s0, T0, hmemU, hfvU⟩ := fv_goInt_exists_mem hmem
      have hlt : sizeOf T0 < sizeOf (SessionType.internalChoice branches) :=
        sizeOf_SessionType_lt_sizeOf_internalChoice hmemU
      obtain ⟨Ss, hpath⟩ := ih T0 hlt hfvU
      exact ⟨Ss, SessionType.LeadsTo.intC hmemU hpath⟩
    | externalChoice q branches =>
      simp only [SessionType.fv] at hmem
      obtain ⟨l0, s0, T0, hmemU, hfvU⟩ := fv_goExt_exists_mem hmem
      have hlt : sizeOf T0 < sizeOf (SessionType.externalChoice q branches) :=
        sizeOf_SessionType_lt_sizeOf_externalChoice (p := q) hmemU
      obtain ⟨Ss, hpath⟩ := ih T0 hlt hfvU
      exact ⟨q :: Ss, SessionType.LeadsTo.extC hmemU hpath⟩
    | tRec Y B =>
      simp only [SessionType.fv, List.mem_filter] at hmem
      obtain ⟨hmemB, hne⟩ := hmem
      have hneY : Y ≠ X := by
        intro hcon
        subst hcon
        simpa using hne
      have hlt : sizeOf B < sizeOf (SessionType.tRec Y B) := by simp
      obtain ⟨Ss, hpath⟩ := ih B hlt hmemB
      exact ⟨Ss, SessionType.LeadsTo.trec hneY hpath⟩
  exact hC B hmem

-- ================================================================
-- `LeadsTo` utilities moved from `Nest/SessionSyntax.lean` and
-- `Nest/SessionLTS.lean`: unneeded by the five monitor-correctness roots
-- but used under `Nest/NoRec`.
-- ================================================================

/-- Membership in `fv.goInt`: if a branch target contains `Y`, so does the whole list. -/
private theorem fv_goInt_mem {l : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} {T0 : SessionType} {Y : String}
    (hmem : (p, lab, S, T0) ∈ l) (hY : Y ∈ T0.fv) :
    Y ∈ SessionType.fv.goInt l := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨p', lab', S', T'⟩
    simp [SessionType.fv.goInt]
    simp at hmem
    rcases hmem with h | h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Or.inl hY
    · exact Or.inr (ih h)

/-- Membership in `fv.goExt`: if a branch target contains `Y`, so does the whole list. -/
private theorem fv_goExt_mem {l : List (Lab × DataSort × SessionType)}
    {lab : Lab} {S : DataSort} {T0 : SessionType} {Y : String}
    (hmem : (lab, S, T0) ∈ l) (hY : Y ∈ T0.fv) :
    Y ∈ SessionType.fv.goExt l := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨lab', S', T'⟩
    simp [SessionType.fv.goExt]
    simp at hmem
    rcases hmem with h | h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl hY
    · exact Or.inr (ih h)

/-- A `LeadsTo` path to `X` witnesses `X ∈ fv`. -/
theorem SessionType.LeadsTo_fv {X : String} {T : SessionType} {Ss : List Role}
    (h : SessionType.LeadsTo X T Ss) : X ∈ T.fv := by
  induction h with
  | var => simp [SessionType.fv]
  | intC hmem _ ih =>
    simp only [SessionType.fv]
    exact fv_goInt_mem hmem ih
  | extC hmem _ ih =>
    simp only [SessionType.fv]
    exact fv_goExt_mem hmem ih
  | trec hne _ ih =>
    simp only [SessionType.fv]
    rw [List.mem_filter]
    constructor
    · exact ih
    · have hne' : ¬ X = _ := Ne.symm hne
      cases hb : X == _ with
      | true =>
        exfalso
        exact hne' (beq_iff_eq.mp hb)
      | false =>
        simpa using hne'

/-- Closed types admit no `LeadsTo` paths. -/
theorem SessionType.LeadsTo_of_closed {T : SessionType} (hCl : T.IsClosed)
    {X : String} {Ss : List Role} (h : SessionType.LeadsTo X T Ss) : False := by
  have hmem := SessionType.LeadsTo_fv h
  unfold SessionType.IsClosed at hCl
  rw [hCl] at hmem
  exact List.not_mem_nil hmem

/-- `LeadsTo` for `Y ≠ X` in a substitution with closed `R` comes from the
    original body (closed `R` contributes no `LeadsTo` paths). By size induction
    (`sizeOf`), following `occurs_of_subst`: branch targets use `ih` with
    `sizeOf_...` bounds; `tVar X` grafts are impossible since `R` is closed. -/
theorem SessionType.LeadsTo_subst_inv_of_closed {Y X : String} (B : SessionType)
    {Ss : List Role} {R : SessionType} (hR : R.IsClosed) (hne : Y ≠ X)
    (h : SessionType.LeadsTo Y (substSessionType B X R) Ss) :
    SessionType.LeadsTo Y B Ss := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop := fun B =>
    ∀ Ss : List Role, SessionType.LeadsTo Y (substSessionType B X R) Ss →
      SessionType.LeadsTo Y B Ss
  have hC : ∀ B, C B := by
    intro B
    refine hwf.induction (α := SessionType) (C := C) (a := B) ?step
    intro B ih Ss h
    cases B with
    | tEnd =>
      simp only [substSessionType] at h
      cases h
    | tVar W =>
      by_cases heq : X = W
      · subst heq
        simp [substSessionType] at h
        exact (SessionType.LeadsTo_of_closed hR h).elim
      · simp [substSessionType, heq] at h
        cases h with
        | var => exact SessionType.LeadsTo.var
    | internalChoice branches =>
      simp only [substSessionType, go_int_eq_map] at h
      cases h with
      | intC hmem hsub =>
        rw [List.mem_map] at hmem
        obtain ⟨⟨p0, lab0, S0, T0⟩, hmemB, heqT⟩ := hmem
        cases heqT
        have hlt : sizeOf T0 < sizeOf (SessionType.internalChoice branches) :=
          sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
        have hL := ih T0 hlt Ss hsub
        exact SessionType.LeadsTo.intC hmemB hL
    | externalChoice p branches =>
      simp only [substSessionType, go_ext_eq_map] at h
      cases h with
      | extC hmem hsub =>
        rw [List.mem_map] at hmem
        obtain ⟨⟨lab0, S0, T0⟩, hmemB, heqT⟩ := hmem
        cases heqT
        have hlt : sizeOf T0 < sizeOf (SessionType.externalChoice p branches) :=
          sizeOf_SessionType_lt_sizeOf_externalChoice hmemB
        have hL := ih T0 hlt _ hsub
        exact SessionType.LeadsTo.extC hmemB hL
    | tRec Y0 B' =>
      by_cases heq : X = Y0
      · simp [substSessionType, heq] at h
        cases h with
        | trec hne0 h' => exact SessionType.LeadsTo.trec hne0 h'
      · simp [substSessionType, heq] at h
        cases h with
        | trec hne0 h' =>
          have hlt : sizeOf B' < sizeOf (SessionType.tRec Y0 B') := by simp
          have hL := ih B' hlt _ h'
          exact SessionType.LeadsTo.trec hne0 hL
  exact hC B Ss h

/-- Graft chains: iterated substitution as data (outermost graft first).
    Nested-subst semantics by construction. Regress machinery: replaying a
    `LeadsTo` path in a derivation accumulates grafts here (one per
    `trec_yes` premise entered); closed replacers keep grafted copies
    verbatim. -/
def graftFold : List (String × SessionType) → SessionType → SessionType
  | [], T => T
  | (Z, U) :: G, T => graftFold G (substSessionType T Z U)
