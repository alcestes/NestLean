import Nest.SessionSyntax

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# SessionLTS: Session-type LTS (without queues).

Single-session operational semantics: `st_label`/`st_trans` step relation and its
basic metatheory (exclusion, sender occurrence, substitution interaction).
-/

-- ================================================================
-- Session type LTS (without queues)
-- ================================================================

/-- Labels α ::= p ⊕ lab (S)  |  p & lab (S)  (S-IntC, S-ExtC) -/
inductive st_label : Type where
  | out : Role → Lab → DataSort → st_label
  | inp : Role → Lab → DataSort → st_label
  /-- Silent unfold: `over_trans.tauUnfold` only (never produced by `st_trans`,
      never observed by monitors). -/
  | tau : st_label
  deriving DecidableEq

/-- Transition relation for session types (without queues).
    Rules: S-IntC, S-ExtC, S-Rec. -/
inductive st_trans : SessionType → st_label → SessionType → Prop where
  | intC {branches : List (Role × Lab × DataSort × SessionType)}
      {p : Role} {lab : Lab} {S : DataSort} {T : SessionType}
      (h : (p, lab, S, T) ∈ branches) :
    st_trans (SessionType.internalChoice branches) (st_label.out p lab S) T
  | extC {branches : List (Lab × DataSort × SessionType)}
      {p : Role} {lab : Lab} {S : DataSort} {T : SessionType}
      (h : (lab, S, T) ∈ branches) :
    st_trans (SessionType.externalChoice p branches) (st_label.inp p lab S) T
  | tRec {X : String} {T T' : SessionType} {α : st_label}
      (h : st_trans (substSessionType T X (SessionType.tRec X T)) α T') :
    st_trans (SessionType.tRec X T) α T'

/-- Branch targets of an internal choice are strict subterms (their `sizeOf` is smaller). -/
lemma sizeOf_SessionType_lt_sizeOf_internalChoice {branches : List (Role × Lab × DataSort × SessionType)}
    {r : Role} {lab : Lab} {S : DataSort} {T0 : SessionType} (h : (r, lab, S, T0) ∈ branches) :
    sizeOf T0 < sizeOf (SessionType.internalChoice branches) := by
  have hsize1 : sizeOf T0 < sizeOf ((r : Role), (lab : Lab), (S : DataSort), (T0 : SessionType)) := by
    simp; omega
  have hsize2 : sizeOf ((r : Role), (lab : Lab), (S : DataSort), (T0 : SessionType)) < sizeOf branches :=
    List.sizeOf_lt_of_mem h
  have hsize3 : sizeOf branches < sizeOf (SessionType.internalChoice branches) := by
    simp
  exact Nat.lt_trans (Nat.lt_trans hsize1 hsize2) hsize3

/-- Branch targets of an external choice are strict subterms (their `sizeOf` is smaller). -/
lemma sizeOf_SessionType_lt_sizeOf_externalChoice {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {lab : Lab} {S : DataSort} {T0 : SessionType} (h : (lab, S, T0) ∈ branches) :
    sizeOf T0 < sizeOf (SessionType.externalChoice p branches) := by
  have hsize1 : sizeOf T0 < sizeOf ((lab : Lab), (S : DataSort), (T0 : SessionType)) := by
    simp; omega
  have hsize2 : sizeOf ((lab : Lab), (S : DataSort), (T0 : SessionType)) < sizeOf branches :=
    List.sizeOf_lt_of_mem h
  have hsize3 : sizeOf branches < sizeOf (SessionType.externalChoice p branches) := by
    simp
  exact Nat.lt_trans (Nat.lt_trans hsize1 hsize2) hsize3

/-- Occurrence through substitution: a role occurring in `B{X ↦ R}`
    occurs in `B` or in `R` (senders/owners are preserved by
    substitution; target occurrences push through branch targets or
    come from `R`; `tVar`/`tEnd` admit no occurrence). By size induction
    (`sizeOf`), since branch targets hide inside lists. -/
lemma occurs_of_subst {r : Role} {B : SessionType} {X : String} {R : SessionType}
    (h : SessionType.Occurs r (substSessionType B X R)) :
    SessionType.Occurs r B ∨ SessionType.Occurs r R := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop := fun B => SessionType.Occurs r (substSessionType B X R) →
    SessionType.Occurs r B ∨ SessionType.Occurs r R
  have hC : ∀ B, C B := by
    intro B
    refine hwf.induction (α := SessionType) (C := C) (a := B) ?step
    intro B ih h
    cases B with
  | tEnd =>
    simp only [substSessionType] at h
    cases h
  | tVar Y =>
    by_cases heq : X = Y
    · simp [substSessionType, heq] at h
      exact Or.inr h
    · simp [substSessionType, heq] at h
      cases h
  | internalChoice branches =>
    simp only [substSessionType, go_int_eq_map] at h
    cases h with
    | intSender hmem heq =>
      rw [List.mem_map] at hmem
      obtain ⟨⟨p0, lab0, S0, T0⟩, hmemB, heqT⟩ := hmem
      cases heqT
      exact Or.inl (SessionType.Occurs.intSender hmemB heq)
    | intTarget hmem hsub =>
      rw [List.mem_map] at hmem
      obtain ⟨⟨p0, lab0, S0, T0⟩, hmemB, heqT⟩ := hmem
      cases heqT
      have hlt : sizeOf T0 < sizeOf (SessionType.internalChoice branches) :=
        sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
      rcases ih T0 hlt hsub with hL | hR
      · exact Or.inl (SessionType.Occurs.intTarget hmemB hL)
      · exact Or.inr hR
  | externalChoice p branches =>
    simp only [substSessionType, go_ext_eq_map] at h
    cases h with
    | extOwner heq =>
      exact Or.inl (SessionType.Occurs.extOwner heq)
    | extTarget hmem hsub =>
      rw [List.mem_map] at hmem
      obtain ⟨⟨lab0, S0, T0⟩, hmemB, heqT⟩ := hmem
      cases heqT
      have hlt : sizeOf T0 < sizeOf (SessionType.externalChoice p branches) :=
        sizeOf_SessionType_lt_sizeOf_externalChoice hmemB
      rcases ih T0 hlt hsub with hL | hR
      · exact Or.inl (SessionType.Occurs.extTarget hmemB hL)
      · exact Or.inr hR
  | tRec Y B' =>
    by_cases heq : X = Y
    · simp [substSessionType, heq] at h
      exact Or.inl h
    · simp [substSessionType, heq] at h
      cases h with
      | recBody h' =>
        have hlt : sizeOf B' < sizeOf (SessionType.tRec Y B') := by simp
        rcases ih B' hlt h' with hL | hR
        · exact Or.inl (SessionType.Occurs.recBody hL)
        · exact Or.inr hR
  exact hC B h

/-- `st_trans` exclusivity core: a type stepping by `out` offers no `inp`
    (placed here for use by the round-robin scheduler). -/
lemma sttr_excl_aux : ∀ {T T' : SessionType} {α : st_label},
    st_trans T α T' →
    (∀ (p1 : Role) (lab1 : Lab) (S1 : DataSort) (p2 : Role) (lab2 : Lab) (S2 : DataSort)
      (T2 : SessionType),
      α = st_label.out p1 lab1 S1 → st_trans T (st_label.inp p2 lab2 S2) T2 → False) := by
  intro T T' α hST
  induction hST with
  | intC hmem =>
    intro p1 lab1 S1 p2 lab2 S2 T2 hEq hIn
    cases hIn
  | extC hmem =>
    intro p1 lab1 S1 p2 lab2 S2 T2 hEq hIn
    cases hEq
  | tRec hsub ih =>
    intro p1 lab1 S1 p2 lab2 S2 T2 hEq hIn
    match hIn with
    | st_trans.tRec hsub2 => exact ih p1 lab1 S1 p2 lab2 S2 T2 hEq hsub2

/-- A role offering `out` offers no `inp` (same-role lapse is impossible:
    a dequeue-pending role cannot lapse by sending and vice versa). -/
theorem sttr_out_not_inp {T T1 T2 : SessionType} {p1 : Role} {lab1 : Lab}
    {S1 : DataSort} {p2 : Role} {lab2 : Lab} {S2 : DataSort}
    (hOut : st_trans T (st_label.out p1 lab1 S1) T1)
    (hIn : st_trans T (st_label.inp p2 lab2 S2) T2) : False :=
  sttr_excl_aux hOut p1 lab1 S1 p2 lab2 S2 T2 rfl hIn

/-- Send-firing exhibits its sender in the source (`intC` by membership;
    `extC` pruned by tag, `tRec` through the unfolded derivation with the
    IH, closing via `occurs_of_subst`). -/
lemma st_trans_out_sender_occurs {T T' : SessionType} {r : Role} {lab : Lab}
    {S : DataSort} (hST : st_trans T (st_label.out r lab S) T') :
    T.Occurs r := by
  generalize hα : st_label.out r lab S = αs at hST
  induction hST with
  | intC hmem =>
    cases hα
    exact SessionType.Occurs.intSender hmem rfl
  | extC hmem =>
    cases hα
  | tRec hsub ih =>
    rcases occurs_of_subst (ih hα) with hL | hR
    · exact SessionType.Occurs.recBody hL
    · exact hR

/-- A send from a self-free entry goes elsewhere. -/
lemma out_ne_self_of_noSelf {q r : Role} {T T' : SessionType} {lab : Lab}
    {S : DataSort} (hNS : ¬ T.Occurs q)
    (hST : st_trans T (st_label.out r lab S) T') : q ≠ r := by
  intro heq
  subst heq
  exact hNS (st_trans_out_sender_occurs hST)

/-- Occurrence back-propagates from `st_trans` targets to sources (branch-target
    occurrence lifts through the choice head; `tRec` goes through the
    unfolded derivation with the IH, closing via `occurs_of_subst`). -/
lemma occurs_of_st_trans_target {T T' : SessionType} {α : st_label} {r : Role}
    (hST : st_trans T α T') (hOcc : T'.Occurs r) : T.Occurs r := by
  revert hOcc
  induction hST with
  | intC hmem =>
    intro hOcc
    exact SessionType.Occurs.intTarget hmem hOcc
  | extC hmem =>
    intro hOcc
    exact SessionType.Occurs.extTarget hmem hOcc
  | tRec hsub ih =>
    intro hOcc
    rcases occurs_of_subst (ih hOcc) with hL | hR
    · exact SessionType.Occurs.recBody hL
    · exact hR

/-- `tEnd` takes no `st_trans` step (all three rules conclude choice/`tRec` heads). -/
lemma st_trans_t_end_absurd {α : st_label} {T' : SessionType} :
    ¬ st_trans SessionType.tEnd α T' := by
  intro h
  cases h

/-- Termination measure step: a branch target is smaller than head-plus-tail sizes (used for the
   `mutual` decreases proofs on branch lists). -/
lemma sizeOf_int_quad_lt (h : Role × Lab × DataSort × SessionType)
    (t : List (Role × Lab × DataSort × SessionType)) :
    sizeOf h.2.2.2 < 1 + sizeOf h + sizeOf t := by
  rcases h with ⟨p, lab, S, T'⟩
  simp
  omega

/-- Termination measure step: an external-choice branch target is smaller than head-plus-tail sizes
   (used for the `mutual` decreases proofs on branch lists). -/
lemma sizeOf_ext_triple_lt (h : Lab × DataSort × SessionType)
    (t : List (Lab × DataSort × SessionType)) :
    sizeOf h.2.2 < 1 + sizeOf h + sizeOf t := by
  rcases h with ⟨lab, S, T'⟩
  simp
  omega

mutual
  /-- Substituting a closed type filters exactly the substituted variable out of the free-variable
     list. -/
  theorem fv_subst_aux : (T : SessionType) → (X : String) → (U : SessionType) → U.IsClosed →
      (substSessionType T X U).fv = T.fv.filter (λ x => x != X)
  | SessionType.tEnd, X, U, hU => by
      simp [substSessionType, SessionType.fv]
  | SessionType.tVar Y, X, U, hU => by
      by_cases hXY : X = Y
      · subst hXY
        simp [substSessionType, SessionType.fv, List.filter]
        exact hU
      · simp [substSessionType, hXY, SessionType.fv, List.filter]
        have hyb : (Y != X) = true := by
          have hn : ¬Y = X := by intro hyx; exact hXY hyx.symm
          cases hb : Y == X with
          | true =>
            exfalso
            exact hn (beq_iff_eq.mp hb)
          | false =>
            simpa using hn
        simp [hyb]
  | SessionType.internalChoice branches, X, U, hU => by
      change SessionType.fv.goInt (substSessionType.goInt X U branches) =
        (SessionType.fv.goInt branches).filter (λ x => x != X)
      exact fv_goInt U hU X branches
  | SessionType.externalChoice p branches, X, U, hU => by
      change SessionType.fv.goExt (substSessionType.goExt X U branches) =
        (SessionType.fv.goExt branches).filter (λ x => x != X)
      exact fv_goExt U hU X branches
  | SessionType.tRec Y T', X, U, hU => by
      by_cases hXY : X = Y
      · simp [substSessionType, hXY, SessionType.fv, List.filter_filter]
      · simp [substSessionType, hXY, SessionType.fv]
        rw [fv_subst_aux T' X U hU]
        rw [List.filter_filter]
        simp [Bool.and_comm]
  termination_by T X U hU => sizeOf T
  decreasing_by
    all_goals simp_wf

  /-- Lifting `fv_subst_aux` through internal-choice branch lists. -/
  theorem fv_goInt : (U : SessionType) → U.IsClosed → (X : String) →
      (l : List (Role × Lab × DataSort × SessionType)) →
      SessionType.fv.goInt (substSessionType.goInt X U l) =
        (SessionType.fv.goInt l).filter (λ x => x != X)
  | U, hU, X, [] => by simp [substSessionType.goInt, SessionType.fv.goInt]
  | U, hU, X, h :: t => by
      simp [substSessionType.goInt, SessionType.fv.goInt, List.filter_append,
        fv_goInt U hU X t, fv_subst_aux h.2.2.2 X U hU]
  termination_by U hU X l => sizeOf l
  decreasing_by
    all_goals simp_wf <;> first | exact sizeOf_int_quad_lt h t

  /-- Lifting `fv_subst_aux` through external-choice branch lists. -/
  theorem fv_goExt : (U : SessionType) → U.IsClosed → (X : String) →
      (l : List (Lab × DataSort × SessionType)) →
      SessionType.fv.goExt (substSessionType.goExt X U l) =
        (SessionType.fv.goExt l).filter (λ x => x != X)
  | U, hU, X, [] => by simp [substSessionType.goExt, SessionType.fv.goExt]
  | U, hU, X, h :: t => by
      simp [substSessionType.goExt, SessionType.fv.goExt, List.filter_append,
        fv_goExt U hU X t, fv_subst_aux h.2.2 X U hU]
  termination_by U hU X l => sizeOf l
  decreasing_by
    all_goals simp_wf <;> first | exact sizeOf_ext_triple_lt h t
end

/-- Local (private) copy of the `goInt` traversal characterization, for use outside the `mutual`
   block. -/
private lemma go_int_eq_map' (X : String) (U : SessionType)
    (l : List (Role × Lab × DataSort × SessionType)) :
    substSessionType.goInt X U l = l.map (λ (p, lab, S, T') => (p, lab, S, substSessionType T' X U)) := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rcases h with ⟨p, lab, S, T'⟩
    simp [substSessionType.goInt, ih]

/-- Local (private) copy of the `goExt` traversal characterization, for use outside the `mutual`
   block. -/
private lemma go_ext_eq_map' (X : String) (U : SessionType)
    (l : List (Lab × DataSort × SessionType)) :
    substSessionType.goExt X U l = l.map (λ (lab, S, T') => (lab, S, substSessionType T' X U)) := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    rcases h with ⟨lab, S, T'⟩
    simp [substSessionType.goExt, ih]

/-- Substitution preserves `NoDupl` (branch keys are unchanged by substitution; branch targets
   recurse). -/
lemma NoDupl_subst {T U : SessionType} {X : String}
    (h_noDupl : SessionType.NoDupl T) (h_noDupl_U : SessionType.NoDupl U) :
    SessionType.NoDupl (substSessionType T X U) := by
  induction h_noDupl generalizing X U
  · simp [substSessionType, SessionType.NoDupl.end]
  · simp [substSessionType]
    split <;> simp [h_noDupl_U, SessionType.NoDupl.tVar]
  · rename_i branches h_nodup h_nonempty h_branches ih
    have h_branches' : ∀ x ∈ substSessionType.goInt X U branches, SessionType.NoDupl x.2.2.2 := by
      intro x hx
      rw [go_int_eq_map' X U] at hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact ih y hy h_noDupl_U
    have hmap' : ∀ (l : List (Role × Lab × DataSort × SessionType)),
      List.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
        (substSessionType.goInt X U l) =
      List.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) l := by
      intro l; induction l with
      | nil => rfl
      | cons h t ih' =>
        rcases h with ⟨p, lab, S, T'⟩
        simp [substSessionType.goInt, ih']
    have h_nodup' : List.Nodup (List.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))
      (substSessionType.goInt X U branches)) := by
      rw [hmap' branches]
      exact h_nodup
    have h_nonempty'_goInt : ∀ (l : List (Role × Lab × DataSort × SessionType)), l ≠ [] → substSessionType.goInt X U l ≠ [] := by
      intro l
      induction l with
      | nil => intro h; simp [substSessionType.goInt]; exact h rfl
      | cons h t ih' => intro h; simp [substSessionType.goInt]
    have h_nonempty' : substSessionType.goInt X U branches ≠ [] :=
      h_nonempty'_goInt branches h_nonempty
    exact SessionType.NoDupl.internalChoice h_nodup' h_nonempty' h_branches'
  · rename_i r branches h_nodup h_nonempty h_branches ih
    have hmap' : ∀ (l : List (Lab × DataSort × SessionType)),
      List.map (λ x : Lab × DataSort × SessionType => (x.1))
        (substSessionType.goExt X U l) =
      List.map (λ x : Lab × DataSort × SessionType => (x.1)) l := by
      intro l; induction l with
      | nil => rfl
      | cons h t ih' =>
        rcases h with ⟨lab, S, T'⟩
        simp [substSessionType.goExt, ih']
    have h_nodup' : List.Nodup (List.map (λ x : Lab × DataSort × SessionType => (x.1))
      (substSessionType.goExt X U branches)) := by
      rw [hmap' branches]
      exact h_nodup
    have h_nonempty'_goExt : ∀ (l : List (Lab × DataSort × SessionType)), l ≠ [] → substSessionType.goExt X U l ≠ [] := by
      intro l
      induction l with
      | nil => intro h; simp [substSessionType.goExt]; exact h rfl
      | cons h t ih' => intro h; simp [substSessionType.goExt]
    have h_nonempty' : substSessionType.goExt X U branches ≠ [] :=
      h_nonempty'_goExt branches h_nonempty
    have h_branches' : ∀ x ∈ substSessionType.goExt X U branches, SessionType.NoDupl x.2.2 := by
      intro x hx
      rw [go_ext_eq_map' X U] at hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact ih y hy h_noDupl_U
    exact SessionType.NoDupl.externalChoice h_nodup' h_nonempty' h_branches'
  · rename_i X' T' h_noDupl_T' ih
    simp [substSessionType]
    split
    · exact SessionType.NoDupl.tRec h_noDupl_T'
    · exact SessionType.NoDupl.tRec (ih h_noDupl_U)

/-- In a contractive type, a variable that does not occur free is guarded. -/
lemma Guarded_of_not_mem_fv {T : SessionType} {Z : String} (hT : T.Contractive) (hZ : Z ∉ T.fv) :
    SessionType.Guarded Z T := by
  induction hT
  · simp [SessionType.Guarded]
  · simpa [SessionType.Guarded, SessionType.fv] using hZ
  · simp [SessionType.Guarded]
  · simp [SessionType.Guarded]
  · rename_i Y T' hC hG ih
    by_cases hZY : Z = Y
    · subst hZY
      simpa [SessionType.Guarded] using hG
    · have hZ' : Z ∉ T'.fv := by
        intro hZ_in
        have hZ'' : Z ∈ (T'.fv).filter (fun x => x != Y) := by
          rw [List.mem_filter]
          constructor
          · exact hZ_in
          · have hn : ¬ Z = Y := hZY
            cases hb : Z == Y with
            | true =>
              exfalso
              exact hn (beq_iff_eq.mp hb)
            | false =>
              simpa using hn
        exact hZ (by change Z ∈ (T'.fv).filter (fun x => x != Y); exact hZ'')
      simpa [SessionType.Guarded] using (ih hZ')

/-- A contractive and closed type is guarded for every variable. -/
lemma Guarded_all_of_closed (U : SessionType) (Z : String) (hU : U.Contractive) (hUc : U.IsClosed) :
    SessionType.Guarded Z U := by
  apply Guarded_of_not_mem_fv hU
  unfold SessionType.IsClosed at hUc
  simp [hUc]

/-- `Guarded` is preserved under substitution when the variable of interest is
    guarded both in the substituted type and in the inserted type. -/
lemma Guarded_subst_guarded {X Z : String} (C U : SessionType)
    (h_gC : SessionType.Guarded Z C) (h_gU : SessionType.Guarded Z U) :
    SessionType.Guarded Z (substSessionType C X U) := by
  cases C with
  | tEnd => simp [SessionType.Guarded, substSessionType]
  | tVar W =>
      by_cases hXY : X = W
      · subst hXY
        simp [substSessionType]
        exact h_gU
      · simp [substSessionType, hXY, SessionType.Guarded]
        exact h_gC
  | internalChoice _ =>
      simp [SessionType.Guarded, substSessionType]
  | externalChoice _ _ =>
      simp [SessionType.Guarded, substSessionType]
  | tRec Y C' =>
      by_cases hXY : X = Y
      · simpa [substSessionType, hXY, SessionType.Guarded] using h_gC
      · simpa [substSessionType, hXY, SessionType.Guarded] using
          (Guarded_subst_guarded C' U (by simpa [SessionType.Guarded] using h_gC) h_gU)

/-- Substitution with a closed, contractive type preserves contractiveness (`Guarded` threads
   through the substituted part via `Guarded_subst_guarded`). -/
lemma IsContractive_subst {T U : SessionType} {X : String}
    (hI : T.Contractive) (hU : U.Contractive) (hUc : U.IsClosed) :
    (substSessionType T X U).Contractive := by
  induction hI
  · simpa [substSessionType] using SessionType.Contractive.end
  · rename_i W
    by_cases hXY : X = W
    · subst hXY
      simpa [substSessionType] using hU
    · simpa [substSessionType, hXY] using (SessionType.Contractive.tVar W)
  · rename_i branches h_branches ih
    have h_branches' : ∀ x ∈ substSessionType.goInt X U branches, SessionType.Contractive x.2.2.2 := by
      intro x hx
      rw [go_int_eq_map' X U] at hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact ih y hy
    change SessionType.Contractive (SessionType.internalChoice (substSessionType.goInt X U branches))
    exact SessionType.Contractive.internalChoice h_branches'
  · rename_i r branches h_branches ih
    have h_branches' : ∀ x ∈ substSessionType.goExt X U branches, SessionType.Contractive x.2.2 := by
      intro x hx
      rw [go_ext_eq_map' X U] at hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact ih y hy
    change SessionType.Contractive (SessionType.externalChoice r (substSessionType.goExt X U branches))
    exact SessionType.Contractive.externalChoice h_branches'
  · rename_i Y T' hC hG ih
    by_cases hXY : X = Y
    · simpa [substSessionType, hXY] using (SessionType.Contractive.tRec hC hG)
    · simp [substSessionType, hXY]
      apply SessionType.Contractive.tRec
      · exact ih
      · exact Guarded_subst_guarded T' U hG (Guarded_all_of_closed U Y hU hUc)

/-- If the concatenated free variables of an internal-choice branch list are empty, every branch
   target is closed. -/
lemma fv_nil_of_goInt_nil (l : List (Role × Lab × DataSort × SessionType))
    (h : SessionType.fv.goInt l = []) : ∀ x ∈ l, x.2.2.2.fv = [] := by
  induction l with
  | nil =>
      intro x hx
      cases hx
  | cons hd tl ih =>
      rcases hd with ⟨p, lab, S, T0⟩
      simp [SessionType.fv.goInt, List.append_eq_nil_iff] at h
      rcases h with ⟨hT0, htl⟩
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with hx_eq | hxl
      · rw [hx_eq]
        simpa using hT0
      · exact ih htl x hxl

/-- If the concatenated free variables of an external-choice branch list are empty, every branch
   target is closed. -/
lemma fv_nil_of_goExt_nil (l : List (Lab × DataSort × SessionType))
    (h : SessionType.fv.goExt l = []) : ∀ x ∈ l, x.2.2.fv = [] := by
  induction l with
  | nil =>
      intro x hx
      cases hx
  | cons hd tl ih =>
      rcases hd with ⟨lab, S, T0⟩
      simp [SessionType.fv.goExt, List.append_eq_nil_iff] at h
      rcases h with ⟨hT0, htl⟩
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with hx_eq | hxl
      · rw [hx_eq]
        simpa using hT0
      · exact ih htl x hxl

/-- If a session type is well-formed and performs a transition, it remains well-formed. -/
lemma SessionType.wellFormedPreserved (T : SessionType) (α : st_label) (T' : SessionType)
  (hWF : T.WellFormed) (hTr : st_trans T α T') : T'.WellFormed := by
  revert hWF
  induction hTr with
  | intC h =>
      rename_i branches p lab S T
      intro hWF
      unfold SessionType.WellFormed at hWF
      rcases hWF with ⟨hND, hCl, hCo⟩
      unfold SessionType.WellFormed
      constructor
      · cases hND with
        | internalChoice _ _ h_branches => exact h_branches (p, lab, S, T) h
      · constructor
        · unfold SessionType.IsClosed
          unfold SessionType.IsClosed at hCl
          simp [SessionType.fv] at hCl
          exact fv_nil_of_goInt_nil branches hCl (p, lab, S, T) h
        · cases hCo with
          | internalChoice h_branches => exact h_branches (p, lab, S, T) h
  | extC h =>
      rename_i branches p lab S T
      intro hWF
      unfold SessionType.WellFormed at hWF
      rcases hWF with ⟨hND, hCl, hCo⟩
      unfold SessionType.WellFormed
      constructor
      · cases hND with
        | externalChoice _ _ h_branches => exact h_branches (lab, S, T) h
      · constructor
        · unfold SessionType.IsClosed
          unfold SessionType.IsClosed at hCl
          simp [SessionType.fv] at hCl
          exact fv_nil_of_goExt_nil branches hCl (lab, S, T) h
        · cases hCo with
          | externalChoice h_branches => exact h_branches (lab, S, T) h
  | tRec h ih =>
      rename_i X T0 T1 α
      intro hWF
      unfold SessionType.WellFormed at hWF
      rcases hWF with ⟨hND, hCl, hCo⟩
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


