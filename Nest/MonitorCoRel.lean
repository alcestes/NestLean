import Nest.MonitorCo
import Nest.MonitorCoBase

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-! # MonitorCoRel: relational base of coinductive monitoring.

Fold relation (`fmon`), pruning (`Prune`), and type equivalence (`Eqv`),
with head normalisation, base-case transfer, and well-formedness infrastructure.
Shared by the executable development (`Nest.MonitorCoFun`) and the
coinductive soundness development (`Nest.SemFoldCo`, `Nest.FoldExistsCo`,
`Nest.MonitorSoundnessCo`).
-/

/-- Well-formedness survives one head unfolding. -/
theorem SessionType.WellFormed.unfold_single {X : String} {B : SessionType}
    (hWF : (SessionType.tRec X B).WellFormed) :
    (substSessionType B X (SessionType.tRec X B)).WellFormed := by
  rcases hWF with ⟨hND, hCl, hCo⟩
  cases hND with
  | tRec hND0 =>
    cases hCo with
    | tRec hCo0 hG0 =>
      refine ⟨NoDupl_subst hND0 (SessionType.NoDupl.tRec hND0), ?_, ?_⟩
      · unfold SessionType.IsClosed
        rw [fv_subst_aux B X (SessionType.tRec X B) hCl]
        simpa [SessionType.IsClosed, SessionType.fv] using hCl
      · exact IsContractive_subst hCo0 (SessionType.Contractive.tRec hCo0 hG0) hCl

/-- Computable structural equality on session types (mirrors the `goInt` /
`goExt` helper pattern of `substSessionType`). -/
def SessionType.beq : SessionType → SessionType → Bool
  | .tEnd, .tEnd => true
  | .tVar X, .tVar Y => X == Y
  | .internalChoice bs, .internalChoice bs' => goInt bs bs'
  | .externalChoice p bs, .externalChoice p' bs' => p == p' && goExt bs bs'
  | .tRec X B, .tRec Y C => X == Y && beq B C
  | _, _ => false
where
  goInt : List (Role × Lab × DataSort × SessionType) →
      List (Role × Lab × DataSort × SessionType) → Bool
    | [], [] => true
    | (p, lab, S, T) :: bs, (p', lab', S', T') :: bs' =>
        p == p' && lab == lab' && S == S' && beq T T' && goInt bs bs'
    | _, _ => false
  goExt : List (Lab × DataSort × SessionType) →
      List (Lab × DataSort × SessionType) → Bool
    | [], [] => true
    | (lab, S, T) :: bs, (lab', S', T') :: bs' =>
        lab == lab' && S == S' && beq T T' && goExt bs bs'
    | _, _ => false

mutual
/-- Reflexivity of `beq`. -/
theorem SessionType.beq_refl : ∀ (T : SessionType), T.beq T = true
  | .tEnd => rfl
  | .tVar X => by simp [SessionType.beq]
  | .internalChoice bs => by simp [SessionType.beq, SessionType.beq_refl_int bs]
  | .externalChoice p bs => by simp [SessionType.beq, SessionType.beq_refl_ext bs]
  | .tRec X B => by simp [SessionType.beq, SessionType.beq_refl B]

/-- Reflexivity of the internal-branch helper. -/
theorem SessionType.beq_refl_int :
    ∀ (l : List (Role × Lab × DataSort × SessionType)),
      SessionType.beq.goInt l l = true
  | [] => rfl
  | (p, lab, S, T) :: bs => by
      simp [SessionType.beq.goInt, SessionType.beq_refl T, SessionType.beq_refl_int bs]

/-- Reflexivity of the external-branch helper. -/
theorem SessionType.beq_refl_ext :
    ∀ (l : List (Lab × DataSort × SessionType)),
      SessionType.beq.goExt l l = true
  | [] => rfl
  | (lab, S, T) :: bs => by
      simp [SessionType.beq.goExt, SessionType.beq_refl T, SessionType.beq_refl_ext bs]
end

mutual
/-- Soundness of `beq`: equal-by-test implies Leibniz equality. -/
theorem SessionType.beq_sound : ∀ (T U : SessionType), T.beq U = true → T = U
  | .tEnd, .tEnd, _ => rfl
  | .tVar X, .tVar Y, h => by
      simp only [SessionType.beq] at h
      exact congrArg _ (beq_iff_eq.mp h)
  | .internalChoice bs, .internalChoice bs', h => by
      simp only [SessionType.beq] at h
      exact congrArg _ (SessionType.beq_sound_int _ _ h)
  | .externalChoice p bs, .externalChoice p' bs', h => by
      simp only [SessionType.beq, Bool.and_eq_true] at h
      obtain ⟨hp, hs⟩ := h
      have e1 : p = p' := beq_iff_eq.mp hp
      subst e1
      exact congrArg _ (SessionType.beq_sound_ext _ _ hs)
  | .tRec X B, .tRec Y C, h => by
      simp only [SessionType.beq, Bool.and_eq_true] at h
      obtain ⟨hXY, hBC⟩ := h
      have e1 : X = Y := beq_iff_eq.mp hXY
      subst e1
      exact congrArg _ (SessionType.beq_sound _ _ hBC)
  | .tEnd, .tVar _, h => by simp [SessionType.beq] at h
  | .tEnd, .internalChoice _, h => by simp [SessionType.beq] at h
  | .tEnd, .externalChoice _ _, h => by simp [SessionType.beq] at h
  | .tEnd, .tRec _ _, h => by simp [SessionType.beq] at h
  | .tVar _, .tEnd, h => by simp [SessionType.beq] at h
  | .tVar _, .internalChoice _, h => by simp [SessionType.beq] at h
  | .tVar _, .externalChoice _ _, h => by simp [SessionType.beq] at h
  | .tVar _, .tRec _ _, h => by simp [SessionType.beq] at h
  | .internalChoice _, .tEnd, h => by simp [SessionType.beq] at h
  | .internalChoice _, .tVar _, h => by simp [SessionType.beq] at h
  | .internalChoice _, .externalChoice _ _, h => by simp [SessionType.beq] at h
  | .internalChoice _, .tRec _ _, h => by simp [SessionType.beq] at h
  | .externalChoice _ _, .tEnd, h => by simp [SessionType.beq] at h
  | .externalChoice _ _, .tVar _, h => by simp [SessionType.beq] at h
  | .externalChoice _ _, .internalChoice _, h => by simp [SessionType.beq] at h
  | .externalChoice _ _, .tRec _ _, h => by simp [SessionType.beq] at h
  | .tRec _ _, .tEnd, h => by simp [SessionType.beq] at h
  | .tRec _ _, .tVar _, h => by simp [SessionType.beq] at h
  | .tRec _ _, .internalChoice _, h => by simp [SessionType.beq] at h
  | .tRec _ _, .externalChoice _ _, h => by simp [SessionType.beq] at h

/-- Soundness of the internal-branch helper. -/
theorem SessionType.beq_sound_int :
    ∀ (l l' : List (Role × Lab × DataSort × SessionType)),
      SessionType.beq.goInt l l' = true → l = l'
  | [], [], _ => rfl
  | (p, lab, S, T) :: bs, (p', lab', S', T') :: bs', h => by
      simp only [SessionType.beq.goInt, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hp, hl⟩, hs⟩, hT⟩, hbs⟩ := h
      have e1 : p = p' := beq_iff_eq.mp hp
      have e2 : lab = lab' := beq_iff_eq.mp hl
      have e3 : S = S' := beq_iff_eq.mp hs
      have e4 : T = T' := SessionType.beq_sound _ _ hT
      have e5 : bs = bs' := SessionType.beq_sound_int _ _ hbs
      rw [e1, e2, e3, e4, e5]
  | [], _ :: _, h => by simp [SessionType.beq.goInt] at h
  | _ :: _, [], h => by simp [SessionType.beq.goInt] at h

/-- Soundness of the external-branch helper. -/
theorem SessionType.beq_sound_ext :
    ∀ (l l' : List (Lab × DataSort × SessionType)),
      SessionType.beq.goExt l l' = true → l = l'
  | [], [], _ => rfl
  | (lab, S, T) :: bs, (lab', S', T') :: bs', h => by
      simp only [SessionType.beq.goExt, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hl, hs⟩, hT⟩, hbs⟩ := h
      have e1 : lab = lab' := beq_iff_eq.mp hl
      have e2 : S = S' := beq_iff_eq.mp hs
      have e3 : T = T' := SessionType.beq_sound _ _ hT
      have e4 : bs = bs' := SessionType.beq_sound_ext _ _ hbs
      rw [e1, e2, e3, e4]
  | [], _ :: _, h => by simp [SessionType.beq.goExt] at h
  | _ :: _, [], h => by simp [SessionType.beq.goExt] at h
end

/-- Correctness of `beq` (both directions). -/
theorem SessionType.beq_iff (T U : SessionType) : T.beq U = true ↔ T = U :=
  ⟨SessionType.beq_sound _ _, fun h => by subst h; exact SessionType.beq_refl _⟩

/-- Computable decidable equality via `beq_iff`.
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
instance SessionType.decEqComputed : DecidableEq SessionType :=
  fun T U => decidable_of_bool (T.beq U) (SessionType.beq_iff T U)

/-- Head normal form predicate (port; see header for credit). -/
def hnf (T H : SessionType) : Prop := UnfoldStar T H ∧ IsHeadNF H

/-- Fuel-bounded head unfolding (port; see header for credit). -/
def headFuel : Nat → SessionType → SessionType
  | 0, T => T
  | n + 1, .tRec X B => headFuel n (substSessionType B X (.tRec X B))
  | _ + 1, T => T

/-- Head-`tRec` depth bound (port; see header for credit). -/
def headDepth : SessionType → Nat
  | .tRec _ B => headDepth B + 1
  | _ => 0

/-- Executable head normal form (port; see header for credit). -/
def head (T : SessionType) : SessionType := headFuel (headDepth T) T

/-- `headDepth` equals `spine` (port; see header for credit). -/
private theorem headDepth_eq_spine (T : SessionType) : headDepth T = T.spine := by
  cases T with
  | tRec X B =>
      simp [headDepth, SessionType.spine, headDepth_eq_spine B]
  | _ => rfl
termination_by sizeOf T

/-- Fuel-correctness of `headFuel` (port; see header for credit). -/
theorem headFuel_correct (fuel : Nat) {T : SessionType} (wf : T.WellFormed)
    (bound : T.spine ≤ fuel) : hnf T (headFuel fuel T) := by
  induction fuel generalizing T with
  | zero =>
      cases T <;> simp_all [SessionType.spine, headFuel, hnf, IsHeadNF, UnfoldStar.refl]
  | succ n ih =>
      cases T with
      | tRec X B =>
          have unfolded := SessionType.wellFormedUnfold wf (.step .tRec (.refl _))
          have smaller : (substSessionType B X (.tRec X B)).spine ≤ n := by
            cases wf.2.2 with
            | tRec contractive guarded =>
                have h := spine_subst_le B X (.tRec X B)
                  (guarded_not_mem_headVars B X guarded)
                simp only [SessionType.spine] at bound
                omega
          obtain ⟨steps, normal⟩ := ih unfolded smaller
          exact ⟨.step .tRec steps, normal⟩
      | _ => exact ⟨.refl _, trivial⟩

/-- Correctness of `head` (port; see header for credit). -/
theorem head_correct {T : SessionType} (wf : T.WellFormed) : hnf T (head T) :=
  headFuel_correct (headDepth T) wf (by rw [headDepth_eq_spine])

/-- Fresh recursion variable for fold contexts (port; see header for credit). -/
def fvar : Nat → String
  | 0 => "%"
  | n + 1 => "'" ++ fvar n

/-- Fold target: rebind `u` iff it occurs free (port; see header for credit). -/
def mkRec (u : String) (V : SessionType) : SessionType :=
  if u ∈ V.fv then .tRec u V else V

/-- Fold context: stack of `(type, variable)` binders (port; see header for credit). -/
abbrev FCtx := List (SessionType × String)

/-- Choice head predicate (see header for credit). -/
def IsChoice : SessionType → Prop
  | .internalChoice _ | .externalChoice _ _ => True
  | _ => False

mutual
  /-- Inductive fold relation (port; see header for credit). -/
  inductive fmon : FCtx → SessionType → ext_tag → SessionType → Prop where
    | fm_base {G T g V} : mon_tr_yes_base T g V → fmon G T g V
    | fm_pfxInt {G bs kept q lab S}
        (hne : bs ≠ []) (hke : kept ≠ [])
        (hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ bs → q ≠ p')
        (hall : ∀ T0 T1 r l s, (r, l, s, T0) ∈ bs → (r, l, s, T1) ∈ kept →
          fchild G T0 (.recv q lab S) T1)
        (hnd : (kept.map int_key).Nodup)
        (hkey : ∀ r l s T1, (r, l, s, T1) ∈ kept →
          ∃ T0, (r, l, s, T0) ∈ bs ∧ Ex T0 (.recv q lab S))
        (hcov : ∀ r l s T0, (r, l, s, T0) ∈ bs → Ex T0 (.recv q lab S) →
          ∃ T1, (r, l, s, T1) ∈ kept)
        (hord : (kept.map int_key3).Sublist (bs.map int_key3)) :
        fmon G (.internalChoice bs) (.recv q lab S) (.internalChoice kept)
    | fm_pfxExt {G p bs kept q lab S}
        (hne : bs ≠ []) (hke : kept ≠ []) (hneq : q ≠ p)
        (hall : ∀ T0 T1 l s, (l, s, T0) ∈ bs → (l, s, T1) ∈ kept →
          fchild G T0 (.recv q lab S) T1)
        (hnd : (kept.map ext_key).Nodup)
        (hkey : ∀ l s T1, (l, s, T1) ∈ kept →
          ∃ T0, (l, s, T0) ∈ bs ∧ Ex T0 (.recv q lab S))
        (hcov : ∀ l s T0, (l, s, T0) ∈ bs → Ex T0 (.recv q lab S) →
          ∃ T1, (l, s, T1) ∈ kept)
        (hord : (kept.map ext_key2).Sublist (bs.map ext_key2)) :
        fmon G (.externalChoice p bs) (.recv q lab S) (.externalChoice p kept)
    | fm_rec {G X B H g V}
        (hS : UnfoldStar (.tRec X B) H) (hNF : IsHeadNF H)
        (hsub : fmon ((.tRec X B, fvar G.length) :: G) H g V) :
        fmon G (.tRec X B) g (mkRec (fvar G.length) V)

  /-- Fold child: fold variable or recursive fold (port; see header for credit). -/
  inductive fchild : FCtx → SessionType → ext_tag → SessionType → Prop where
    | fc_fold {G T g u} : (T, u) ∈ G → fchild G T g (.tVar u)
    | fc_go {G T g V} : T ∉ G.map Prod.fst → fmon G T g V → fchild G T g V
end

/-- `fvar` length (see header). -/
theorem fvar_length (n : Nat) : (fvar n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fvar, String.length_append, ih]; change 1 + (n + 1) = n + 1 + 1; omega

/-- `fvar` injectivity (port; see header for credit). -/
theorem fvar_inj {n m : Nat} (h : fvar n = fvar m) : n = m := by
  have := congrArg String.length h
  simp only [fvar_length] at this
  omega

/-- Free variables of `mkRec` (port; see header for credit). -/
theorem fv_mkRec {u y : String} {V : SessionType} (h : y ∈ (mkRec u V).fv) :
    y ∈ V.fv ∧ y ≠ u := by
  unfold mkRec at h
  split at h
  · simpa [SessionType.fv] using h
  · exact ⟨h, fun he => by subst he; contradiction⟩

/-- Internal membership iff (port; see header for credit). -/
theorem fv_int_iff {bs : List (Role × Lab × DataSort × SessionType)} {y : String} :
    y ∈ (SessionType.internalChoice bs).fv ↔ ∃ b ∈ bs, y ∈ b.2.2.2.fv := by
  change y ∈ SessionType.fv.goInt bs ↔ _
  induction bs with
  | nil => simp [SessionType.fv.goInt]
  | cons b bs ih =>
    rcases b with ⟨p, l, s, T⟩
    simp [SessionType.fv.goInt, ih]

/-- External membership iff (port; see header for credit). -/
theorem fv_ext_iff {p : Role} {bs : List (Lab × DataSort × SessionType)} {y : String} :
    y ∈ (SessionType.externalChoice p bs).fv ↔ ∃ b ∈ bs, y ∈ b.2.2.fv := by
  change y ∈ SessionType.fv.goExt bs ↔ _
  induction bs with
  | nil => simp [SessionType.fv.goExt]
  | cons b bs ih =>
    rcases b with ⟨l, s, T⟩
    simp [SessionType.fv.goExt, ih]

/-- Well-formed branch target (internal, port; see header for credit). -/
theorem wf_of_mem_int {bs : List (Role × Lab × DataSort × SessionType)} {b : Role × Lab × DataSort × SessionType}
    (h : (SessionType.internalChoice bs).WellFormed) (hb : b ∈ bs) : b.2.2.2.WellFormed :=
  ⟨noDupl_of_mem_intBranches h.1 hb,
   isClosed_of_mem_intBranches h.2.1 hb, isContractive_of_mem_intBranches h.2.2 hb⟩

/-- Well-formed branch target (external, port; see header for credit). -/
theorem wf_of_mem_ext {p : Role} {bs : List (Lab × DataSort × SessionType)} {b : Lab × DataSort × SessionType}
    (h : (SessionType.externalChoice p bs).WellFormed) (hb : b ∈ bs) : b.2.2.WellFormed :=
  ⟨noDupl_of_mem_extBranches h.1 hb,
   isClosed_of_mem_extBranches h.2.1 hb, isContractive_of_mem_extBranches h.2.2 hb⟩

/-- Fold at head-normal form yields well-formed or choice (port; see header). -/
theorem fmon_headnf_shape {G H g V} (hNF : IsHeadNF H) (hWF : H.WellFormed)
    (h : fmon G H g V) : V.WellFormed ∨ IsChoice V := by
  cases h
  case fm_base hb => exact .inl (mon_tr_yes_base_preserves_wf hb hWF)
  case fm_pfxInt => exact .inr trivial
  case fm_pfxExt => exact .inr trivial
  case fm_rec => exact False.elim hNF

/-- Choices are guarded (port; see header for credit). -/
theorem guarded_of_choice (u : String) {V : SessionType} (h : IsChoice V) : V.Guarded u := by
  cases V <;> simp_all [IsChoice, SessionType.Guarded]

/-- Fold well-formedness invariant (port; see header for credit). -/
def FWF (G : FCtx) (V : SessionType) : Prop :=
  V.NoDupl ∧ V.Contractive ∧ ∀ y ∈ V.fv, y ∈ G.map Prod.snd

/-- `fmon` preserves well-formedness into `FWF` (port; see header for credit). -/
theorem fmon_wf {G T g V} (h : fmon G T g V) : T.WellFormed → FWF G V := by
  apply fmon.rec
    (motive_1 := fun G T _ V _ => T.WellFormed → FWF G V)
    (motive_2 := fun G T _ V _ => T.WellFormed → FWF G V) (t := h)
  case fm_base =>
      intro G T g V hb hW
      obtain ⟨hND, hCl, hCo⟩ := mon_tr_yes_base_preserves_wf hb hW
      refine ⟨hND, hCo, ?_⟩
      intro y hy
      change V.fv = [] at hCl
      simp [hCl] at hy
  case fm_pfxInt =>
      intro G bs kept q lab S hne hke hno hall hnd hkey hcov hord ih hW
      have hk : ∀ b ∈ kept, FWF G b.2.2.2 := by
        rintro ⟨r,l,s,T1⟩ h1
        obtain ⟨T0,h0,_⟩ := hkey r l s T1 h1
        exact ih T0 T1 r l s h0 h1 (wf_of_mem_int hW h0)
      refine ⟨.internalChoice hnd hke (fun b hb => (hk b hb).1),
        .internalChoice (fun b hb => (hk b hb).2.1), ?_⟩
      intro y hy
      obtain ⟨b,hb,hy⟩ := fv_int_iff.mp hy
      exact (hk b hb).2.2 y hy
  case fm_pfxExt =>
      intro G p bs kept q lab S hne hke hneq hall hnd hkey hcov hord ih hW
      have hk : ∀ b ∈ kept, FWF G b.2.2 := by
        rintro ⟨l,s,T1⟩ h1
        obtain ⟨T0,h0,_⟩ := hkey l s T1 h1
        exact ih T0 T1 l s h0 h1 (wf_of_mem_ext hW h0)
      refine ⟨.externalChoice hnd hke (fun b hb => (hk b hb).1),
        .externalChoice (fun b hb => (hk b hb).2.1), ?_⟩
      intro y hy
      obtain ⟨b,hb,hy⟩ := fv_ext_iff.mp hy
      exact (hk b hb).2.2 y hy
  case fm_rec =>
      intro G X B H g V hS hNF hsub ih hW
      have hH := SessionType.wellFormedUnfold hW hS
      obtain ⟨hND,hCo,hfv⟩ := ih hH
      have hbound : ∀ y ∈ (mkRec (fvar G.length) V).fv, y ∈ G.map Prod.snd := by
        intro y hy
        obtain ⟨hy,hne⟩ := fv_mkRec hy
        have hmem := hfv y hy
        simpa [hne] using hmem
      unfold mkRec at hbound ⊢
      split
      · rename_i hmem
        simp only [ite_eq_left hmem] at hbound
        refine ⟨.tRec hND, .tRec hCo ?_, hbound⟩
        rcases fmon_headnf_shape hNF hH hsub with hclosed | hchoice
        · have hc : V.fv = [] := hclosed.2.1
          simp [hc] at hmem
        · exact guarded_of_choice _ hchoice
      · rename_i hmem
        simp only [ite_eq_right hmem] at hbound
        exact ⟨hND,hCo,hbound⟩
  case fc_fold =>
      intro G T g u hin _
      refine ⟨.tVar u, .tVar u, ?_⟩
      intro y hy
      have : y = u := by simpa [SessionType.fv] using hy
      subst y
      exact List.mem_map.mpr ⟨(T,u),hin,rfl⟩
  case fc_go =>
      intro G T g V hfresh hsub ih
      exact ih

/-- Fold preserves well-formedness at empty context (port; see header). -/
theorem fmon_preserves_wf {T g V} (hW : T.WellFormed) (h : fmon [] T g V) : V.WellFormed := by
  obtain ⟨hND,hCo,hfv⟩ := fmon_wf h hW
  refine ⟨hND,?_,hCo⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro y hy
  exact List.not_mem_nil (hfv y hy)

/-- Pair-key nodup from well-formedness (port; see header for credit). -/
theorem nodup_int_key_of_wf {bs : List (Role × Lab × DataSort × SessionType)}
    (hW : (SessionType.internalChoice bs).WellFormed) :
    (bs.map int_key).Nodup := by
  cases hW.1 with
  | internalChoice hnd _ _ => exact hnd

/-- Singleton-key nodup from well-formedness (port; see header for credit). -/
theorem nodup_ext_key_of_wf {p : Role} {bs : List (Lab × DataSort × SessionType)}
    (hW : (SessionType.externalChoice p bs).WellFormed) :
    (bs.map ext_key).Nodup := by
  cases hW.1 with
  | externalChoice hnd _ _ => exact hnd

/-- Pair-key nodup from well-formedness (port; see header for credit). -/
theorem nodup_ext_key2_of_wf {p : Role} {bs : List (Lab × DataSort × SessionType)}
    (hW : (SessionType.externalChoice p bs).WellFormed) :
    (bs.map ext_key2).Nodup :=
  nodup_of_nodup_labels (nodup_ext_key_of_wf hW)

/-- `PruneStep` preserves well-formedness (port; see header for credit). -/
theorem prune_step_wf {T U : SessionType} (h : PruneStep T U) (hW : T.WellFormed) :
    U.WellFormed := by
  cases h with
  | intC hm => exact wf_of_mem_int hW hm
  | extC hm => exact wf_of_mem_ext hW hm
  | trec => exact SessionType.wellFormedUnfold hW (.step .tRec (.refl _))

/-- Unfold stars replay as prune-step paths (port; see header for credit). -/
theorem unfoldstar_prune {T U : SessionType} (h : UnfoldStar T U) :
    Relation.ReflTransGen PruneStep T U := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => cases hs; exact (Relation.ReflTransGen.single .trec).trans ih

/-- Send-observations are always base (port; see header for credit). -/
theorem Ex_send_base {T : SessionType} {p : Role} {l : Lab} {s : DataSort}
    (h : Ex T (.send p l s)) : ∃ V, mon_tr_yes_base T (.send p l s) V := by
  obtain ⟨V, h⟩ := h
  generalize hg : ext_tag.send p l s = g at h
  induction h with
  | base hb => exact ⟨_, hb⟩
  | pfxInt => cases hg
  | pfxExt => cases hg
  | unfold _ ih =>
    obtain ⟨V, hb⟩ := ih hg
    exact ⟨V, .tRec hb⟩

/-- Base steps lift backward along unfold stars (port; see header for credit). -/
theorem base_unfoldstar_lift {T H : SessionType} {g : ext_tag} {V : SessionType}
    (hs : UnfoldStar T H) (hb : mon_tr_yes_base H g V) :
    mon_tr_yes_base T g V := by
  induction hs with
  | refl => exact hb
  | step hs _ ih => cases hs; exact .tRec (ih hb)

/-- Unfolding a head-normal form is the identity (port; see header). -/
theorem UnfoldStar_headnf_inv {T U : SessionType} (steps : UnfoldStar T U)
    (normal : IsHeadNF T) : U = T := by
  cases steps with
  | refl => rfl
  | step first _ => cases first; exact False.elim normal

/-- Head normal forms are unique (port; see header for credit). -/
theorem hnf_unique {T H K : SessionType} (first : hnf T H) (second : hnf T K) :
    H = K := by
  obtain ⟨steps, normal⟩ := first
  induction steps with
  | refl => exact (UnfoldStar_headnf_inv second.1 normal).symm
  | step first rest ih =>
      cases first
      cases second.1 with
      | refl => exact False.elim second.2
      | step first' rest' => cases first'; exact ih ⟨rest', second.2⟩ normal

/-- Every head-normal form is a head normal form of itself (port; see header). -/
theorem hnf_self {T : SessionType} (normal : IsHeadNF T) : hnf T T :=
  ⟨.refl _, normal⟩

/-- Direct base shape at head (port; see header for credit). -/
def base_direct (H : SessionType) (g : ext_tag) (V : SessionType) : Prop :=
  match g, H with
  | .send p l s, .internalChoice bs =>
      (bs.map fun b => (b.1, b.2.1, b.2.2.1)).Nodup ∧ (p, l, s, V) ∈ bs
  | .recv p l s, .externalChoice q bs =>
      q = p ∧ (bs.map fun b => (b.1, b.2.1)).Nodup ∧ (l, s, V) ∈ bs
  | _, _ => False

/-- Every base step factors through head (port; see header for credit). -/
theorem base_hnf {T V : SessionType} {g : ext_tag} (base : mon_tr_yes_base T g V) :
    ∃ H, hnf T H ∧ base_direct H g V := by
  induction base with
  | intC unique member => exact ⟨_, hnf_self trivial, unique, member⟩
  | extC unique member => exact ⟨_, hnf_self trivial, rfl, unique, member⟩
  | tRec _ ih =>
      obtain ⟨H, head, direct⟩ := ih
      exact ⟨H, ⟨.step .tRec head.1, head.2⟩, direct⟩

/-- Direct base at head lifts to a base step (port; see header for credit). -/
theorem base_of_hnf {T H V : SessionType} {g : ext_tag}
    (head : hnf T H) (direct : base_direct H g V) : mon_tr_yes_base T g V := by
  obtain ⟨steps, normal⟩ := head
  induction steps with
  | @refl T0 =>
      cases g with
      | send p l s =>
          cases T0 with
          | internalChoice bs =>
              simp only [base_direct] at direct
              exact .intC direct.1 direct.2
          | tEnd => exact False.elim direct
          | tVar _ => exact False.elim direct
          | externalChoice _ _ => exact False.elim direct
          | tRec _ _ => exact False.elim direct
      | recv p l s =>
          cases T0 with
          | externalChoice q bs =>
              simp only [base_direct] at direct
              obtain ⟨rfl, _, member⟩ := direct
              exact .extC ‹_› member
          | tEnd => exact False.elim direct
          | tVar _ => exact False.elim direct
          | internalChoice _ => exact False.elim direct
          | tRec _ _ => exact False.elim direct
  | step first _ ih => cases first; exact .tRec (ih direct normal)

/-- Existential steps push forward along unfold stars (see header). -/
theorem exist_unfoldstar_inv {T U V : SessionType} {g : ext_tag}
    (steps : UnfoldStar T U) (accept : mon_tr_yes_exist T g V) :
    mon_tr_yes_exist U g V := by
  induction steps with
  | refl => exact accept
  | step first rest ih => cases first; exact ih (mon_tr_yes_exist_trec_inv accept)

/-- Existential steps lift backward along unfold stars (port; `exist_unfoldstar_lift`). -/
theorem exist_unfoldstar_lift {T U V : SessionType} {g : ext_tag}
    (steps : UnfoldStar T U) (accept : mon_tr_yes_exist U g V) :
    mon_tr_yes_exist T g V := by
  induction steps with
  | refl => exact accept
  | step first rest ih => cases first; exact .unfold (ih accept)

/-- `Ex` is invariant under head unfolding (port; see header for credit). -/
theorem Ex_unfoldstar {T U : SessionType} {g : ext_tag} (steps : UnfoldStar T U) :
    Ex T g ↔ Ex U g :=
  ⟨fun ⟨V, h⟩ => ⟨V, exist_unfoldstar_inv steps h⟩,
   fun ⟨V, h⟩ => ⟨V, exist_unfoldstar_lift steps h⟩⟩

/-- Fold-context names are canonical `fvar` indices (port; see header). -/
def GNames (G : FCtx) : Prop := ∀ T u, (T, u) ∈ G → ∃ i, i < G.length ∧ u = fvar i

theorem GNames_nil : GNames [] := by intro T u member; cases member

theorem GNames_push {G : FCtx} (T : SessionType) (names : GNames G) :
    GNames ((T, fvar G.length) :: G) := by
  intro T' u member
  cases List.mem_cons.mp member with
  | inl same =>
      cases same
      exact ⟨G.length, by simp, rfl⟩
  | inr old =>
      obtain ⟨i, lt, eq⟩ := names _ _ old
      exact ⟨i, by simp; omega, eq⟩

theorem GNames_fresh {G : FCtx} {T : SessionType} {u : String}
    (names : GNames G) (member : (T, u) ∈ G) : u ≠ fvar G.length := by
  obtain ⟨i, lt, eq⟩ := names _ _ member
  rw [eq]
  intro contra
  have := fvar_inj contra
  omega

/-- Inductive environment predicate.
`R` is the closed residual stored for `u`: `R = ssubst ρ (mkRec u V)`. -/
inductive EnvCoOK (g : ext_tag) : FCtx → env → Prop where
  | nil : EnvCoOK g [] []
  | cons {G ρ A u X B H V R} : EnvCoOK g G ρ → A.WellFormed → GNames G →
      (hS : UnfoldStar (.tRec X B) H) → (hNF : IsHeadNF H) →
      fmon ((.tRec X B, fvar G.length) :: G) H g V →
      A = .tRec X B → u = fvar G.length → R = ssubst ρ (mkRec u V) →
      EnvCoOK g ((A, u) :: G) ((u, R) :: ρ)

/-- Every name in `G` is bound in `ρ`. -/
theorem EnvCoOK_defined {g : ext_tag} {G : FCtx} {ρ : env} {x : String}
    (h : EnvCoOK g G ρ) (hmem : x ∈ G.map Prod.snd) : elookup ρ x ≠ none := by
  induction h with
  | nil =>
    simp at hmem
  | cons h_old hWF hG hS hNF hsub hA hu hR ih =>
    subst hA; subst hu
    simp only [List.map_cons, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp [elookup]
    · obtain ⟨b, hmemG, heq⟩ := List.mem_map.mp hmem
      obtain ⟨T0, y⟩ := b
      simp at heq
      subst heq
      have hne := GNames_fresh hG hmemG
      have hmem' := ih hmem
      simpa [elookup, hne] using hmem'

/-- `EnvCoOK` environments are closed. -/
theorem EnvCoOK_env_closed {g : ext_tag} {G : FCtx} {ρ : env}
    (h : EnvCoOK g G ρ) : env_closed ρ := by
  induction h with
  | nil =>
    intro x v hm
    cases hm
  | cons =>
    subst_vars
    apply env_closed_cons
    · assumption
    · apply ssubst_closed
      · assumption
      · intro y hy
        obtain ⟨hyV, hyne⟩ := fv_mkRec hy
        have hHWF : _ := SessionType.wellFormedUnfold (by assumption) (by assumption)
        have hFWF := fmon_wf (by assumption) hHWF
        have hmem : y ∈ _ := hFWF.2.2 y hyV
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact absurd rfl hyne
        · exact EnvCoOK_defined (by assumption) hmem

/-- Lookup in `EnvCoOK` (no `R.WellFormed`, frame doesn't need target WF).
Gives old `G0 ρ0` with `fmon G0 T0 g (mkRec u V)` via `fm_rec`. -/
theorem EnvCoOK_lookup {g : ext_tag} {G : FCtx} {ρ : env} {T0 : SessionType} {u : String}
    (h : EnvCoOK g G ρ) (hmem : (T0, u) ∈ G) :
    ∃ X B H V R G0 ρ0, T0 = .tRec X B ∧ elookup ρ u = some R ∧
      R = ssubst ρ0 (mkRec u V) ∧
      EnvCoOK g G0 ρ0 ∧ GNames G0 ∧ fmon G0 T0 g (mkRec u V) ∧
      UnfoldStar (.tRec X B) H ∧ IsHeadNF H ∧
      fmon ((.tRec X B, fvar G0.length) :: G0) H g V := by
  induction h generalizing T0 u with
  | nil =>
    simp at hmem
  | @cons G_old ρ_old A_new u_new X B H V R h_old hWF hG hS hNF hsub hA hu hR ih =>
    subst hA; subst hu; subst hR
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact ⟨X, B, H, V, ssubst ρ_old (mkRec (fvar G_old.length) V),
        G_old, ρ_old, rfl, by simp [elookup], rfl,
        h_old, hG, fmon.fm_rec hS hNF hsub, hS, hNF, hsub⟩
    · obtain ⟨X0, B0, H0, V0, R0, G0, ρ0, hT0, hlook, hReq, hEnv0, hG0, hfmon0, hS0, hNF0, hsub0⟩ :=
        ih hmem
      have hne : u ≠ fvar G_old.length := GNames_fresh hG hmem
      have hbeq : (u == fvar G_old.length) = false := beq_eq_false_iff_ne.mpr hne
      have hlook' : elookup ((fvar G_old.length, ssubst ρ_old (mkRec (fvar G_old.length) V)) :: ρ_old) u = some R0 := by
        simp [elookup, List.lookup_cons, hbeq, hlook]
      exact ⟨X0, B0, H0, V0, R0, G0, ρ0, hT0, hlook', hReq, hEnv0, hG0, hfmon0, hS0, hNF0, hsub0⟩

/-- Closed types are fixed by substitution (via `ssubst_ext` + `ssubst_nil`). -/
theorem ssubst_closed_id' (T : SessionType) (ρ : env) (closed : T.IsClosed) :
    ssubst ρ T = T := by
  have h := ssubst_ext T ρ [] (by
    intro x hx
    simp [SessionType.IsClosed] at closed
    simp [closed] at hx)
  simpa [ssubst_nil] using h

/-- `ssubst` on internal choices maps branch targets (by definition). -/
theorem ssubst_internalChoice (ρ : env) (bs : List (Role × Lab × DataSort × SessionType)) :
    ssubst ρ (SessionType.internalChoice bs) =
    SessionType.internalChoice (bs.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ b.2.2.2)) := by
  simp [ssubst]

/-- `ssubst` on external choices maps branch targets (by definition). -/
theorem ssubst_externalChoice (ρ : env) (p : Role) (bs : List (Lab × DataSort × SessionType)) :
    ssubst ρ (SessionType.externalChoice p bs) =
    SessionType.externalChoice p (bs.map fun b => (b.1, b.2.1, ssubst ρ b.2.2)) := by
  simp [ssubst]

/-- Mapped kept keys unchanged (internal, `int_key3` ignores targets). -/
theorem kept_mapped_keys_int3 (ρ : env)
    (kept : List (Role × Lab × DataSort × SessionType)) :
    ((kept.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ b.2.2.2)).map
      fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) =
    kept.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1) := by
  induction kept with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨r, l, s, T⟩
    simp [ih]

/-- Mapped kept keys unchanged (external, `ext_key2` ignores targets). -/
theorem kept_mapped_keys_ext2 (ρ : env)
    (kept : List (Lab × DataSort × SessionType)) :
    ((kept.map fun b => (b.1, b.2.1, ssubst ρ b.2.2)).map
      fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) =
    kept.map fun x : Lab × DataSort × SessionType => (x.1, x.2.1) := by
  induction kept with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨l, s, T⟩
    simp [ih]

/-- Membership in mapped kept inverts to original (internal). -/
theorem mem_mapped_int_inv {ρ : env} {kept : List (Role × Lab × DataSort × SessionType)}
    {r : Role} {l : Lab} {s : DataSort} {T1' : SessionType}
    (hmem : (r, l, s, T1') ∈ kept.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ b.2.2.2)) :
    ∃ T1, T1' = ssubst ρ T1 ∧ (r, l, s, T1) ∈ kept := by
  rw [List.mem_map] at hmem
  obtain ⟨⟨r', l', s', T1⟩, hmem, heq⟩ := hmem
  simp at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  exact ⟨_, rfl, hmem⟩

/-- Membership in mapped kept inverts to original (external). -/
theorem mem_mapped_ext_inv {ρ : env} {kept : List (Lab × DataSort × SessionType)}
    {l : Lab} {s : DataSort} {T1' : SessionType}
    (hmem : (l, s, T1') ∈ kept.map fun b => (b.1, b.2.1, ssubst ρ b.2.2)) :
    ∃ T1, T1' = ssubst ρ T1 ∧ (l, s, T1) ∈ kept := by
  rw [List.mem_map] at hmem
  obtain ⟨⟨l', s', T1⟩, hmem, heq⟩ := hmem
  simp at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨_, rfl, hmem⟩

/-- Mapped kept non-empty if original non-empty (internal). -/
theorem mapped_kept_ne_nil_int {ρ : env} {kept : List (Role × Lab × DataSort × SessionType)}
    (hne : kept ≠ []) :
    (kept.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ b.2.2.2)) ≠ [] := by
  cases kept with
  | nil => cases hne rfl
  | cons _ _ => simp

/-- Mapped kept non-empty if original non-empty (external). -/
theorem mapped_kept_ne_nil_ext {ρ : env} {kept : List (Lab × DataSort × SessionType)}
    (hne : kept ≠ []) :
    (kept.map fun b => (b.1, b.2.1, ssubst ρ b.2.2)) ≠ [] := by
  cases kept with
  | nil => cases hne rfl
  | cons _ _ => simp

def CoFmonInv (g : ext_tag) (X : SessionType) (δ : ext_tag) (W : SessionType) : Prop :=
  (∃ A G ρ W0, X = A ∧ δ = g ∧ W = ssubst ρ W0 ∧ A.WellFormed ∧ GNames G ∧
    EnvCoOK g G ρ ∧ fmon G A g W0) ∨
  (∃ U H G' ρ' V, X = U ∧ δ = g ∧ W = ssubst ρ' V ∧ U.WellFormed ∧
    UnfoldStar U H ∧ IsHeadNF H ∧ GNames G' ∧ EnvCoOK g G' ρ' ∧ fmon G' H g V)

theorem fmon_implies_mon_tr_yes_co {T V : SessionType} {γ : ext_tag}
    (hT : T.WellFormed) (hV : V.WellFormed)
    (h : fmon [] T γ V) : mon_tr_yes_co T γ V hT hV := by
  have hinit : CoFmonInv γ T γ (ssubst [] V) := by
    left
    exact ⟨T, [], [], V, rfl, rfl, by simp [ssubst_nil], hT, GNames_nil, .nil, h⟩
  have heq : ssubst [] V = V := ssubst_nil V
  rw [heq] at hinit
  refine mon_tr_yes_max_deriv_co.coinduct (CoFmonInv γ) ?_ T γ V hinit
  intro a a_1 a_2 hinv
  rcases hinv with ⟨A, G, ρ, W0, rfl, rfl, rfl, hA, hGnames, hEnv, hfmon⟩ |
    ⟨U, H, G', ρ', V0, rfl, rfl, rfl, hU, hS, hNF, hGnames', hEnv', hfmon'⟩
  · cases hfmon with
    | fm_base hb =>
      have hW0 : W0.WellFormed := mon_tr_yes_base_preserves_wf hb hA
      have heqW : ssubst ρ W0 = W0 := ssubst_closed_id' W0 ρ hW0.2.1
      rw [heqW]
      exact Or.inl ⟨hA, hb⟩
    | @fm_pfxInt G bs kept q lab S hne hke hno hall hnd hkey hcov hord =>
      refine Or.inr (Or.inl ⟨bs, kept.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ b.2.2.2),
        q, lab, S, hA, ⟨hne, mapped_kept_ne_nil_int hke⟩, hno, ?hall', ?hkey', ?hcover', ?horder',
        rfl, rfl, ssubst_internalChoice ρ kept⟩)
      · intro T0 T1' r l s hB hK'
        obtain ⟨T1, rfl, hK⟩ := mem_mapped_int_inv hK'
        have hc := hall T0 T1 r l s hB hK
        cases hc with
        | fc_go hfresh hsub =>
          left
          exact ⟨T0, G, ρ, T1, rfl, rfl, rfl, wf_of_mem_int hA hB, hGnames, hEnv, hsub⟩
        | @fc_fold _ _ _ u hmem =>
          obtain ⟨X, B, H, V, R, G0, ρ0, hT0, hlook, hReq, hEnv0, hG0, hfmon0, hS0, hNF0, hsub0⟩ :=
            EnvCoOK_lookup hEnv hmem
          have hss : ssubst ρ (SessionType.tVar u) = R := by
            simp [ssubst, hlook]
          -- `T1 = tVar u`; `T1' = ssubst ρ T1 = ssubst ρ (tVar u) = R`.
          left
          exact ⟨T0, G0, ρ0, mkRec u V, rfl, rfl, hss.trans hReq,
            wf_of_mem_int hA hB, hG0, hEnv0, hfmon0⟩
      · intro r l s T1' hmem'
        obtain ⟨T1, rfl, hmemK⟩ := mem_mapped_int_inv hmem'
        obtain ⟨T0, hmemB, hEx⟩ := hkey r l s T1 hmemK
        obtain ⟨V', hEx'⟩ := hEx
        exact ⟨T0, hmemB, V', hEx'⟩
      · intro r l s T0 hmemB hEx
        obtain ⟨T1, hmemK⟩ := hcov r l s T0 hmemB hEx
        exact ⟨ssubst ρ T1, List.mem_map.mpr ⟨_, hmemK, rfl⟩⟩
      · rw [kept_mapped_keys_int3]
        exact hord
    | @fm_pfxExt G p bs kept q lab S hne hke hneq hall hnd hkey hcov hord =>
      refine Or.inr (Or.inr (Or.inl ⟨p, bs, kept.map fun b => (b.1, b.2.1, ssubst ρ b.2.2),
        q, lab, S, hA, ⟨hne, mapped_kept_ne_nil_ext hke⟩, hneq, ?hallE, ?hkeyE, ?hcoverE, ?horderE,
        rfl, rfl, ssubst_externalChoice ρ p kept⟩))
      · intro T0 T1' l s hB hK'
        obtain ⟨T1, rfl, hK⟩ := mem_mapped_ext_inv hK'
        have hc := hall T0 T1 l s hB hK
        cases hc with
        | fc_go hfresh hsub =>
          left
          exact ⟨T0, G, ρ, T1, rfl, rfl, rfl, wf_of_mem_ext hA hB, hGnames, hEnv, hsub⟩
        | @fc_fold _ _ _ u hmem =>
          obtain ⟨X, B, H, V, R, G0, ρ0, hT0, hlook, hReq, hEnv0, hG0, hfmon0, hS0, hNF0, hsub0⟩ :=
            EnvCoOK_lookup hEnv hmem
          have hss : ssubst ρ (SessionType.tVar u) = R := by
            simp [ssubst, hlook]
          left
          exact ⟨T0, G0, ρ0, mkRec u V, rfl, rfl, hss.trans hReq,
            wf_of_mem_ext hA hB, hG0, hEnv0, hfmon0⟩
      · intro l s T1' hmem'
        obtain ⟨T1, rfl, hmemK⟩ := mem_mapped_ext_inv hmem'
        obtain ⟨T0, hmemB, hEx⟩ := hkey l s T1 hmemK
        obtain ⟨V', hEx'⟩ := hEx
        exact ⟨T0, hmemB, V', hEx'⟩
      · intro l s T0 hmemB hEx
        obtain ⟨T1, hmemK⟩ := hcov l s T0 hmemB hEx
        exact ⟨ssubst ρ T1, List.mem_map.mpr ⟨_, hmemK, rfl⟩⟩
      · rw [kept_mapped_keys_ext2]
        exact hord
    | @fm_rec G X B H _ V hS hNF hsub =>
      -- `A = tRec X B`, `W0 = mkRec (fvar G.length) V`, `g` unchanged.
      -- `R = ssubst ρ W0`. Split on `fvar G.length ∈ V.fv`.
      by_cases hu : fvar G.length ∈ V.fv
      · -- `u ∈ V.fv`: `R = tRec u (...)`, step by `recR` to spine.
        have hmk : mkRec (fvar G.length) V = .tRec (fvar G.length) V := by
          simp [mkRec, hu]
        have hRclosed : (ssubst ρ (mkRec (fvar G.length) V)).IsClosed := by
          apply ssubst_closed
          · exact EnvCoOK_env_closed hEnv
          · intro y hy
            obtain ⟨hyV, hyne⟩ := fv_mkRec hy
            have hHWF : H.WellFormed := SessionType.wellFormedUnfold hA hS
            have hFWF := fmon_wf hsub hHWF
            have hmem : y ∈ _ := hFWF.2.2 y hyV
            simp only [List.map_cons, List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact absurd rfl hyne
            · exact EnvCoOK_defined hEnv hmem
        -- New env for spine.
        have hEnv' : EnvCoOK _ ((SessionType.tRec X B, fvar G.length) :: G)
            ((fvar G.length, ssubst ρ (mkRec (fvar G.length) V)) :: ρ) :=
          EnvCoOK.cons hEnv hA hGnames hS hNF hsub rfl rfl rfl
        have hGnames' : GNames ((SessionType.tRec X B, fvar G.length) :: G) :=
          GNames_push _ hGnames
        -- `subst` equals `ssubst` (direct, with `R`).
        have heq : substSessionType (ssubst (eremove (fvar G.length) ρ) V)
            (fvar G.length) (ssubst ρ (mkRec (fvar G.length) V)) =
            ssubst ((fvar G.length, ssubst ρ (mkRec (fvar G.length) V)) :: ρ) V :=
          subst_ssubst_cons V ρ (fvar G.length) _ (EnvCoOK_env_closed hEnv) hRclosed
        -- Target is `tRec` (via `hmk` + `ssubst` unfolding).
        have hRtRec : ssubst ρ (mkRec (fvar G.length) V) =
            SessionType.tRec (fvar G.length) (ssubst (eremove (fvar G.length) ρ) V) := by
          simp [ssubst, hmk]
        -- `recR` with `Y = u`, `C = ssubst (eremove u ρ) V`.
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨fvar G.length,
          ssubst (eremove (fvar G.length) ρ) V, hA, ?_, hRtRec⟩)))
        · -- Spine for `(A, g, subst C Y (tRec Y C))` with new `G',ρ'`.
          have hEq : substSessionType (ssubst (eremove (fvar G.length) ρ) V)
              (fvar G.length)
              (SessionType.tRec (fvar G.length) (ssubst (eremove (fvar G.length) ρ) V)) =
              ssubst ((fvar G.length, ssubst ρ (mkRec (fvar G.length) V)) :: ρ) V := by
            rw [← hRtRec]
            exact heq
          right
          exact ⟨SessionType.tRec X B, H,
            ((SessionType.tRec X B, fvar G.length) :: G),
            ((fvar G.length, ssubst ρ (mkRec (fvar G.length) V)) :: ρ),
            V, rfl, rfl, hEq,
            hA, hS, hNF, hGnames', hEnv', hsub⟩
      · -- `u ∉ V.fv`: `R = ssubst ρ V`, already spine, step by `recL`.
        have hmk' : mkRec (fvar G.length) V = V := by
          simp [mkRec, hu]
        -- `R = ssubst ρ V`.
        have hR : ssubst ρ (mkRec (fvar G.length) V) = ssubst ρ V := by
          rw [hmk']
        -- New env (same as `recR` but with `mkRec = V`).
        have hEnv' : EnvCoOK _ ((SessionType.tRec X B, fvar G.length) :: G)
            ((fvar G.length, ssubst ρ (mkRec (fvar G.length) V)) :: ρ) :=
          EnvCoOK.cons hEnv hA hGnames hS hNF hsub rfl rfl rfl
        have hGnames' : GNames ((SessionType.tRec X B, fvar G.length) :: G) :=
          GNames_push _ hGnames
        -- Destructure `hS : UnfoldStar (tRec X B) H` (must be `step`, since
        -- `H` head-normal rules out `refl` as `tRec` isn't head-normal).
        cases hS with
        | refl => cases hNF
        | step h1 h2 =>
      -- `h1 : Unfold1 (tRec X B) _`, so `_ = subst B X (tRec X B)`.
      cases h1
      -- `h2 : UnfoldStar (subst ...) H`.
      -- `ssubst new V = ssubst old V` since `u ∉ V.fv`.
      have hss : ssubst ((fvar G.length, ssubst ρ (mkRec (fvar G.length) V)) :: ρ) V =
          ssubst ρ V := by
        apply ssubst_ext
        intro x hx
        have hne : x ≠ fvar G.length := fun heq => hu (heq ▸ hx)
        have hbeq : (x == fvar G.length) = false := beq_eq_false_iff_ne.mpr hne
        simp [elookup, List.lookup_cons, hbeq]
      -- `R = ssubst old V` via `hmk'` + `hR`.
      have hR' : ssubst ρ (mkRec (fvar G.length) V) = ssubst ρ V := by
        rw [hmk']
      -- Spine already holds; step by `recL`.
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨X, B, hA, ?_, rfl⟩)))
      · right
        have hRW : ssubst ρ (mkRec (fvar G.length) V) = ssubst ((fvar G.length, ssubst ρ (mkRec (fvar G.length) V)) :: ρ) V := hR.trans hss.symm
        exact ⟨_, _, _, _, _, rfl, rfl, hRW,
          SessionType.WellFormed.unfold_single hA, h2, hNF, hGnames', hEnv', hsub⟩
  · cases hS with
    | refl =>
      -- `(U,H) = (H,H)` with `H` head-normal; `fmon` can't be `fm_rec`.
      cases hfmon' with
      | fm_base hb =>
        have hW0 : V0.WellFormed := mon_tr_yes_base_preserves_wf hb hU
        have heqW : ssubst ρ' V0 = V0 := ssubst_closed_id' V0 ρ' hW0.2.1
        rw [heqW]
        exact Or.inl ⟨hU, hb⟩
      | @fm_pfxInt G bs kept q lab S hne hke hno hall hnd hkey hcov hord =>
        refine Or.inr (Or.inl ⟨bs, kept.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ' b.2.2.2),
          q, lab, S, hU, ⟨hne, mapped_kept_ne_nil_int hke⟩, hno, ?hallS, ?hkeyS, ?hcoverS, ?horderS,
          rfl, rfl, ssubst_internalChoice ρ' kept⟩)
        · intro T0 T1' r l s hB hK'
          obtain ⟨T1, rfl, hK⟩ := mem_mapped_int_inv hK'
          have hc := hall T0 T1 r l s hB hK
          cases hc with
          | fc_go hfresh hsub =>
            left
            exact ⟨T0, G', ρ', T1, rfl, rfl, rfl, wf_of_mem_int hU hB, hGnames', hEnv', hsub⟩
          | @fc_fold _ _ _ u hmem =>
            obtain ⟨X, B, H, V, R, G0, ρ0, hT0, hlook, hReq, hEnv0, hG0, hfmon0, hS0, hNF0, hsub0⟩ :=
              EnvCoOK_lookup hEnv' hmem
            have hss : ssubst ρ' (SessionType.tVar u) = R := by
              simp [ssubst, hlook]
            left
            exact ⟨T0, G0, ρ0, mkRec u V, rfl, rfl, hss.trans hReq,
              wf_of_mem_int hU hB, hG0, hEnv0, hfmon0⟩
        · intro r l s T1' hmem'
          obtain ⟨T1, rfl, hmemK⟩ := mem_mapped_int_inv hmem'
          obtain ⟨T0, hmemB, hEx⟩ := hkey r l s T1 hmemK
          obtain ⟨V', hEx'⟩ := hEx
          exact ⟨T0, hmemB, V', hEx'⟩
        · intro r l s T0 hmemB hEx
          obtain ⟨T1, hmemK⟩ := hcov r l s T0 hmemB hEx
          exact ⟨ssubst ρ' T1, List.mem_map.mpr ⟨_, hmemK, rfl⟩⟩
        · rw [kept_mapped_keys_int3]
          exact hord
      | @fm_pfxExt G p bs kept q lab S hne hke hneq hall hnd hkey hcov hord =>
        refine Or.inr (Or.inr (Or.inl ⟨p, bs, kept.map fun b => (b.1, b.2.1, ssubst ρ' b.2.2),
          q, lab, S, hU, ⟨hne, mapped_kept_ne_nil_ext hke⟩, hneq, ?hallES, ?hkeyES, ?hcoverES, ?horderES,
          rfl, rfl, ssubst_externalChoice ρ' p kept⟩))
        · intro T0 T1' l s hB hK'
          obtain ⟨T1, rfl, hK⟩ := mem_mapped_ext_inv hK'
          have hc := hall T0 T1 l s hB hK
          cases hc with
          | fc_go hfresh hsub =>
            left
            exact ⟨T0, G', ρ', T1, rfl, rfl, rfl, wf_of_mem_ext hU hB, hGnames', hEnv', hsub⟩
          | @fc_fold _ _ _ u hmem =>
            obtain ⟨X, B, H, V, R, G0, ρ0, hT0, hlook, hReq, hEnv0, hG0, hfmon0, hS0, hNF0, hsub0⟩ :=
              EnvCoOK_lookup hEnv' hmem
            have hss : ssubst ρ' (SessionType.tVar u) = R := by
              simp [ssubst, hlook]
            left
            exact ⟨T0, G0, ρ0, mkRec u V, rfl, rfl, hss.trans hReq,
              wf_of_mem_ext hU hB, hG0, hEnv0, hfmon0⟩
        · intro l s T1' hmem'
          obtain ⟨T1, rfl, hmemK⟩ := mem_mapped_ext_inv hmem'
          obtain ⟨T0, hmemB, hEx⟩ := hkey l s T1 hmemK
          obtain ⟨V', hEx'⟩ := hEx
          exact ⟨T0, hmemB, V', hEx'⟩
        · intro l s T0 hmemB hEx
          obtain ⟨T1, hmemK⟩ := hcov l s T0 hmemB hEx
          exact ⟨ssubst ρ' T1, List.mem_map.mpr ⟨_, hmemK, rfl⟩⟩
        · rw [kept_mapped_keys_ext2]
          exact hord
      | @fm_rec G X B H _ V hS hNF hsub =>
        cases hNF
    | step h1 h2 =>
      cases h1 with
      | tRec =>
        -- `U = tRec X B`, `U_mid = subst B X (tRec X B)`, `h2 : UnfoldStar U_mid H`.
        -- `U.WF` via `hU`; `U_mid.WF` via `unfold_single`.
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, hU, ?_, rfl⟩)))
        · right
          exact ⟨_, _, _, _, _, rfl, rfl, rfl,
            SessionType.WellFormed.unfold_single hU, h2, hNF, hGnames', hEnv', hfmon'⟩

/-- Branch relation for internal choices (port; see header for credit). -/
def intRel (R : SessionType → SessionType → Prop)
    (x y : Role × Lab × DataSort × SessionType) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧ R x.2.2.2 y.2.2.2

/-- Branch relation for external choices (port; see header for credit). -/
def extRel (R : SessionType → SessionType → Prop)
    (x y : Lab × DataSort × SessionType) : Prop :=
  x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ R x.2.2 y.2.2

/-- Shape equality at head (port; see header for credit). -/
def shapeEq (R : SessionType → SessionType → Prop) : SessionType → SessionType → Prop
  | .tEnd, .tEnd => True
  | .internalChoice bs, .internalChoice cs => List.Forall₂ (intRel R) bs cs
  | .externalChoice p bs, .externalChoice q cs => p = q ∧ List.Forall₂ (extRel R) bs cs
  | _, _ => False

/-- Stratified tree equivalence, depth `n` (port; see header for credit). -/
def teqN : Nat → SessionType → SessionType → Prop
  | 0, _, _ => True
  | n + 1, T, U => ∃ H HU, hnf T H ∧ hnf U HU ∧ shapeEq (teqN n) H HU

/-- Equality of all finite unfoldings (port; see header for credit). -/
def Eqv (T U : SessionType) : Prop := ∀ n, teqN n T U

/-- `hnf` through `tRec` (see header). -/
theorem hnf_rec_iff' {X : String} {B H : SessionType} :
    hnf (.tRec X B) H ↔ hnf (substSessionType B X (.tRec X B)) H := by
  constructor
  · rintro ⟨steps, normal⟩
    cases steps with
    | refl => exact False.elim normal
    | step first rest => cases first; exact ⟨rest, normal⟩
  · rintro ⟨steps, normal⟩
    exact ⟨.step .tRec steps, normal⟩

/-- `Forall₂` congruence (see header). -/
theorem Forall2_impl {A B : Type} {P Q : A → B → Prop} {xs : List A} {ys : List B}
    (change : ∀ x ∈ xs, ∀ y ∈ ys, P x y → Q x y) (pairs : List.Forall₂ P xs ys) :
    List.Forall₂ Q xs ys := by
  induction pairs with
  | nil => exact .nil
  | cons first rest ih =>
      exact .cons (change _ (by simp) _ (by simp) first)
        (ih (fun x hx y hy => change x (by simp [hx]) y (by simp [hy])))

/-- `Forall₂` reflexivity (port; see header). -/
theorem Forall2_diag {A : Type} {P : A → A → Prop} (xs : List A)
    (each : ∀ x ∈ xs, P x x) : List.Forall₂ P xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (each _ (by simp)) (ih (fun y hy => each y (by simp [hy])))

/-- `Forall₂` symmetry (port; see header). -/
theorem Forall2_sym {A B : Type} {P : A → B → Prop} {Q : B → A → Prop}
    {xs : List A} {ys : List B} (flip : ∀ x y, P x y → Q y x)
    (pairs : List.Forall₂ P xs ys) : List.Forall₂ Q ys xs := by
  induction pairs with
  | nil => exact .nil
  | cons first rest ih => exact .cons (flip _ _ first) ih

/-- `Forall₂` transitivity (port; see header). -/
theorem Forall2_trans {A B C : Type} {P : A → B → Prop} {Q : B → C → Prop}
    {R : A → C → Prop} {xs : List A} {ys : List B} {zs : List C}
    (compose : ∀ x y z, P x y → Q y z → R x z)
    (first : List.Forall₂ P xs ys) (second : List.Forall₂ Q ys zs) : List.Forall₂ R xs zs := by
  induction first generalizing zs with
  | nil => cases second; exact .nil
  | cons first rest ih => cases second with
    | cons second tail => exact .cons (compose _ _ _ first second) (ih tail)

/-- `Forall₂` for all `n` (port; see header). -/
theorem Forall2_forall {A B : Type} {P : Nat → A → B → Prop} {xs : List A} {ys : List B}
    (all : ∀ n, List.Forall₂ (P n) xs ys) : List.Forall₂ (fun x y => ∀ n, P n x y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact .nil
    | cons y ys => cases all 0
  | cons x xs ih =>
    cases ys with
    | nil => cases all 0
    | cons y ys =>
      exact .cons (fun n => (List.forall₂_cons.mp (all n)).1)
        (ih (fun n => (List.forall₂_cons.mp (all n)).2))

/-- `shapeEq` congruence (port; see header). -/
theorem shapeEq_impl {R S : SessionType → SessionType → Prop} {H K : SessionType}
    (change : ∀ T U, R T U → S T U) (same : shapeEq R H K) : shapeEq S H K := by
  cases H <;> cases K <;> simp only [shapeEq] at same ⊢ <;> try contradiction
  · exact Forall2_impl (fun x _ y _ h => ⟨h.1, h.2.1, h.2.2.1, change _ _ h.2.2.2⟩) same
  · exact ⟨same.1, Forall2_impl (fun x _ y _ h => ⟨h.1, h.2.1, change _ _ h.2.2⟩) same.2⟩

/-- `shapeEq` symmetry (port; see header). -/
theorem shapeEq_sym {R : SessionType → SessionType → Prop} {H K : SessionType}
    (flip : ∀ T U, R T U → R U T) (same : shapeEq R H K) : shapeEq R K H := by
  cases H <;> cases K <;> simp only [shapeEq] at same ⊢ <;> try contradiction
  · exact Forall2_sym (fun x y h => ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, flip _ _ h.2.2.2⟩) same
  · exact ⟨same.1.symm, Forall2_sym (fun x y h => ⟨h.1.symm, h.2.1.symm, flip _ _ h.2.2⟩) same.2⟩

/-- `shapeEq` transitivity (port; see header). -/
theorem shapeEq_trans {R : SessionType → SessionType → Prop} {H K L : SessionType}
    (compose : ∀ T U V, R T U → R U V → R T V)
    (first : shapeEq R H K) (second : shapeEq R K L) : shapeEq R H L := by
  cases H <;> cases K <;> cases L <;> simp only [shapeEq] at first second ⊢ <;> try contradiction
  · exact Forall2_trans (fun x y z h k =>
      ⟨h.1.trans k.1, h.2.1.trans k.2.1, h.2.2.1.trans k.2.2.1, compose _ _ _ h.2.2.2 k.2.2.2⟩) first second
  · exact ⟨first.1.trans second.1, Forall2_trans (fun x y z h k =>
      ⟨h.1.trans k.1, h.2.1.trans k.2.1, compose _ _ _ h.2.2 k.2.2⟩) first.2 second.2⟩

theorem teqN_mono {n m : Nat} {T U : SessionType} (le : m ≤ n)
    (same : teqN n T U) : teqN m T U := by
  induction n generalizing m T U with
  | zero =>
      have : m = 0 := by omega
      subst m
      trivial
  | succ n ih =>
    cases m with
    | zero => trivial
    | succ m =>
      obtain ⟨H, K, ht, hu, shape⟩ := same
      exact ⟨H, K, ht, hu, shapeEq_impl (fun _ _ h => ih (by omega) h) shape⟩

theorem teqN_unfold_l (n : Nat) {X : String} {B U : SessionType} :
    teqN n (.tRec X B) U ↔ teqN n (substSessionType B X (.tRec X B)) U := by
  cases n with
  | zero => rfl
  | succ n => simp only [teqN, hnf_rec_iff']

theorem teqN_unfold_r (n : Nat) {X : String} {B T : SessionType} :
    teqN n T (.tRec X B) ↔ teqN n T (substSessionType B X (.tRec X B)) := by
  cases n with
  | zero => rfl
  | succ n => simp only [teqN, hnf_rec_iff']

theorem teqN_refl (n : Nat) {T : SessionType} (wf : T.WellFormed) : teqN n T T := by
  induction n generalizing T with
  | zero => trivial
  | succ n ih =>
    obtain ⟨H, hhead⟩ : ∃ H, hnf T H := ⟨head T, head_correct wf⟩
    have hw : H.WellFormed := SessionType.wellFormedUnfold wf hhead.1
    refine ⟨H, H, hhead, hhead, ?_⟩
    cases H with
    | tEnd => trivial
    | tVar name => have closed := hw.2.1; simp [SessionType.IsClosed, SessionType.fv] at closed
    | tRec name body => exact False.elim hhead.2
    | internalChoice bs =>
        exact Forall2_diag bs (fun x hx => ⟨rfl, rfl, rfl, ih (wf_of_mem_int hw hx)⟩)
    | externalChoice p bs =>
        exact ⟨rfl, Forall2_diag bs (fun x hx => ⟨rfl, rfl, ih (wf_of_mem_ext hw hx)⟩)⟩

theorem teqN_sym (n : Nat) {T U : SessionType} (same : teqN n T U) : teqN n U T := by
  induction n generalizing T U with
  | zero => trivial
  | succ n ih =>
    obtain ⟨H, K, ht, hu, shape⟩ := same
    exact ⟨K, H, hu, ht, shapeEq_sym (fun _ _ h => ih h) shape⟩

theorem teqN_trans (n : Nat) {T U V : SessionType}
    (first : teqN n T U) (second : teqN n U V) : teqN n T V := by
  induction n generalizing T U V with
  | zero => trivial
  | succ n ih =>
    obtain ⟨H, K, ht, hu, shape⟩ := first
    obtain ⟨K', L, hu', hv, shape'⟩ := second
    have : K' = K := hnf_unique hu' hu
    subst K'
    exact ⟨H, L, ht, hv, shapeEq_trans (fun _ _ _ h k => ih h k) shape shape'⟩

theorem Eqv_refl {T : SessionType} (wf : T.WellFormed) : Eqv T T := fun n => teqN_refl n wf

theorem Eqv_sym {T U : SessionType} (same : Eqv T U) : Eqv U T := fun n => teqN_sym n (same n)

theorem Eqv_trans {T U V : SessionType} (first : Eqv T U) (second : Eqv U V) : Eqv T V :=
  fun n => teqN_trans n (first n) (second n)

theorem Eqv_shape {T U H K : SessionType} (same : Eqv T U)
    (ht : hnf T H) (hu : hnf U K) : shapeEq Eqv H K := by
  have all : ∀ n, shapeEq (teqN n) H K := by
    intro n
    obtain ⟨H', K', ht', hu', shape⟩ := same (n + 1)
    have : H' = H := hnf_unique ht' ht
    subst H'
    have : K' = K := hnf_unique hu' hu
    subst K'
    exact shape
  cases H <;> cases K <;> simp only [shapeEq] at all ⊢ <;> try exact False.elim (all 0)
  · exact Forall2_impl (fun x _ y _ h => ⟨(h 0).1, (h 0).2.1, (h 0).2.2.1, fun n => (h n).2.2.2⟩)
      (Forall2_forall all)
  · exact ⟨(all 0).1, Forall2_impl (fun x _ y _ h => ⟨(h 0).1, (h 0).2.1, fun n => (h n).2.2⟩)
      (Forall2_forall (fun n => (all n).2))⟩

/-- Aligned internal branches (port; see header for credit). -/
abbrev alignInt (R : SessionType → SessionType → Prop) := List.Forall₂ (intRel R)

/-- Aligned external branches (port; see header for credit). -/
abbrev alignExt (R : SessionType → SessionType → Prop) := List.Forall₂ (extRel R)

theorem alignInt_mem {Q : SessionType → SessionType → Prop}
    {bs cs : List (Role × Lab × DataSort × SessionType)} {p : Role} {l : Lab} {s : DataSort}
    {T : SessionType} (aligned : alignInt Q bs cs) (member : (p, l, s, T) ∈ bs) :
    ∃ U, (p, l, s, U) ∈ cs ∧ Q T U := by
  induction aligned with
  | nil => cases member
  | @cons x y xs ys same rest ih =>
      rcases x with ⟨p₀, l₀, s₀, T₀⟩
      rcases y with ⟨p₁, l₁, s₁, T₁⟩
      rcases same with ⟨rfl, rfl, rfl, next⟩
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact ⟨T₁, List.mem_cons_self, next⟩
      · obtain ⟨U, member', next⟩ := ih member
        exact ⟨U, List.mem_cons_of_mem _ member', next⟩

theorem alignExt_mem {Q : SessionType → SessionType → Prop}
    {bs cs : List (Lab × DataSort × SessionType)} {l : Lab} {s : DataSort}
    {T : SessionType} (aligned : alignExt Q bs cs) (member : (l, s, T) ∈ bs) :
    ∃ U, (l, s, U) ∈ cs ∧ Q T U := by
  induction aligned with
  | nil => cases member
  | @cons x y xs ys same rest ih =>
      rcases x with ⟨l₀, s₀, T₀⟩
      rcases y with ⟨l₁, s₁, T₁⟩
      rcases same with ⟨rfl, rfl, next⟩
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact ⟨T₁, List.mem_cons_self, next⟩
      · obtain ⟨U, member', next⟩ := ih member
        exact ⟨U, List.mem_cons_of_mem _ member', next⟩

theorem alignInt_keys {Q : SessionType → SessionType → Prop}
    {bs cs : List (Role × Lab × DataSort × SessionType)} (aligned : alignInt Q bs cs) :
    bs.map (fun b => (b.1, b.2.1, b.2.2.1)) = cs.map (fun b => (b.1, b.2.1, b.2.2.1)) := by
  induction aligned with
  | nil => rfl
  | cons first rest ih => simp [first.1, first.2.1, first.2.2.1, ih]

theorem alignExt_keys {Q : SessionType → SessionType → Prop}
    {bs cs : List (Lab × DataSort × SessionType)} (aligned : alignExt Q bs cs) :
    bs.map (fun b => (b.1, b.2.1)) = cs.map (fun b => (b.1, b.2.1)) := by
  induction aligned with
  | nil => rfl
  | cons first rest ih => simp [first.1, first.2.1, ih]

/-- Zip membership projects to left membership (port; helper for `eqv_implies`). -/
theorem mem_zip_fst {A B : Type} {l1 : List A} {l2 : List B} {a : A} {b : B}
    (hmem : (a, b) ∈ l1.zip l2) : a ∈ l1 := by
  induction l1 generalizing l2 with
  | nil => simp at hmem
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hmem
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hmem)

/-- Zip membership projects to right membership (port; helper). -/
theorem mem_zip_snd {A B : Type} {l1 : List A} {l2 : List B} {a : A} {b : B}
    (hmem : (a, b) ∈ l1.zip l2) : b ∈ l2 := by
  induction l1 generalizing l2 with
  | nil => simp at hmem
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hmem
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hmem)

theorem eqv_implies_unfoldEquiv {T U : SessionType}
    (hT : T.WellFormed) (hU : U.WellFormed) (h : Eqv T U) :
    T.UnfoldEquiv U := by
  refine SessionType.UnfoldEquiv.coinduct
    (fun A B => A.WellFormed ∧ B.WellFormed ∧ Eqv A B) ?_ T U ⟨hT, hU, h⟩
  intro A B ⟨hA, hB, hEqv⟩
  cases A with
  | tRec X B0 =>
    -- `A = tRec`, step by `recL`.
    have hAunfold : (substSessionType B0 X (SessionType.tRec X B0)).WellFormed :=
      SessionType.WellFormed.unfold_single hA
    have hEqv' : Eqv (substSessionType B0 X (SessionType.tRec X B0)) B :=
      fun n => (teqN_unfold_l n).mp (hEqv n)
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨X, B0, ⟨hAunfold, hB, hEqv'⟩, rfl⟩))))
  | tEnd =>
    cases B with
    | tRec Y C0 =>
      -- `B = tRec`, step by `recR`.
      have hBunfold : (substSessionType C0 Y (SessionType.tRec Y C0)).WellFormed :=
        SessionType.WellFormed.unfold_single hB
      have hEqv' : Eqv _ (substSessionType C0 Y (SessionType.tRec Y C0)) :=
        fun n => (teqN_unfold_r n).mp (hEqv n)
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Y, C0, ⟨hA, hBunfold, hEqv'⟩, rfl⟩))))
    | tEnd =>
      -- Both `tEnd`: `UnfoldEquiv.end` via `Eqv_shape` (must be `tEnd/tEnd`).
      exact Or.inl ⟨rfl, rfl⟩
    | tVar Y =>
      -- `B = tVar` impossible (closed).
      have hCl := hB.2.1
      simp [SessionType.IsClosed, SessionType.fv] at hCl
    | internalChoice bs =>
      -- Mismatch `tEnd` vs `internalChoice`: impossible via `Eqv_shape`.
      have hShape := Eqv_shape hEqv (hnf_self trivial) (hnf_self trivial)
      simp [shapeEq] at hShape
    | externalChoice p bs =>
      have hShape := Eqv_shape hEqv (hnf_self trivial) (hnf_self trivial)
      simp [shapeEq] at hShape
  | tVar X =>
    have hCl := hA.2.1
    simp [SessionType.IsClosed, SessionType.fv] at hCl
  | internalChoice bs =>
    cases B with
    | tRec Y C0 =>
      have hBunfold : (substSessionType C0 Y (SessionType.tRec Y C0)).WellFormed :=
        SessionType.WellFormed.unfold_single hB
      have hEqv' : Eqv _ (substSessionType C0 Y (SessionType.tRec Y C0)) :=
        fun n => (teqN_unfold_r n).mp (hEqv n)
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Y, C0, ⟨hA, hBunfold, hEqv'⟩, rfl⟩))))
    | tEnd =>
      have hShape := Eqv_shape hEqv (hnf_self trivial) (hnf_self trivial)
      simp [shapeEq] at hShape
    | tVar Y =>
      have hCl := hB.2.1
      simp [SessionType.IsClosed, SessionType.fv] at hCl
    | internalChoice cs =>
      -- Matching `int/int`: `UnfoldEquiv.intC` via `alignInt_keys` + zip bridge.
      have haligned : alignInt Eqv bs cs :=
        Eqv_shape hEqv (hnf_self trivial) (hnf_self trivial)
      have hkeys := alignInt_keys haligned
      refine Or.inr (Or.inr (Or.inl ⟨bs, cs, hkeys, ?_, rfl, rfl⟩))
      · intro a b hmem
        have hmemA : a ∈ bs := mem_zip_fst hmem
        have hmemB : b ∈ cs := mem_zip_snd hmem
        have hrel : intRel Eqv a b :=
          (List.forall₂_iff_zip.mp haligned).2 hmem
        exact ⟨wf_of_mem_int hA hmemA, wf_of_mem_int hB hmemB, hrel.2.2.2⟩
    | externalChoice _ _ =>
      have hShape := Eqv_shape hEqv (hnf_self trivial) (hnf_self trivial)
      simp [shapeEq] at hShape
  | externalChoice p bs =>
    cases B with
    | tRec Y C0 =>
      have hBunfold : (substSessionType C0 Y (SessionType.tRec Y C0)).WellFormed :=
        SessionType.WellFormed.unfold_single hB
      have hEqv' : Eqv _ (substSessionType C0 Y (SessionType.tRec Y C0)) :=
        fun n => (teqN_unfold_r n).mp (hEqv n)
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Y, C0, ⟨hA, hBunfold, hEqv'⟩, rfl⟩))))
    | tEnd =>
      have hShape := Eqv_shape hEqv (hnf_self trivial) (hnf_self trivial)
      simp [shapeEq] at hShape
    | tVar Y =>
      have hCl := hB.2.1
      simp [SessionType.IsClosed, SessionType.fv] at hCl
    | internalChoice _ =>
      have hShape := Eqv_shape hEqv (hnf_self trivial) (hnf_self trivial)
      simp [shapeEq] at hShape
    | externalChoice q cs =>
      -- Matching `ext/ext`: `UnfoldEquiv.extC` via `alignExt_keys` + zip bridge.
      have hShape := Eqv_shape hEqv (hnf_self trivial) (hnf_self trivial)
      have hpeq : p = q := hShape.1
      subst hpeq
      have haligned : alignExt Eqv bs cs := hShape.2
      have hkeys := alignExt_keys haligned
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨p, bs, cs, hkeys, ?_, rfl, rfl⟩)))
      · intro a b hmem
        have hmemA : a ∈ bs := mem_zip_fst hmem
        have hmemB : b ∈ cs := mem_zip_snd hmem
        have hrel : extRel Eqv a b :=
          (List.forall₂_iff_zip.mp haligned).2 hmem
        exact ⟨wf_of_mem_ext hA hmemA, wf_of_mem_ext hB hmemB, hrel.2.2⟩

/-- Base unfolds through `tRec` (port; see header). -/
theorem base_rec_iff {X : String} {B V : SessionType} {g : ext_tag} :
    mon_tr_yes_base (.tRec X B) g V ↔ mon_tr_yes_base (substSessionType B X (.tRec X B)) g V := by
  exact ⟨fun h => by cases h with | tRec next => exact next, mon_tr_yes_base.tRec⟩

/-- Prefix step (see header). -/

-- Uses `hnf_rec_iff` (as `hnf_rec_iff'`) for `PruneN_unfold_*` below.
def PfxStep (P : SessionType → SessionType → Prop) (g : ext_tag) :
    SessionType → SessionType → Prop
  | .internalChoice bs, .internalChoice kept =>
      match g with
      | .recv q _ _ => bs ≠ [] ∧ kept ≠ [] ∧
          (∀ p l s T, (p, l, s, T) ∈ bs → q ≠ p) ∧ KRint (fun T => Ex T g) P bs kept
      | _ => False
  | .externalChoice p bs, .externalChoice q kept =>
      match g with
      | .recv r _ _ => q = p ∧ r ≠ p ∧ bs ≠ [] ∧ kept ≠ [] ∧ KRext (fun T => Ex T g) P bs kept
      | _ => False
  | _, _ => False

/-- Stratified pruning (port; see header). -/
def PruneN : Nat → ext_tag → SessionType → SessionType → Prop
  | 0, _, _, _ => True
  | n + 1, g, T, R =>
      (∃ U, mon_tr_yes_base T g U ∧ teqN (n + 1) U R) ∨
      (∃ H HR, hnf T H ∧ hnf R HR ∧ PfxStep (PruneN n g) g H HR)

/-- Pruning (all finite unfoldings; port; see header). -/
def Prune (g : ext_tag) (T R : SessionType) : Prop := ∀ n, PruneN n g T R

/-- `KRint` congruence (see header). -/
theorem KRint_impl {E E' : SessionType → Prop} {P P' : SessionType → SessionType → Prop}
    {bs kept : List (Role × Lab × DataSort × SessionType)}
    (eligibility : ∀ p l s T, (p, l, s, T) ∈ bs → (E T ↔ E' T))
    (targets : ∀ p l s T U, (p, l, s, T) ∈ bs → P T U → P' T U)
    (pruned : KRint E P bs kept) : KRint E' P' bs kept := by
  induction pruned with
  | nil => exact .nil
  | keep eligible next rest ih =>
      exact .keep ((eligibility _ _ _ _ List.mem_cons_self).mp eligible)
        (targets _ _ _ _ _ List.mem_cons_self next)
        (ih (fun p l s T member => eligibility p l s T (by simp [member]))
          (fun p l s T U member => targets p l s T U (by simp [member])))
  | drop ineligible rest ih =>
      exact .drop (fun eligible => ineligible ((eligibility _ _ _ _ List.mem_cons_self).mpr eligible))
        (ih (fun p l s T member => eligibility p l s T (by simp [member]))
          (fun p l s T U member => targets p l s T U (by simp [member])))

/-- `KRext` congruence (port; see header). -/
theorem KRext_impl {E E' : SessionType → Prop} {P P' : SessionType → SessionType → Prop}
    {bs kept : List (Lab × DataSort × SessionType)}
    (eligibility : ∀ l s T, (l, s, T) ∈ bs → (E T ↔ E' T))
    (targets : ∀ l s T U, (l, s, T) ∈ bs → P T U → P' T U)
    (pruned : KRext E P bs kept) : KRext E' P' bs kept := by
  induction pruned with
  | nil => exact .nil
  | keep eligible next rest ih =>
      exact .keep ((eligibility _ _ _ List.mem_cons_self).mp eligible)
        (targets _ _ _ _ List.mem_cons_self next)
        (ih (fun l s T member => eligibility l s T (by simp [member]))
          (fun l s T U member => targets l s T U (by simp [member])))
  | drop ineligible rest ih =>
      exact .drop (fun eligible => ineligible ((eligibility _ _ _ List.mem_cons_self).mpr eligible))
        (ih (fun l s T member => eligibility l s T (by simp [member]))
          (fun l s T U member => targets l s T U (by simp [member])))

/-- `PfxStep` congruence (port; see header). -/
theorem PfxStep_impl {P Q : SessionType → SessionType → Prop} {g : ext_tag} {H R : SessionType}
    (change : ∀ T U, P T U → Q T U) (pruned : PfxStep P g H R) : PfxStep Q g H R := by
  cases g <;> cases H <;> cases R <;> simp only [PfxStep] at pruned ⊢ <;> try contradiction
  · exact ⟨pruned.1, pruned.2.1, pruned.2.2.1,
      KRint_impl (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ _ => change _ _) pruned.2.2.2⟩
  · exact ⟨pruned.1, pruned.2.1, pruned.2.2.1, pruned.2.2.2.1,
      KRext_impl (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => change _ _) pruned.2.2.2.2⟩

/-- `PruneN` mono (port; see header). -/
theorem PruneN_mono {n m : Nat} {g : ext_tag} {T R : SessionType}
    (le : m ≤ n) (pruned : PruneN n g T R) : PruneN m g T R := by
  induction n generalizing m T R with
  | zero =>
      have : m = 0 := by omega
      subst m
      trivial
  | succ n ih =>
      cases m with
      | zero => trivial
      | succ m =>
        rcases pruned with ⟨U, base, same⟩ | ⟨H, HR, head, residual, prefixStep⟩
        · exact .inl ⟨U, base, teqN_mono le same⟩
        · exact .inr ⟨H, HR, head, residual, PfxStep_impl (fun _ _ h => ih (by omega) h) prefixStep⟩

/-- `PruneN` through `tRec` left (port; see header; uses `hnf_rec_iff'`). -/
theorem PruneN_unfold_l (n : Nat) {g : ext_tag} {X : String} {B R : SessionType} :
    PruneN n g (.tRec X B) R ↔ PruneN n g (substSessionType B X (.tRec X B)) R := by
  cases n with
  | zero => rfl
  | succ n => simp only [PruneN, base_rec_iff, hnf_rec_iff']

/-- `PruneN` through `tRec` right (port; see header). -/
theorem PruneN_unfold_r (n : Nat) {g : ext_tag} {X : String} {B T : SessionType} :
    PruneN n g T (.tRec X B) ↔ PruneN n g T (substSessionType B X (.tRec X B)) := by
  cases n with
  | zero => rfl
  | succ n => simp only [PruneN, teqN_unfold_r, hnf_rec_iff']

/-- `PruneN` through `UnfoldStar` left (port; see header). -/
theorem PruneN_unfoldstar_l (n : Nat) {g : ext_tag} {T U R : SessionType}
    (steps : UnfoldStar T U) : PruneN n g T R ↔ PruneN n g U R := by
  induction steps with
  | refl => rfl
  | step first rest ih => cases first; exact (PruneN_unfold_l n).trans ih

/-- Internal/external branch abbreviations (see header). -/
abbrev IntBranch := Role × Lab × DataSort × SessionType

abbrev ExtBranch := Lab × DataSort × SessionType

/-- `KRint` post-composition (port; see header). -/
theorem KRint_right {E : SessionType → Prop} {P Q : SessionType → SessionType → Prop}
    {bs kept kept' : List IntBranch} (pruned : KRint E P bs kept)
    (aligned : alignInt Q kept kept') :
    KRint E (fun T V => ∃ U, P T U ∧ Q U V) bs kept' := by
  induction pruned generalizing kept' with
  | nil => cases aligned; exact .nil
  | keep eligible next rest ih =>
      cases aligned with
      | cons same tail =>
        rename_i y ys
        rcases y with ⟨p, l, s, U⟩
        rcases same with ⟨rfl, rfl, rfl, hq⟩
        exact .keep eligible ⟨_, next, hq⟩ (ih tail)
  | drop ineligible rest ih => exact .drop ineligible (ih aligned)

/-- `KRext` post-composition (port; see header). -/
theorem KRext_right {E : SessionType → Prop} {P Q : SessionType → SessionType → Prop}
    {bs kept kept' : List ExtBranch} (pruned : KRext E P bs kept)
    (aligned : alignExt Q kept kept') :
    KRext E (fun T V => ∃ U, P T U ∧ Q U V) bs kept' := by
  induction pruned generalizing kept' with
  | nil => cases aligned; exact .nil
  | keep eligible next rest ih =>
      cases aligned with
      | cons same tail =>
        rename_i y ys
        rcases y with ⟨l, s, U⟩
        rcases same with ⟨rfl, rfl, hq⟩
        exact .keep eligible ⟨_, next, hq⟩ (ih tail)
  | drop ineligible rest ih => exact .drop ineligible (ih aligned)

/-- `KRint` functionality (port; see header). -/
theorem KRint_func {E : SessionType → Prop} {P Q : SessionType → SessionType → Prop}
    {bs first second : List IntBranch} (left : KRint E P bs first) (right : KRint E Q bs second) :
    List.Forall₂ (fun x y : IntBranch => x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2.1 = y.2.2.1 ∧
      ∃ T, (x.1, x.2.1, x.2.2.1, T) ∈ bs ∧ P T x.2.2.2 ∧ Q T y.2.2.2) first second := by
  induction left generalizing second with
  | nil => cases right; exact .nil
  | keep eligible next rest ih =>
      cases right with
      | keep eligible' next' rest' =>
          exact .cons ⟨rfl, rfl, rfl, _, List.mem_cons_self, next, next'⟩
            (Forall2_impl (fun x _ y _ h => by
              obtain ⟨hp, hl, hs, T, member, first, second⟩ := h
              exact ⟨hp, hl, hs, T, List.mem_cons_of_mem _ member, first, second⟩) (ih rest'))
      | drop ineligible rest' => exact False.elim (ineligible eligible)
    | drop ineligible rest ih =>
      cases right with
      | keep eligible next' rest' => exact False.elim (ineligible eligible)
      | drop ineligible' rest' =>
          exact Forall2_impl (fun x _ y _ h => by
              obtain ⟨hp, hl, hs, T, member, first, second⟩ := h
              exact ⟨hp, hl, hs, T, List.mem_cons_of_mem _ member, first, second⟩) (ih rest')

/-- `KRext` functionality (port; see header). -/
theorem KRext_func {E : SessionType → Prop} {P Q : SessionType → SessionType → Prop}
    {bs first second : List ExtBranch} (left : KRext E P bs first) (right : KRext E Q bs second) :
    List.Forall₂ (fun x y : ExtBranch => x.1 = y.1 ∧ x.2.1 = y.2.1 ∧
      ∃ T, (x.1, x.2.1, T) ∈ bs ∧ P T x.2.2 ∧ Q T y.2.2) first second := by
  induction left generalizing second with
  | nil => cases right; exact .nil
  | keep eligible next rest ih =>
      cases right with
      | keep eligible' next' rest' =>
          exact .cons ⟨rfl, rfl, _, List.mem_cons_self, next, next'⟩
            (Forall2_impl (fun x _ y _ h => by
              obtain ⟨hp, hl, T, member, first, second⟩ := h
              exact ⟨hp, hl, T, List.mem_cons_of_mem _ member, first, second⟩) (ih rest'))
      | drop ineligible rest' => exact False.elim (ineligible eligible)
  | drop ineligible rest ih =>
      cases right with
      | keep eligible next' rest' => exact False.elim (ineligible eligible)
      | drop ineligible' rest' =>
          exact Forall2_impl (fun x _ y _ h => by
              obtain ⟨hp, hl, T, member, first, second⟩ := h
              exact ⟨hp, hl, T, List.mem_cons_of_mem _ member, first, second⟩) (ih rest')

/-- Nonempty left implies nonempty right for `Forall₂` (port; see header). -/
theorem Forall2_nil_r {A B : Type} {P : A → B → Prop} {xs : List A} {ys : List B}
    (pairs : List.Forall₂ P xs ys) (nonempty : xs ≠ []) : ys ≠ [] := by
  intro empty
  subst ys
  cases pairs
  exact nonempty rfl

/-- Base and prefix are exclusive (port; see header; uses `base_hnf`, `hnf_unique`). -/
theorem base_pfx_exclusive {T U H R : SessionType} {g : ext_tag}
    {P : SessionType → SessionType → Prop} (base : mon_tr_yes_base T g U)
    (head : hnf T H) (next : PfxStep P g H R) : False := by
  obtain ⟨H', head', direct⟩ := base_hnf base
  have equal := hnf_unique head' head
  subst H'
  cases g <;> cases H <;> cases R <;> (simp only [base_direct, PfxStep] at direct next; try contradiction)
  exact next.2.1 direct.1.symm

/-- `PruneN` determinism (port; see header). -/
theorem PruneN_unique (n : Nat) {g : ext_tag} {T R S : SessionType}
    (wf : T.WellFormed) (first : PruneN n g T R) (second : PruneN n g T S) : teqN n R S := by
  induction n generalizing T R S with
  | zero => trivial
  | succ n ih =>
      rcases first with ⟨U, base, same⟩ | ⟨H, HR, head, residual, next⟩
      · rcases second with ⟨V, base', same'⟩ | ⟨H, HS, head, residual, next⟩
        · have equal := mon_tr_yes_base_target_unique base base'
          subst V
          exact teqN_trans (n + 1) (teqN_sym (n + 1) same) same'
        · exact False.elim (base_pfx_exclusive base head next)
      · rcases second with ⟨V, base', same'⟩ | ⟨H', HS, head', residual', next'⟩
        · exact False.elim (base_pfx_exclusive base' head next)
        · have equal := hnf_unique head' head
          subst H'
          have hw := SessionType.wellFormedUnfold wf head.1
          refine ⟨HR, HS, residual, residual', ?_⟩
          cases g <;> cases H <;> cases HR <;>
            simp only [PfxStep] at next ⊢ <;> try contradiction
          all_goals cases HS <;> (simp only [PfxStep] at next'; try contradiction)
          · exact Forall2_impl (fun x _ y _ h => by
              obtain ⟨hp, hl, hs, U, member, a, b⟩ := h
              exact ⟨hp, hl, hs, ih (wf_of_mem_int hw member) a b⟩)
                (KRint_func next.2.2.2 next'.2.2.2)
          · obtain ⟨rfl, _, _, _, first⟩ := next
            obtain ⟨rfl, _, _, _, second⟩ := next'
            exact ⟨rfl, Forall2_impl (fun x _ y _ h => by
              obtain ⟨hl, hs, U, member, a, b⟩ := h
              exact ⟨hl, hs, ih (wf_of_mem_ext hw member) a b⟩)
                (KRext_func first second)⟩

/-- `Prune` determinism (port; see header). -/
theorem Prune_unique {g : ext_tag} {T R S : SessionType}
    (wf : T.WellFormed) (first : Prune g T R) (second : Prune g T S) : Eqv R S :=
  fun n => PruneN_unique n wf (first n) (second n)

/-- Nonempty kept lists retain an eligible source (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem KRint_some_kept {E : SessionType → Prop} {P : SessionType → SessionType → Prop}
    {bs kept : List (Role × Lab × DataSort × SessionType)}
    (pruned : KRint E P bs kept) (nonempty : kept ≠ []) :
    ∃ p l s T, (p, l, s, T) ∈ bs ∧ E T := by
  induction pruned with
  | nil => exact False.elim (nonempty rfl)
  | keep eligible next rest ih => exact ⟨_, _, _, _, List.mem_cons_self, eligible⟩
  | drop ineligible rest ih =>
      obtain ⟨p, l, s, T, member, eligible⟩ := ih nonempty
      exact ⟨p, l, s, T, List.mem_cons_of_mem _ member, eligible⟩

/-- Nonempty kept ext lists retain an eligible source (port; cf. `KRint_some_kept`). -/
theorem KRext_some_kept {E : SessionType → Prop} {P : SessionType → SessionType → Prop}
    {bs kept : List (Lab × DataSort × SessionType)}
    (pruned : KRext E P bs kept) (nonempty : kept ≠ []) :
    ∃ l s T, (l, s, T) ∈ bs ∧ E T := by
  induction pruned with
  | nil => exact False.elim (nonempty rfl)
  | keep eligible _ _ ih => exact ⟨_, _, _, List.mem_cons_self, eligible⟩
  | drop _ _ ih =>
    obtain ⟨l, s, T, member, eligible⟩ := ih nonempty
    exact ⟨l, s, T, List.mem_cons_of_mem _ member, eligible⟩

/-- `PruneN` at positive fuel gives acceptability (port; see header). -/
theorem Ex_of_PruneN {n : Nat} {g : ext_tag} {T R : SessionType}
    (wf : T.WellFormed) (pruned : PruneN (n + 1) g T R) : Ex T g := by
  rcases pruned with ⟨U, base, same⟩ | ⟨H, HR, head, residual, next⟩
  · exact ⟨U, .base base⟩
  · apply (Ex_unfoldstar head.1).mpr
    have hw := SessionType.wellFormedUnfold wf head.1
    cases g <;> cases H <;> cases HR <;> (simp only [PfxStep] at next; try contradiction)
    · obtain ⟨p, l, s, U, member, accept⟩ := KRint_some_kept next.2.2.2 next.2.1
      exact Ex_int_single hw next.2.2.1 member accept
    · obtain ⟨l, s, U, member, accept⟩ := KRext_some_kept next.2.2.2.2 next.2.2.2.1
      exact Ex_ext_single hw next.2.1 member accept

/-- `Prune` gives acceptability (port; see header). -/
theorem Ex_of_Prune {g : ext_tag} {T R : SessionType}
    (wf : T.WellFormed) (pruned : Prune g T R) : Ex T g := Ex_of_PruneN wf (pruned 1)

/-- `PruneN` respects `teqN` on the right (port; see header). -/
theorem PruneN_teq_r (n : Nat) {g : ext_tag} {T R R' : SessionType}
    (pruned : PruneN n g T R) (same : teqN n R R') : PruneN n g T R' := by
  induction n generalizing T R R' with
  | zero => trivial
  | succ n ih =>
      rcases pruned with ⟨U, base, equal⟩ | ⟨H, HR, head, residual, next⟩
      · exact .inl ⟨U, base, teqN_trans (n + 1) equal same⟩
      · obtain ⟨HR₀, HR', residual₀, residual', shape⟩ := same
        have eq := hnf_unique residual₀ residual
        subst HR₀
        refine .inr ⟨H, HR', head, residual', ?_⟩
        cases g <;> cases H <;> cases HR <;>
          simp only [PfxStep] at next ⊢ <;> try contradiction
        all_goals cases HR' <;> (simp only [shapeEq] at shape; try contradiction)
        · exact ⟨next.1, Forall2_nil_r shape next.2.1, next.2.2.1,
            KRint_impl (fun _ _ _ _ _ => Iff.rfl)
              (fun _ _ _ _ _ _ ⟨U, hp, hq⟩ => ih hp hq) (KRint_right next.2.2.2 shape)⟩
        · obtain ⟨rfl, shape⟩ := shape
          exact ⟨next.1, next.2.1, next.2.2.1, Forall2_nil_r shape next.2.2.2.1,
            KRext_impl (fun _ _ _ _ => Iff.rfl)
              (fun _ _ _ _ _ ⟨U, hp, hq⟩ => ih hp hq) (KRext_right next.2.2.2.2 shape)⟩

/-- `Prune` respects `Eqv` on the right (port; see header). -/
theorem Prune_eqv_r {g : ext_tag} {T R R' : SessionType}
    (pruned : Prune g T R) (same : Eqv R R') : Prune g T R' :=
  fun n => PruneN_teq_r n (pruned n) (same n)

-- ================================================================
-- `co_implies_Prune`.
-- Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
-- Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>.
-- `co_implies_pruneN` is proved by double induction on
-- `(n, T.spine + T'.spine)`.
-- ================================================================

-- `in_keys` helpers.

theorem in_keys_int {bs : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {l : Lab} {s : DataSort} :
    (p, l, s) ∈ bs.map int_key3 ↔ ∃ T, (p, l, s, T) ∈ bs := by
  constructor
  · intro h
    obtain ⟨b, member, equal⟩ := List.mem_map.mp h
    rcases b with ⟨p', l', s', T⟩
    change (p', l', s') = (p, l, s) at equal
    cases equal
    exact ⟨T, member⟩
  · rintro ⟨T, member⟩
    exact List.mem_map.mpr ⟨_, member, rfl⟩

theorem in_keys_ext {bs : List (Lab × DataSort × SessionType)}
    {l : Lab} {s : DataSort} :
    (l, s) ∈ bs.map ext_key2 ↔ ∃ T, (l, s, T) ∈ bs := by
  constructor
  · intro h
    obtain ⟨b, member, equal⟩ := List.mem_map.mp h
    rcases b with ⟨l', s', T⟩
    change (l', s') = (l, s) at equal
    cases equal
    exact ⟨T, member⟩
  · rintro ⟨T, member⟩
    exact List.mem_map.mpr ⟨_, member, rfl⟩

-- `KRint_of_premises`.

theorem KRint_of_premises {E : SessionType → Prop} {P : SessionType → SessionType → Prop}
    {bs kept : List (Role × Lab × DataSort × SessionType)}
    (sourceUnique : (bs.map int_key3).Nodup)
    (keptUnique : (kept.map int_key3).Nodup)
    (order : (kept.map int_key3).Sublist (bs.map int_key3))
    (keys : ∀ p l s U, (p, l, s, U) ∈ kept → ∃ T, (p, l, s, T) ∈ bs ∧ E T)
    (cover : ∀ p l s T, (p, l, s, T) ∈ bs → E T → ∃ U, (p, l, s, U) ∈ kept)
    (next : ∀ T U p l s, (p, l, s, T) ∈ bs → (p, l, s, U) ∈ kept → P T U) :
    KRint E P bs kept := by
  classical
  induction bs generalizing kept with
  | nil =>
      have empty : kept = [] := List.map_eq_nil_iff.mp (List.sublist_nil.mp order)
      subst kept
      exact .nil
  | cons x bs ih =>
      rcases x with ⟨p, l, s, T⟩
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp sourceUnique
      have other {q : Role} {a : Lab} {b : DataSort} {V : SessionType}
          (member : (q, a, b, V) ∈ bs) : (q, a, b) ≠ (p, l, s) := by
        intro equal
        apply absent
        change (p, l, s) ∈ bs.map int_key3
        rw [← equal]
        exact in_keys_int.mpr ⟨V, member⟩
      by_cases eligible : E T
      · obtain ⟨U, member⟩ := cover p l s T List.mem_cons_self eligible
        cases kept with
        | nil => cases member
        | cons y kept =>
            rcases y with ⟨q, a, b, V⟩
            rcases List.cons_sublist_cons'.mp order with skipped | ⟨equal, tailOrder⟩
            · exact False.elim (absent (skipped.subset (in_keys_int.mpr ⟨U, member⟩)))
            · change (q, a, b) = (p, l, s) at equal
              cases equal
              obtain ⟨absentKept, uniqueKept⟩ := List.nodup_cons.mp keptUnique
              refine .keep eligible (next T V p l s List.mem_cons_self List.mem_cons_self)
                (ih unique uniqueKept tailOrder ?_ ?_ ?_)
              · intro q a b W member
                obtain ⟨Z, source, ez⟩ := keys q a b W (List.mem_cons_of_mem _ member)
                rcases List.mem_cons.mp source with equal | source
                · have keyEq : (q, a, b) = (p, l, s) := congrArg int_key3 equal
                  apply False.elim
                  apply absentKept
                  change (p, l, s) ∈ kept.map int_key3
                  rw [← keyEq]
                  exact in_keys_int.mpr ⟨W, member⟩
                · exact ⟨Z, source, ez⟩
              · intro q a b W source ew
                obtain ⟨Z, member⟩ := cover q a b W (List.mem_cons_of_mem _ source) ew
                rcases List.mem_cons.mp member with equal | member
                · exact False.elim (other source (congrArg int_key3 equal))
                · exact ⟨Z, member⟩
              · intro W Z q a b source member
                exact next W Z q a b (List.mem_cons_of_mem _ source) (List.mem_cons_of_mem _ member)
      · have absentKept : (p, l, s) ∉ kept.map int_key3 := by
          intro member
          obtain ⟨U, keptMem⟩ := in_keys_int.mp member
          obtain ⟨V, source, ev⟩ := keys p l s U keptMem
          rcases List.mem_cons.mp source with equal | source
          · cases equal
            exact eligible ev
          · exact other source rfl
        have tailOrder : (kept.map int_key3).Sublist (bs.map int_key3) := by
          rcases List.sublist_cons_iff.mp order with h | ⟨rest, equal, tail⟩
          · exact h
          · exact False.elim (absentKept (equal ▸ List.mem_cons_self))
        refine .drop eligible (ih unique keptUnique tailOrder ?_ ?_ ?_)
        · intro q a b U member
          obtain ⟨V, source, ev⟩ := keys q a b U member
          rcases List.mem_cons.mp source with equal | source
          · cases equal
            exact False.elim (eligible ev)
          · exact ⟨V, source, ev⟩
        · intro q a b U member eu
          exact cover q a b U (List.mem_cons_of_mem _ member) eu
        · intro U V q a b source member
          exact next U V q a b (List.mem_cons_of_mem _ source) member

-- `KRext_of_premises`.

theorem KRext_of_premises {E : SessionType → Prop} {P : SessionType → SessionType → Prop}
    {bs kept : List (Lab × DataSort × SessionType)}
    (sourceUnique : (bs.map ext_key2).Nodup)
    (keptUnique : (kept.map ext_key2).Nodup)
    (order : (kept.map ext_key2).Sublist (bs.map ext_key2))
    (keys : ∀ l s U, (l, s, U) ∈ kept → ∃ T, (l, s, T) ∈ bs ∧ E T)
    (cover : ∀ l s T, (l, s, T) ∈ bs → E T → ∃ U, (l, s, U) ∈ kept)
    (next : ∀ T U l s, (l, s, T) ∈ bs → (l, s, U) ∈ kept → P T U) :
    KRext E P bs kept := by
  classical
  induction bs generalizing kept with
  | nil =>
      have empty : kept = [] := List.map_eq_nil_iff.mp (List.sublist_nil.mp order)
      subst kept
      exact .nil
  | cons x bs ih =>
      rcases x with ⟨l, s, T⟩
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp sourceUnique
      have other {a : Lab} {b : DataSort} {V : SessionType}
          (member : (a, b, V) ∈ bs) : (a, b) ≠ (l, s) := by
        intro equal
        apply absent
        change (l, s) ∈ bs.map ext_key2
        rw [← equal]
        exact in_keys_ext.mpr ⟨V, member⟩
      by_cases eligible : E T
      · obtain ⟨U, member⟩ := cover l s T List.mem_cons_self eligible
        cases kept with
        | nil => cases member
        | cons y kept =>
            rcases y with ⟨a, b, V⟩
            rcases List.cons_sublist_cons'.mp order with skipped | ⟨equal, tailOrder⟩
            · exact False.elim (absent (skipped.subset (in_keys_ext.mpr ⟨U, member⟩)))
            · change (a, b) = (l, s) at equal
              cases equal
              obtain ⟨absentKept, uniqueKept⟩ := List.nodup_cons.mp keptUnique
              refine .keep eligible (next T V l s List.mem_cons_self List.mem_cons_self)
                (ih unique uniqueKept tailOrder ?_ ?_ ?_)
              · intro a b W member
                obtain ⟨Z, source, ez⟩ := keys a b W (List.mem_cons_of_mem _ member)
                rcases List.mem_cons.mp source with equal | source
                · have keyEq : (a, b) = (l, s) := congrArg ext_key2 equal
                  apply False.elim
                  apply absentKept
                  change (l, s) ∈ kept.map ext_key2
                  rw [← keyEq]
                  exact in_keys_ext.mpr ⟨W, member⟩
                · exact ⟨Z, source, ez⟩
              · intro a b W source ew
                obtain ⟨Z, member⟩ := cover a b W (List.mem_cons_of_mem _ source) ew
                rcases List.mem_cons.mp member with equal | member
                · exact False.elim (other source (congrArg ext_key2 equal))
                · exact ⟨Z, member⟩
              · intro W Z a b source member
                exact next W Z a b (List.mem_cons_of_mem _ source) (List.mem_cons_of_mem _ member)
      · have absentKept : (l, s) ∉ kept.map ext_key2 := by
          intro member
          obtain ⟨U, keptMem⟩ := in_keys_ext.mp member
          obtain ⟨V, source, ev⟩ := keys l s U keptMem
          rcases List.mem_cons.mp source with equal | source
          · cases equal
            exact eligible ev
          · exact other source rfl
        have tailOrder : (kept.map ext_key2).Sublist (bs.map ext_key2) := by
          rcases List.sublist_cons_iff.mp order with h | ⟨rest, equal, tail⟩
          · exact h
          · exact False.elim (absentKept (equal ▸ List.mem_cons_self))
        refine .drop eligible (ih unique keptUnique tailOrder ?_ ?_ ?_)
        · intro a b U member
          obtain ⟨V, source, ev⟩ := keys a b U member
          rcases List.mem_cons.mp source with equal | source
          · cases equal
            exact False.elim (eligible ev)
          · exact ⟨V, source, ev⟩
        · intro a b U member eu
          exact cover a b U (List.mem_cons_of_mem _ member) eu
        · intro U V a b source member
          exact next U V a b (List.mem_cons_of_mem _ source) member

-- `co_implies_pruneN` (proof by double induction on `(n, spine sum)`).

theorem co_implies_pruneN_aux (n : Nat) : ∀ (s : Nat) (T T' : SessionType) (γ : ext_tag),
    T.WellFormed → T'.WellFormed → T.spine + T'.spine ≤ s →
    mon_tr_yes_max_deriv_co T γ T' → PruneN n γ T T' := by
  induction n with
  | zero =>
      intro s T T' γ hT hT' hle h
      trivial
  | succ m ih_n =>
      intro s
      induction s with
      | zero =>
          intro T T' γ hT hT' hle h
          cases h with
          | base hT hb =>
              exact .inl ⟨_, hb, teqN_refl (m + 1) hT'⟩
          | @pfxInt branches kept q lab S hWF hne hno hall hkey hcover horder =>
              refine .inr ⟨.internalChoice branches, .internalChoice kept,
                hnf_self trivial, hnf_self trivial, ?_⟩
              simp only [PfxStep]
              refine ⟨hne.1, hne.2, hno, ?_⟩
              apply KRint_of_premises
                (SessionType.NoDupl.triple_nodup_of_internalChoice hWF.1)
                (SessionType.NoDupl.triple_nodup_of_internalChoice hT'.1)
                horder
              · intro p l s U member
                obtain ⟨T0, source, ⟨V, exist⟩⟩ := hkey p l s U member
                exact ⟨T0, source, ⟨V, exist⟩⟩
              · intro p l s T0 member ⟨V, exist⟩
                obtain ⟨U, keptMem⟩ := hcover p l s T0 member ⟨V, exist⟩
                exact ⟨U, keptMem⟩
              · intro T0 T1 p l s hB hK
                have h0 := wf_of_mem_int hWF hB
                have h1 := wf_of_mem_int hT' hK
                exact ih_n (T0.spine + T1.spine) T0 T1 _
                  h0 h1 (Nat.le_refl _) (hall T0 T1 p l s hB hK)
          | @pfxExt p branches kept q lab S hWF hne hneq hall hkey hcover horder =>
              refine .inr ⟨.externalChoice p branches, .externalChoice p kept,
                hnf_self trivial, hnf_self trivial, ?_⟩
              simp only [PfxStep]
              refine ⟨trivial, hneq, hne.1, hne.2, ?_⟩
              apply KRext_of_premises
                (nodup_ext_key2_of_wf hWF)
                (nodup_ext_key2_of_wf hT')
                horder
              · intro l s U member
                obtain ⟨T0, source, ⟨V, exist⟩⟩ := hkey l s U member
                exact ⟨T0, source, ⟨V, exist⟩⟩
              · intro l s T0 member ⟨V, exist⟩
                obtain ⟨U, keptMem⟩ := hcover l s T0 member ⟨V, exist⟩
                exact ⟨U, keptMem⟩
              · intro T0 T1 l s hB hK
                have h0 := wf_of_mem_ext hWF hB
                have h1 := wf_of_mem_ext hT' hK
                exact ih_n (T0.spine + T1.spine) T0 T1 _
                  h0 h1 (Nat.le_refl _) (hall T0 T1 l s hB hK)
          | recL hWF hsub =>
              -- `T = tRec`, spine ≥ 1 contradicts `≤ 0` (`simp` closes via `False`).
              simp [SessionType.spine] at hle
          | recR hWF hsub =>
              simp [SessionType.spine] at hle
      | succ s ih_s =>
          intro T T' γ hT hT' hle h
          cases h with
          | base hT hb =>
              exact .inl ⟨_, hb, teqN_refl (m + 1) hT'⟩
          | @pfxInt branches kept q lab S hWF hne hno hall hkey hcover horder =>
              refine .inr ⟨.internalChoice branches, .internalChoice kept,
                hnf_self trivial, hnf_self trivial, ?_⟩
              simp only [PfxStep]
              refine ⟨hne.1, hne.2, hno, ?_⟩
              apply KRint_of_premises
                (SessionType.NoDupl.triple_nodup_of_internalChoice hWF.1)
                (SessionType.NoDupl.triple_nodup_of_internalChoice hT'.1)
                horder
              · intro p l s U member
                obtain ⟨T0, source, ⟨V, exist⟩⟩ := hkey p l s U member
                exact ⟨T0, source, ⟨V, exist⟩⟩
              · intro p l s T0 member ⟨V, exist⟩
                obtain ⟨U, keptMem⟩ := hcover p l s T0 member ⟨V, exist⟩
                exact ⟨U, keptMem⟩
              · intro T0 T1 p l s hB hK
                have h0 := wf_of_mem_int hWF hB
                have h1 := wf_of_mem_int hT' hK
                exact ih_n (T0.spine + T1.spine) T0 T1 _
                  h0 h1 (Nat.le_refl _) (hall T0 T1 p l s hB hK)
          | @pfxExt p branches kept q lab S hWF hne hneq hall hkey hcover horder =>
              refine .inr ⟨.externalChoice p branches, .externalChoice p kept,
                hnf_self trivial, hnf_self trivial, ?_⟩
              simp only [PfxStep]
              refine ⟨trivial, hneq, hne.1, hne.2, ?_⟩
              apply KRext_of_premises
                (nodup_ext_key2_of_wf hWF)
                (nodup_ext_key2_of_wf hT')
                horder
              · intro l s U member
                obtain ⟨T0, source, ⟨V, exist⟩⟩ := hkey l s U member
                exact ⟨T0, source, ⟨V, exist⟩⟩
              · intro l s T0 member ⟨V, exist⟩
                obtain ⟨U, keptMem⟩ := hcover l s T0 member ⟨V, exist⟩
                exact ⟨U, keptMem⟩
              · intro T0 T1 l s hB hK
                have h0 := wf_of_mem_ext hWF hB
                have h1 := wf_of_mem_ext hT' hK
                exact ih_n (T0.spine + T1.spine) T0 T1 _
                  h0 h1 (Nat.le_refl _) (hall T0 T1 l s hB hK)
          | @recL X B γ V hWF hsub =>
              have hco := hWF.2.2
              cases hco with
              | tRec hBco hG =>
                  have hleB : (substSessionType B X (SessionType.tRec X B)).spine ≤ B.spine :=
                    spine_subst_le B X _ (guarded_not_mem_headVars B X hG)
                  have hsp : (SessionType.tRec X B).spine = B.spine + 1 := rfl
                  have hsum : (substSessionType B X (SessionType.tRec X B)).spine + T'.spine ≤ s := by
                    omega
                  have hU : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
                    SessionType.wellFormedUnfold hWF (.step .tRec (.refl _))
                  have ih := ih_s (substSessionType B X (SessionType.tRec X B)) T' γ hU hT' hsum hsub
                  exact (PruneN_unfold_l (m + 1)).mpr ih
          | @recR Y C T γ hWF hsub =>
              have hco := hT'.2.2
              cases hco with
              | tRec hCco hG =>
                  have hleC : (substSessionType C Y (SessionType.tRec Y C)).spine ≤ C.spine :=
                    spine_subst_le C Y _ (guarded_not_mem_headVars C Y hG)
                  have hsum : T.spine + (substSessionType C Y (SessionType.tRec Y C)).spine ≤ s := by
                    simp [SessionType.spine] at hle ⊢
                    omega
                  have hU : (substSessionType C Y (SessionType.tRec Y C)).WellFormed :=
                    SessionType.wellFormedUnfold hT' (.step .tRec (.refl _))
                  have ih := ih_s T (substSessionType C Y (SessionType.tRec Y C)) γ hT hU hsum hsub
                  exact (PruneN_unfold_r (m + 1)).mpr ih

theorem co_implies_pruneN (n : Nat) {T T' : SessionType} {γ : ext_tag}
    (hT : T.WellFormed) (hT' : T'.WellFormed)
    (h : mon_tr_yes_max_deriv_co T γ T') : PruneN n γ T T' :=
  co_implies_pruneN_aux n (T.spine + T'.spine) T T' γ hT hT' (Nat.le_refl _) h

theorem co_implies_Prune {T T' : SessionType} {γ : ext_tag}
    (hT : T.WellFormed) (hT' : T'.WellFormed)
    (h : mon_tr_yes_max_deriv_co T γ T') : Prune γ T T' :=
  fun n => co_implies_pruneN n hT hT' h

theorem nodup_key3_of_nodup_key {kept : List (Role × Lab × DataSort × SessionType)}
    (unique : (kept.map int_key).Nodup) : (kept.map int_key3).Nodup := by
  change (kept.map fun b => (b.1, b.2.1)).Nodup at unique
  apply List.Nodup.of_map (f := fun k : Role × Lab × DataSort => (k.1, k.2.1))
  simpa only [List.map_map, Function.comp_def, int_key, int_key3] using unique

theorem nodup_key2_of_nodup_key {kept : List (Lab × DataSort × SessionType)}
    (unique : (kept.map ext_key).Nodup) : (kept.map ext_key2).Nodup := by
  change (kept.map fun b => b.1).Nodup at unique
  apply List.Nodup.of_map (f := fun k : Lab × DataSort => k.1)
  simpa only [List.map_map, Function.comp_def, ext_key, ext_key2] using unique

theorem KRint_map {E : SessionType → Prop} {P : SessionType → SessionType → Prop}
    (f : SessionType → SessionType) {bs kept : List (Role × Lab × DataSort × SessionType)}
    (pruned : KRint E (fun T U => P T (f U)) bs kept) :
    KRint E P bs (kept.map fun b => (b.1, b.2.1, b.2.2.1, f b.2.2.2)) := by
  induction pruned with
  | nil => exact .nil
  | keep eligible next rest ih => exact .keep eligible next ih
  | drop ineligible rest ih => exact .drop ineligible ih

theorem KRext_map {E : SessionType → Prop} {P : SessionType → SessionType → Prop}
    (f : SessionType → SessionType) {bs kept : List (Lab × DataSort × SessionType)}
    (pruned : KRext E (fun T U => P T (f U)) bs kept) :
    KRext E P bs (kept.map fun b => (b.1, b.2.1, f b.2.2)) := by
  induction pruned with
  | nil => exact .nil
  | keep eligible next rest ih => exact .keep eligible next ih
  | drop ineligible rest ih => exact .drop ineligible ih

def EnvOK (n : Nat) (G : FCtx) (ρ : env) (g : ext_tag) : Prop :=
  env_closed ρ ∧ ∀ T u, (T, u) ∈ G → ∃ R, elookup ρ u = some R ∧ PruneN n g T R

theorem EnvOK_mono {n m : Nat} {G : FCtx} {ρ : env} {g : ext_tag}
    (le : m ≤ n) (good : EnvOK n G ρ g) : EnvOK m G ρ g := by
  refine ⟨good.1, ?_⟩
  intro T u member
  obtain ⟨R, lookup, pruned⟩ := good.2 T u member
  exact ⟨R, lookup, PruneN_mono le pruned⟩

theorem EnvOK_defined {n : Nat} {G : FCtx} {ρ : env} {g : ext_tag} {x : String}
    (good : EnvOK n G ρ g) (member : x ∈ G.map Prod.snd) : elookup ρ x ≠ none := by
  obtain ⟨⟨T, u⟩, entryMem, equal⟩ := List.mem_map.mp member
  subst x
  obtain ⟨R, lookup, _⟩ := good.2 T u entryMem
  simp [lookup]

theorem closed_after_env {n : Nat} {G : FCtx} {ρ : env} {g : ext_tag} {V : SessionType}
    (good : EnvOK n G ρ g) (bound : ∀ y ∈ V.fv, y ∈ G.map Prod.snd) :
    (ssubst ρ V).IsClosed :=
  ssubst_closed V ρ good.1 (fun y member => EnvOK_defined good (bound y member))

theorem fmon_spec_n (n : Nat) {G : FCtx} {T V : SessionType} {g : ext_tag}
    (step : fmon G T g V) : T.WellFormed → GNames G →
    ∀ ρ, EnvOK n G ρ g → PruneN (n + 1) g T (ssubst ρ V) := by
  revert G T V g step
  induction n with
  | zero =>
      intro G T V g step
      apply fmon.rec
        (motive_1 := fun G T g V _ => T.WellFormed → GNames G →
          ∀ ρ, EnvOK 0 G ρ g → PruneN 1 g T (ssubst ρ V))
        (motive_2 := fun G T g V _ => T.WellFormed → GNames G →
          ∀ ρ, EnvOK 0 G ρ g → PruneN 0 g T (ssubst ρ V)) (t := step)
      case fm_base =>
        intro G T g V base wf names ρ good
        have resultWF := mon_tr_yes_base_preserves_wf base wf
        rw [ssubst_closed_id' V ρ resultWF.2.1]
        exact .inl ⟨V, base, teqN_refl 1 resultWF⟩
      case fm_pfxInt =>
        intro G bs kept q lab S nonempty keptNonempty off all unique keys cover order ih wf names ρ good
        refine .inr ⟨.internalChoice bs,
          .internalChoice (kept.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ b.2.2.2)),
          hnf_self trivial, (by rw [ssubst]; exact hnf_self trivial), ?_⟩
        refine ⟨nonempty, (fun empty => keptNonempty (List.map_eq_nil_iff.mp empty)), off, ?_⟩
        apply KRint_map
        apply KRint_of_premises (SessionType.NoDupl.triple_nodup_of_internalChoice wf.1)
          (nodup_key3_of_nodup_key unique) order keys cover
        intro T U p l s source target
        exact ih T U p l s source target (wf_of_mem_int wf source) names ρ good
      case fm_pfxExt =>
        intro G p bs kept q lab S nonempty keptNonempty apart all unique keys cover order ih wf names ρ good
        refine .inr ⟨.externalChoice p bs,
          .externalChoice p (kept.map fun b => (b.1, b.2.1, ssubst ρ b.2.2)),
          hnf_self trivial, (by rw [ssubst]; exact hnf_self trivial), ?_⟩
        refine ⟨rfl, apart, nonempty, (fun empty => keptNonempty (List.map_eq_nil_iff.mp empty)), ?_⟩
        apply KRext_map
        have sourceUnique : (bs.map ext_key2).Nodup := by
          cases wf.1 with
          | externalChoice labels _ _ => exact nodup_of_nodup_labels labels
        apply KRext_of_premises sourceUnique (nodup_key2_of_nodup_key unique) order keys cover
        intro T U l s source target
        exact ih T U l s source target (wf_of_mem_ext wf source) names ρ good
      case fm_rec =>
        intro G X B H g V unfolds normal sub ih wf names ρ good
        let u := fvar G.length
        let R := ssubst ρ (mkRec u V)
        have headWF := SessionType.wellFormedUnfold wf unfolds
        have bound := (fmon_wf sub headWF).2.2
        have closed : R.IsClosed := by
          apply closed_after_env good
          intro y member
          obtain ⟨member, apart⟩ := fv_mkRec member
          have inContext := bound y member
          simpa [u, apart] using inContext
        have self : PruneN 0 g (.tRec X B) R := trivial
        let ρ' := (u, R) :: ρ
        have good' : EnvOK 0 ((.tRec X B, u) :: G) ρ' g := by
          refine ⟨env_closed_cons good.1 closed, ?_⟩
          intro T v member
          rcases List.mem_cons.mp member with equal | member
          · cases equal
            exact ⟨R, by simp [ρ', elookup], self⟩
          · obtain ⟨R', lookup, pruned⟩ := good.2 T v member
            refine ⟨R', ?_, pruned⟩
            have apart : v ≠ u := GNames_fresh names member
            simpa [ρ', elookup, List.lookup_cons, beq_eq_false_iff_ne.mpr apart] using lookup
        have head := ih headWF (GNames_push _ names) ρ' good'
        apply (PruneN_unfoldstar_l 1 unfolds).mpr
        by_cases free : u ∈ V.fv
        · change PruneN 1 g H (ssubst ρ (mkRec u V))
          rw [mkRec, ite_eq_left free, ssubst]
          apply (PruneN_unfold_r 1).mpr
          have rdef : R = .tRec u (ssubst (eremove u ρ) V) := by
            simp only [R, mkRec, ite_eq_left free, ssubst]
          rw [← rdef, subst_ssubst_cons V ρ u R good.1 closed]
          exact head
        · have same : ssubst ρ V = ssubst ρ' V := by
            apply ssubst_ext
            intro y member
            have apart : y ≠ u := by intro equal; subst y; exact free member
            simp [ρ', elookup, List.lookup_cons, beq_eq_false_iff_ne.mpr apart]
          change PruneN 1 g H (ssubst ρ (mkRec u V))
          rw [mkRec, ite_eq_right free, same]
          exact head
      case fc_fold =>
        intro G T g u member wf names ρ good
        obtain ⟨R, lookup, pruned⟩ := good.2 T u member
        simpa [ssubst, lookup] using pruned
      case fc_go =>
        intro G T g V fresh sub ih wf names ρ good
        exact PruneN_mono (by omega) (ih wf names ρ good)
  | succ n ih_n =>
      intro G T V g step
      apply fmon.rec
        (motive_1 := fun G T g V _ => T.WellFormed → GNames G →
          ∀ ρ, EnvOK (n + 1) G ρ g → PruneN (n + 2) g T (ssubst ρ V))
        (motive_2 := fun G T g V _ => T.WellFormed → GNames G →
          ∀ ρ, EnvOK (n + 1) G ρ g → PruneN (n + 1) g T (ssubst ρ V)) (t := step)
      case fm_base =>
        intro G T g V base wf names ρ good
        have resultWF := mon_tr_yes_base_preserves_wf base wf
        rw [ssubst_closed_id' V ρ resultWF.2.1]
        exact .inl ⟨V, base, teqN_refl (n + 2) resultWF⟩
      case fm_pfxInt =>
        intro G bs kept q lab S nonempty keptNonempty off all unique keys cover order ih wf names ρ good
        refine .inr ⟨.internalChoice bs,
          .internalChoice (kept.map fun b => (b.1, b.2.1, b.2.2.1, ssubst ρ b.2.2.2)),
          hnf_self trivial, (by rw [ssubst]; exact hnf_self trivial), ?_⟩
        refine ⟨nonempty, (fun empty => keptNonempty (List.map_eq_nil_iff.mp empty)), off, ?_⟩
        apply KRint_map
        apply KRint_of_premises (SessionType.NoDupl.triple_nodup_of_internalChoice wf.1)
          (nodup_key3_of_nodup_key unique) order keys cover
        intro T U p l s source target
        exact ih T U p l s source target (wf_of_mem_int wf source) names ρ good
      case fm_pfxExt =>
        intro G p bs kept q lab S nonempty keptNonempty apart all unique keys cover order ih wf names ρ good
        refine .inr ⟨.externalChoice p bs,
          .externalChoice p (kept.map fun b => (b.1, b.2.1, ssubst ρ b.2.2)),
          hnf_self trivial, (by rw [ssubst]; exact hnf_self trivial), ?_⟩
        refine ⟨rfl, apart, nonempty, (fun empty => keptNonempty (List.map_eq_nil_iff.mp empty)), ?_⟩
        apply KRext_map
        have sourceUnique : (bs.map ext_key2).Nodup := by
          cases wf.1 with
          | externalChoice labels _ _ => exact nodup_of_nodup_labels labels
        apply KRext_of_premises sourceUnique (nodup_key2_of_nodup_key unique) order keys cover
        intro T U l s source target
        exact ih T U l s source target (wf_of_mem_ext wf source) names ρ good
      case fm_rec =>
        intro G X B H g V unfolds normal sub ih wf names ρ good
        let u := fvar G.length
        let R := ssubst ρ (mkRec u V)
        have headWF := SessionType.wellFormedUnfold wf unfolds
        have bound := (fmon_wf sub headWF).2.2
        have closed : R.IsClosed := by
          apply closed_after_env good
          intro y member
          obtain ⟨member, apart⟩ := fv_mkRec member
          have inContext := bound y member
          simpa [u, apart] using inContext
        have self : PruneN (n + 1) g (.tRec X B) R :=
          ih_n (fmon.fm_rec unfolds normal sub) wf names ρ
            (EnvOK_mono (by omega) good)
        let ρ' := (u, R) :: ρ
        have good' : EnvOK (n + 1) ((.tRec X B, u) :: G) ρ' g := by
          refine ⟨env_closed_cons good.1 closed, ?_⟩
          intro T v member
          rcases List.mem_cons.mp member with equal | member
          · cases equal
            exact ⟨R, by simp [ρ', elookup], self⟩
          · obtain ⟨R', lookup, pruned⟩ := good.2 T v member
            refine ⟨R', ?_, pruned⟩
            have apart : v ≠ u := GNames_fresh names member
            simpa [ρ', elookup, List.lookup_cons, beq_eq_false_iff_ne.mpr apart] using lookup
        have head := ih headWF (GNames_push _ names) ρ' good'
        apply (PruneN_unfoldstar_l (n + 2) unfolds).mpr
        by_cases free : u ∈ V.fv
        · change PruneN (n + 2) g H (ssubst ρ (mkRec u V))
          rw [mkRec, ite_eq_left free, ssubst]
          apply (PruneN_unfold_r (n + 2)).mpr
          have rdef : R = .tRec u (ssubst (eremove u ρ) V) := by
            simp only [R, mkRec, ite_eq_left free, ssubst]
          rw [← rdef, subst_ssubst_cons V ρ u R good.1 closed]
          exact head
        · have same : ssubst ρ V = ssubst ρ' V := by
            apply ssubst_ext
            intro y member
            have apart : y ≠ u := by intro equal; subst y; exact free member
            simp [ρ', elookup, List.lookup_cons, beq_eq_false_iff_ne.mpr apart]
          change PruneN (n + 2) g H (ssubst ρ (mkRec u V))
          rw [mkRec, ite_eq_right free, same]
          exact head
      case fc_fold =>
        intro G T g u member wf names ρ good
        obtain ⟨R, lookup, pruned⟩ := good.2 T u member
        simpa [ssubst, lookup] using pruned
      case fc_go =>
        intro G T g V fresh sub ih wf names ρ good
        exact PruneN_mono (by omega) (ih wf names ρ good)

theorem fmon_spec {T V : SessionType} {g : ext_tag}
    (wf : T.WellFormed) (step : fmon [] T g V) : Prune g T V := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
      have good : EnvOK n [] [] g := by
        constructor
        · intro x v member; cases member
        · intro T u member; cases member
      simpa only [ssubst_nil] using fmon_spec_n n step wf GNames_nil [] good
