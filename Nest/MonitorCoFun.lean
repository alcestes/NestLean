import Nest.MonitorCoRel
import Nest.MonitorCoBase

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-! # MonitorCoFun: executable monitor transition function.

Computable transition function `mon_tr_yes_co_fun`
(`FmonCompute.outgoing`/`residual`/`observe`) with soundness and
completeness, executable well-formedness (`wfCheck` + soundness,
`guardedCheck`), and the eligibility decision procedure. Relational
fold (`fmon`), pruning (`Prune`), and type equivalence (`Eqv`) live in
`Nest.MonitorCoRel`; `Ex`/`traversalNodes`/`KRint`/`KRext` live in
`Nest.MonitorCoBase`. Ports credited to
Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and
Kristýna Petrlíková <auburn@kam.mff.cuni.cz>; see per-declaration doc-comments.
-/


/-- Guardedness check (boolean twin of `SessionType.Guarded`). -/
def SessionType.guardedCheck (X : String) : SessionType → Bool
  | .tEnd => true
  | .tVar Y => decide (X ≠ Y)
  | .internalChoice _ => true
  | .externalChoice _ _ => true
  | .tRec Y T' => guardedCheck X T'

theorem SessionType.guardedCheck_sound {X : String} {T : SessionType}
    (h : SessionType.guardedCheck X T = true) : SessionType.Guarded X T := by
  cases T with
  | tEnd => exact True.intro
  | tVar Y =>
    have h' : decide (X ≠ Y) = true := h
    have h2 : X ≠ Y := of_decide_eq_true h'
    exact h2
  | internalChoice _ => exact True.intro
  | externalChoice _ _ => exact True.intro
  | tRec Y T' =>
    have h' : SessionType.guardedCheck X T' = true := h
    exact @guardedCheck_sound X T' h'

mutual
/-- Executable well-formedness check under a bound-variable context. -/
def SessionType.wfCheck (bound : List String) : SessionType → Bool
  | .tEnd => true
  | .tVar X => decide (X ∈ bound)
  | .internalChoice bs =>
      decide (bs ≠ []) &&
      decide ((bs.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))).Nodup) &&
      wfCheckInt bound bs
  | .externalChoice _ bs =>
      decide (bs ≠ []) &&
      decide ((bs.map (fun x : Lab × DataSort × SessionType => x.1)).Nodup) &&
      wfCheckExt bound bs
  | .tRec X B => wfCheck (X :: bound) B && guardedCheck X B
/-- Branch-list half of `wfCheck` (internal choices). -/
def SessionType.wfCheckInt (bound : List String) :
    List (Role × Lab × DataSort × SessionType) → Bool
  | [] => true
  | (_, _, _, T0) :: tl => wfCheck bound T0 && wfCheckInt bound tl
/-- Branch-list half of `wfCheck` (external choices). -/
def SessionType.wfCheckExt (bound : List String) :
    List (Lab × DataSort × SessionType) → Bool
  | [] => true
  | (_, _, T0) :: tl => wfCheck bound T0 && wfCheckExt bound tl
end

/-- Free variables of an internal choice come from some branch target. -/
theorem SessionType.fv_mem_branch_int
    {branches : List (Role × Lab × DataSort × SessionType)} {X : String}
    (h : X ∈ SessionType.fv (SessionType.internalChoice branches)) :
    ∃ x : Role × Lab × DataSort × SessionType, x ∈ branches ∧ X ∈ (x.2.2.2).fv := by
  induction branches with
  | nil =>
    simp only [SessionType.fv, SessionType.fv.goInt, List.mem_nil_iff] at h
  | cons hd tl ih =>
    obtain ⟨r, l, s, T0⟩ := hd
    simp only [SessionType.fv, SessionType.fv.goInt, List.mem_append] at h
    rcases h with h | h
    · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨x, hmem, hx⟩ := ih h
      exact ⟨x, List.mem_cons.mpr (Or.inr hmem), hx⟩

/-- Free variables of an external choice come from some branch target. -/
theorem SessionType.fv_mem_branch_ext
    {p : Role} {branches : List (Lab × DataSort × SessionType)} {X : String}
    (h : X ∈ SessionType.fv (SessionType.externalChoice p branches)) :
    ∃ x : Lab × DataSort × SessionType, x ∈ branches ∧ X ∈ (x.2.2).fv := by
  induction branches with
  | nil =>
    simp only [SessionType.fv, SessionType.fv.goExt, List.mem_nil_iff] at h
  | cons hd tl ih =>
    obtain ⟨l, s, T0⟩ := hd
    simp only [SessionType.fv, SessionType.fv.goExt, List.mem_append] at h
    rcases h with h | h
    · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨x, hmem, hx⟩ := ih h
      exact ⟨x, List.mem_cons.mpr (Or.inr hmem), hx⟩

/-- `wfCheckInt` unfolds to per-branch checks. -/
theorem SessionType.wfCheckInt_all {bound : List String}
    {bs : List (Role × Lab × DataSort × SessionType)}
    (h : SessionType.wfCheckInt bound bs = true) :
    ∀ x ∈ bs, SessionType.wfCheck bound x.2.2.2 = true := by
  induction bs with
  | nil => intro x hx; simp at hx
  | cons hd tl ih =>
    obtain ⟨r, l, s, T0⟩ := hd
    simp only [SessionType.wfCheckInt, Bool.and_eq_true] at h
    obtain ⟨hT, htl⟩ := h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simpa using hT
    · exact ih htl _ hx

/-- `wfCheckExt` unfolds to per-branch checks. -/
theorem SessionType.wfCheckExt_all {bound : List String}
    {bs : List (Lab × DataSort × SessionType)}
    (h : SessionType.wfCheckExt bound bs = true) :
    ∀ x ∈ bs, SessionType.wfCheck bound x.2.2 = true := by
  induction bs with
  | nil => intro x hx; simp at hx
  | cons hd tl ih =>
    obtain ⟨l, s, T0⟩ := hd
    simp only [SessionType.wfCheckExt, Bool.and_eq_true] at h
    obtain ⟨hT, htl⟩ := h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simpa using hT
    · exact ih htl _ hx

/-- Soundness auxiliary: free variables stay in scope, plus `NoDupl`
and `Contractive`, by induction on a size fuel bound. Branch targets are
strictly smaller (`sizeOf` lemmas), and `tRec` bodies are strictly
smaller than the `tRec` node. -/
theorem SessionType.wfCheck_sound_aux (n : Nat) : ∀ (bound : List String) (T : SessionType),
    sizeOf T < n → T.wfCheck bound = true →
    (∀ X, X ∈ T.fv → X ∈ bound) ∧ T.NoDupl ∧ T.Contractive := by
  induction n with
  | zero =>
    intro bound T hlt _
    omega
  | succ n ih =>
    intro bound T hlt h
    cases T with
    | tEnd =>
      refine ⟨?_, SessionType.NoDupl.end, SessionType.Contractive.end⟩
      intro X hX
      simp [SessionType.fv] at hX
    | tVar Y =>
      simp only [SessionType.wfCheck.eq_2] at h
      have hY : Y ∈ bound := of_decide_eq_true h
      refine ⟨?_, SessionType.NoDupl.tVar Y, SessionType.Contractive.tVar Y⟩
      intro X hX
      simp only [SessionType.fv, List.mem_singleton] at hX
      subst hX
      exact hY
    | internalChoice branches =>
      have heq : SessionType.wfCheck bound (SessionType.internalChoice branches) =
          (decide (branches ≠ []) && decide ((branches.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)).Nodup) && SessionType.wfCheckInt bound branches) := rfl
      rw [heq] at h
      simp only [Bool.and_eq_true] at h
      have hne : decide (branches ≠ []) = true := h.1.1
      have hND : decide ((branches.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)).Nodup) = true := h.1.2
      have hall : SessionType.wfCheckInt bound branches = true := h.2
      have hmem : ∀ {x : Role × Lab × DataSort × SessionType},
          x ∈ branches → sizeOf x.2.2.2 < n := by
        intro x hx
        obtain ⟨r, l, s, T0⟩ := x
        have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice hx
        show sizeOf T0 < n
        omega
      have hall' := SessionType.wfCheckInt_all hall
      have hsub : ∀ {x : Role × Lab × DataSort × SessionType} (hm : x ∈ branches),
          (∀ X, X ∈ x.2.2.2.fv → X ∈ bound) ∧ x.2.2.2.NoDupl ∧ x.2.2.2.Contractive := by
        intro x hx
        exact ih _ _ (hmem hx) (hall' x hx)
      have hND' : (branches.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)).Nodup :=
        of_decide_eq_true hND
      have hne' : branches ≠ [] := of_decide_eq_true hne
      refine ⟨?_, SessionType.NoDupl.internalChoice hND' hne'
        (fun x hx => (hsub hx).2.1), SessionType.Contractive.internalChoice
        (fun x hx => (hsub hx).2.2)⟩
      intro X hX
      obtain ⟨x, hxmem, hX0⟩ := SessionType.fv_mem_branch_int hX
      exact (hsub hxmem).1 X hX0
    | externalChoice p branches =>
      have heq : SessionType.wfCheck bound (SessionType.externalChoice p branches) =
          (decide (branches ≠ []) && decide ((branches.map fun x : Lab × DataSort × SessionType => x.1).Nodup) && SessionType.wfCheckExt bound branches) := rfl
      rw [heq] at h
      simp only [Bool.and_eq_true] at h
      have hne : decide (branches ≠ []) = true := h.1.1
      have hND : decide ((branches.map fun x : Lab × DataSort × SessionType => x.1).Nodup) = true := h.1.2
      have hall : SessionType.wfCheckExt bound branches = true := h.2
      have hmem : ∀ {x : Lab × DataSort × SessionType},
          x ∈ branches → sizeOf x.2.2 < n := by
        intro x hx
        obtain ⟨l, s, T0⟩ := x
        have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice (p := p) hx
        show sizeOf T0 < n
        omega
      have hall' := SessionType.wfCheckExt_all hall
      have hsub : ∀ {x : Lab × DataSort × SessionType} (hm : x ∈ branches),
          (∀ X, X ∈ x.2.2.fv → X ∈ bound) ∧ x.2.2.NoDupl ∧ x.2.2.Contractive := by
        intro x hx
        exact ih _ _ (hmem hx) (hall' _ hx)
      have hND' : (branches.map fun x : Lab × DataSort × SessionType => x.1).Nodup :=
        of_decide_eq_true hND
      have hne' : branches ≠ [] := of_decide_eq_true hne
      refine ⟨?_, SessionType.NoDupl.externalChoice hND' hne'
        (fun x hx => (hsub hx).2.1), SessionType.Contractive.externalChoice
        (fun x hx => (hsub hx).2.2)⟩
      intro X hX
      obtain ⟨x, hxmem, hX0⟩ := SessionType.fv_mem_branch_ext hX
      exact (hsub hxmem).1 X hX0
    | tRec X B =>
      simp only [SessionType.wfCheck.eq_5, Bool.and_eq_true] at h
      obtain ⟨hB, hG⟩ := h
      have hBsize : sizeOf B < n := by
        have h1 : sizeOf B < sizeOf (SessionType.tRec X B) := by simp
        omega
      obtain ⟨ihFv, ihND, ihCo⟩ := ih _ _ hBsize hB
      refine ⟨?_, SessionType.NoDupl.tRec ihND,
        SessionType.Contractive.tRec ihCo (guardedCheck_sound hG)⟩
      intro X0 hX0
      simp only [SessionType.fv, List.mem_filter] at hX0
      obtain ⟨hXmem, hXcond⟩ := hX0
      have hmem : X0 ∈ X :: bound := ihFv _ hXmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp at hXcond
      · exact hmem

/-- Soundness of the executable check: `wfCheck [] T = true` delivers
a `WellFormed` proof. Concrete types discharge this by `decide`. -/
theorem SessionType.wfCheck_sound {T : SessionType}
    (h : T.wfCheck [] = true) : T.WellFormed := by
  obtain ⟨hfv, hND, hCo⟩ :=
    SessionType.wfCheck_sound_aux (sizeOf T + 1) [] T (Nat.lt_succ_self _) h
  refine ⟨hND, ?_, hCo⟩
  unfold SessionType.IsClosed
  rw [List.eq_nil_iff_forall_not_mem]
  intro X hX
  exact absurd (hfv X hX) (by simp)


-- ================================================================
-- Fuel-bounded acceptability search.
-- ================================================================


/-! # Fuel-bounded acceptability search.

A fuel-bounded boolean search (`eligibleFuel`) that decides branch
acceptability, with soundness (`eligibleFuel_sound`: fuel-true implies
`Ex`) and eventual completeness (`eligible_eventually`: every
`mon_tr_yes_exist` derivation is found at some fuel).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>.
Adapted to `Nest`'s `SessionType`/`WellFormed` (identical shape:
pair-key `NoDupl` for internal choice, singleton keys for external choice).
-/

mutual
  /-- Syntax-node count (port).
  Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
  Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
  def syntaxNodes : SessionType → Nat
    | .tEnd | .tVar _ => 1
    | .tRec _ B => 1 + syntaxNodes B
    | .internalChoice bs => 1 + internalNodes bs
    | .externalChoice _ bs => 1 + externalNodes bs
  /-- Internal branch-node count (port; see `syntaxNodes` for credit). -/
  def internalNodes : List (Role × Lab × DataSort × SessionType) → Nat
    | [] => 0
    | b :: bs => syntaxNodes b.2.2.2 + internalNodes bs
  /-- External branch-node count (port; see `syntaxNodes` for credit). -/
  def externalNodes : List (Lab × DataSort × SessionType) → Nat
    | [] => 0
    | b :: bs => syntaxNodes b.2.2 + externalNodes bs
end

/-- Search for a matching observation through at most `fuel` syntax nodes.
Inputs cross an output choice only if every sibling uses another peer (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def eligibleFuel : Nat → SessionType → ext_tag → Bool
  | 0, _, _ => false
  | n + 1, .tRec X B, g => eligibleFuel n (substSessionType B X (.tRec X B)) g
  | _ + 1, .internalChoice bs, .send p l s =>
      bs.any fun b => b.1 == p && b.2.1 == l && b.2.2.1 == s
  | n + 1, .internalChoice bs, .recv q l s =>
      (bs.all fun b => b.1 != q) && bs.any (fun b => eligibleFuel n b.2.2.2 (.recv q l s))
  | n + 1, .externalChoice p bs, .recv q l s =>
      if p == q then bs.any (fun b => b.1 == l && b.2.1 == s)
      else bs.any (fun b => eligibleFuel n b.2.2 (.recv q l s))
  | _ + 1, _, _ => false

/-- Eligibility is decidable by a bounded search on finite recursive syntax (port).
The bound is discharged by `eligibility_correct`
(`eligibility T g = true ↔ Ex T g`).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def eligibility (T : SessionType) (g : ext_tag) : Bool :=
  eligibleFuel (syntaxNodes T) T g

/-- Fuel-monotonicity of the search (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem eligibleFuel_mono {n m : Nat} (le : n ≤ m) {T : SessionType} {g : ext_tag}
    (accepted : eligibleFuel n T g = true) : eligibleFuel m T g = true := by
  induction n generalizing m T with
  | zero => simp [eligibleFuel] at accepted
  | succ n ih =>
      cases m with
      | zero => omega
      | succ m =>
          have nm : n ≤ m := by omega
          cases T with
          | tEnd => cases g <;> simp [eligibleFuel] at accepted
          | tVar X => cases g <;> simp [eligibleFuel] at accepted
          | tRec X B => exact ih nm accepted
          | internalChoice bs =>
              cases g with
              | send p l s => exact accepted
              | recv q l s =>
                  simp only [eligibleFuel, Bool.and_eq_true, List.any_eq_true] at accepted ⊢
                  obtain ⟨off, b, hb, h⟩ := accepted
                  exact ⟨off, b, hb, ih nm h⟩
          | externalChoice p bs =>
              cases g with
              | send q l s => simp [eligibleFuel] at accepted
              | recv q l s =>
                  simp only [eligibleFuel] at accepted ⊢
                  split at accepted
                  · simp_all
                  · rename_i apart
                    rw [ite_eq_right apart]
                    obtain ⟨b, hb, h⟩ := List.any_eq_true.mp accepted
                    exact List.any_eq_true.mpr ⟨b, hb, ih nm h⟩

/-- Soundness: fuel-true implies acceptability (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem eligibleFuel_sound {n : Nat} {T : SessionType} {g : ext_tag}
    (wf : T.WellFormed) (accepted : eligibleFuel n T g = true) : Ex T g := by
  induction n generalizing T with
  | zero => simp [eligibleFuel] at accepted
  | succ n ih =>
      cases T with
      | tEnd => cases g <;> simp [eligibleFuel] at accepted
      | tVar X => cases g <;> simp [eligibleFuel] at accepted
      | tRec X B =>
          obtain ⟨V, h⟩ := ih
            (SessionType.wellFormedUnfold wf (.step .tRec (.refl _))) accepted
          exact ⟨V, .unfold h⟩
      | internalChoice bs =>
          cases g with
          | send p l s =>
              obtain ⟨⟨q, a, b, U⟩, member, keys⟩ := List.any_eq_true.mp accepted
              simp only [Bool.and_eq_true, beq_iff_eq] at keys
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := keys
              exact ⟨U, .base (.intC wf.1.triple_nodup_of_internalChoice member)⟩
          | recv q l s =>
              have accepted' : (bs.all (fun b => b.1 != q)) = true ∧
                  bs.any (fun b => eligibleFuel n b.2.2.2 (.recv q l s)) = true := by
                simpa only [eligibleFuel, Bool.and_eq_true] using accepted
              obtain ⟨off, next⟩ := accepted'
              obtain ⟨⟨r, a, b, U⟩, member, accepted⟩ := List.any_eq_true.mp next
              apply Ex_int_single wf _ member
                (ih (Drainability.wf_of_mem_intBranches member wf) accepted)
              intro p a b U member
              have h := List.all_eq_true.mp off _ member
              simpa only [bne_iff_ne, ne_comm] using h
      | externalChoice p bs =>
          cases g with
          | send q l s => simp [eligibleFuel] at accepted
          | recv q l s =>
              simp only [eligibleFuel] at accepted
              split at accepted
              · rename_i same
                have same' : p = q := beq_iff_eq.mp same
                subst q
                obtain ⟨⟨a, b, U⟩, member, keys⟩ := List.any_eq_true.mp accepted
                simp only [Bool.and_eq_true, beq_iff_eq] at keys
                obtain ⟨rfl, rfl⟩ := keys
                have unique : (bs.map fun b => (b.1, b.2.1)).Nodup := by
                  cases wf.1 with | externalChoice unique _ _ => exact nodup_of_nodup_labels unique
                exact ⟨U, .base (.extC unique member)⟩
              · rename_i apart
                obtain ⟨⟨a, b, U⟩, member, accepted⟩ := List.any_eq_true.mp accepted
                apply Ex_ext_single wf _ member
                  (ih (Drainability.wf_of_mem_extBranches member wf) accepted)
                simpa only [beq_iff_eq, ne_comm] using apart

/-- Base derivations are found at some fuel (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
private theorem base_eventually {T : SessionType} {g : ext_tag} {V : SessionType}
    (step : mon_tr_yes_base T g V) : ∃ n, eligibleFuel n T g = true := by
  induction step with
  | intC _ member =>
      refine ⟨1, List.any_eq_true.mpr ⟨_, member, ?_⟩⟩
      simp
  | extC _ member =>
      refine ⟨1, ?_⟩
      simp only [eligibleFuel, beq_self_eq_true, ite_true]
      exact List.any_eq_true.mpr ⟨_, member, by simp⟩
  | tRec _ ih =>
      obtain ⟨n, h⟩ := ih
      exact ⟨n + 1, h⟩

/-- Eventual completeness: every derivation is found at some fuel (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem eligible_eventually {T : SessionType} {g : ext_tag} {V : SessionType}
    (step : mon_tr_yes_exist T g V) : ∃ n, eligibleFuel n T g = true := by
  induction step with
  | base base => exact base_eventually base
  | @pfxInt bs kept q l s V nonempty off eq all unique keys ih =>
      obtain ⟨⟨r, a, b, W⟩, retained⟩ := List.exists_mem_of_ne_nil kept nonempty.2
      obtain ⟨U, member⟩ := keys r a b W retained
      obtain ⟨n, h⟩ := ih U W r a b member retained
      refine ⟨n + 1, ?_⟩
      simp only [eligibleFuel, Bool.and_eq_true]
      constructor
      · apply List.all_eq_true.mpr
        rintro ⟨p, a, b, U⟩ member
        simpa only [bne_iff_ne] using Ne.symm (off p a b U member)
      · exact List.any_eq_true.mpr ⟨_, member, h⟩
  | @pfxExt p bs kept q l s V nonempty off eq all unique keys ih =>
      obtain ⟨⟨a, b, W⟩, retained⟩ := List.exists_mem_of_ne_nil kept nonempty.2
      obtain ⟨U, member⟩ := keys a b W retained
      obtain ⟨n, h⟩ := ih U W a b member retained
      refine ⟨n + 1, ?_⟩
      simp only [eligibleFuel, beq_eq_false_iff_ne.mpr (Ne.symm off), Bool.false_eq_true,
        ite_false]
      exact List.any_eq_true.mpr ⟨_, member, h⟩
  | unfold _ ih =>
      obtain ⟨n, h⟩ := ih
      exact ⟨n + 1, h⟩

-- ================================================================
-- Finite traversal closure.
-- ================================================================


/-! # Finite traversal + uniform fuel bound.

A computable finite closure (`traversalNodes`) of all `PruneStep`-reachable
nodes, closure (`traversalNodes_closed`), node-count bound
(`traversalNodes_length`), and the stabilization argument yielding
`eligibility_correct`: `eligibility T g = true ↔ Ex T g` with fuel
`syntaxNodes T`.
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>.
Adapted to `Nest`'s `SessionType`/`WellFormed`/`fv` (same shape).
-/

/-- Node count equals syntax-node count (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem traversalNodes_length (T : SessionType) (ρ : env) :
    (traversalNodes ρ T).length = syntaxNodes T := by
  induction T using session_induction generalizing ρ with
  | done => simp [traversalNodes, syntaxNodes]
  | var X => simp [traversalNodes, syntaxNodes]
  | rec X B ih =>
      simp [traversalNodes, syntaxNodes, ih]
      omega
  | intC bs ih =>
      simp only [traversalNodes, List.length_cons, syntaxNodes]
      suffices (bs.flatMap (fun b => traversalNodes ρ b.2.2.2)).length = internalNodes bs by omega
      induction bs with
      | nil => rfl
      | cons b bs next =>
          simp only [List.flatMap_cons, List.length_append, internalNodes]
          rw [ih b (by simp) ρ, next (fun c hc => ih c (by simp [hc]))]
  | extC p bs ih =>
      simp only [traversalNodes, List.length_cons, syntaxNodes]
      suffices (bs.flatMap (fun b => traversalNodes ρ b.2.2)).length = externalNodes bs by omega
      induction bs with
      | nil => rfl
      | cons b bs next =>
          simp only [List.flatMap_cons, List.length_append, externalNodes]
          rw [ih b (by simp) ρ, next (fun c hc => ih c (by simp [hc]))]

/-- Closed node lists are closed under prune steps (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem traversalNodes_closed {T U V : SessionType} (closed : T.IsClosed)
    (member : U ∈ traversalNodes [] T) (step : PruneStep U V) :
    V ∈ traversalNodes [] T := by
  have envClosed : env_closed [] := by intro x value member; cases member
  have covered : ∀ x ∈ T.fv, elookup [] x ≠ none := by
    intro x member
    simp [SessionType.IsClosed] at closed
    simp [closed] at member
  rcases traversalNodes_step T [] envClosed covered member step with next | ⟨x, absent⟩
  · exact next
  · cases absent

/-- Boolean-list congruence helper (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
private theorem any_congr_mem {α : Type*} (bs : List α) (p q : α → Bool)
    (same : ∀ b ∈ bs, p b = q b) : bs.any p = bs.any q := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor <;> rintro ⟨b, hb, h⟩
  · exact ⟨b, hb, (same b hb) ▸ h⟩
  · exact ⟨b, hb, (same b hb).symm ▸ h⟩

/-- Equal fuel on children gives equal fuel at the parent (port).
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
private theorem eligibleFuel_congr {n m : Nat} {T : SessionType} {g : ext_tag}
    (same : ∀ U, PruneStep T U → eligibleFuel n U g = eligibleFuel m U g) :
    eligibleFuel (n + 1) T g = eligibleFuel (m + 1) T g := by
  cases T with
  | tEnd => cases g <;> rfl
  | tVar X => cases g <;> rfl
  | tRec X B => exact same _ .trec
  | internalChoice bs =>
      cases g with
      | send p l s => rfl
      | recv p l s =>
          simp only [eligibleFuel]
          congr 1
          exact any_congr_mem bs _ _ (fun b hb => same _ (.intC hb))
  | externalChoice p bs =>
      cases g with
      | send q l s => rfl
      | recv q l s =>
          simp only [eligibleFuel]
          split
          · rfl
          · exact any_congr_mem bs _ _ (fun b hb => same _ (.extC hb))

/-- Uniform bound: acceptance at any fuel implies acceptance at
`syntaxNodes` fuel (port). The marks filter over `traversalNodes`
is monotone, cardinality-bounded by `syntaxNodes T`, and stabilizes;
equality propagates forward through `eligibleFuel_congr` closedness.
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
private theorem eligibleFuel_bounded {T : SessionType} (closed : T.IsClosed)
    (g : ext_tag) {U : SessionType} (member : U ∈ traversalNodes [] T)
    {n : Nat} (accepted : eligibleFuel n U g = true) :
    eligibleFuel (syntaxNodes T) U g = true := by
  classical
  let nodes := (traversalNodes [] T).toFinset
  let marks (n : Nat) := nodes.filter (fun U => eligibleFuel n U g = true)
  have mono {n m : Nat} (le : n ≤ m) : marks n ⊆ marks m := by
    intro V hv
    obtain ⟨hv, yes⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hv, eligibleFuel_mono le yes⟩
  have fromEqual {n m : Nat} (equal : marks n = marks m) {V : SessionType}
      (hv : V ∈ traversalNodes [] T) : eligibleFuel n V g = eligibleFuel m V g := by
    apply Bool.eq_iff_iff.mpr
    have node : V ∈ nodes := List.mem_toFinset.mpr hv
    have h := Finset.ext_iff.mp equal V
    simpa only [marks, Finset.mem_filter, node, true_and] using h
  have propagation {n m : Nat} (equal : marks n = marks m) : marks (n + 1) = marks (m + 1) := by
    apply Finset.ext
    intro V
    by_cases hv : V ∈ nodes
    · have eq : eligibleFuel (n + 1) V g = eligibleFuel (m + 1) V g := by
        apply eligibleFuel_congr
        intro W step
        exact fromEqual equal (traversalNodes_closed closed (List.mem_toFinset.mp hv) step)
      simp only [marks, Finset.mem_filter, hv, true_and, eq]
    · simp [marks, hv]
  have card_mono : Monotone (fun n => (marks n).card) := fun _ _ le => Finset.card_le_card (mono le)
  have card_bound : ∀ n, (marks n).card ≤ syntaxNodes T := by
    intro n
    calc
      (marks n).card ≤ nodes.card := Finset.card_filter_le _ _
      _ ≤ (traversalNodes [] T).length := List.toFinset_card_le _
      _ = syntaxNodes T := traversalNodes_length T []
  have card_prop (n : Nat) (equal : (marks n).card = (marks (n + 1)).card) :
      (marks (n + 1)).card = (marks (n + 2)).card := by
    have eq : marks n = marks (n + 1) :=
      Finset.eq_of_subset_of_card_le (mono (Nat.le_succ n)) equal.ge
    exact congrArg Finset.card (propagation eq)
  have all_equal {m : Nat} (le : syntaxNodes T ≤ m) : marks (syntaxNodes T) = marks m := by
    apply Finset.eq_of_subset_of_card_le (mono le)
    exact (Nat.stabilises_of_monotone card_mono card_bound card_prop le).le
  have at_max := eligibleFuel_mono (Nat.le_max_left n (syntaxNodes T)) accepted
  have eq := fromEqual (all_equal (Nat.le_max_right n (syntaxNodes T))) member
  exact eq ▸ at_max

/-- Full correctness: bounded search decides acceptability (port).
This is the small-model property discharging the oracle gap:
fuel `syntaxNodes T` always suffices.
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
theorem eligibility_correct {T : SessionType} {g : ext_tag} (wf : T.WellFormed) :
    eligibility T g = true ↔ Ex T g := by
  constructor
  · exact eligibleFuel_sound wf
  · rintro ⟨V, step⟩
    obtain ⟨n, h⟩ := eligible_eventually step
    apply eligibleFuel_bounded wf.2.1 g _ h
    simpa only [ssubst_nil] using traversalNodes_root T []

-- ================================================================
-- Branch filtering (keep/drop).
-- ================================================================


/-! # Keep/drop branch retention.

Selective retention (`KRint`/`KRext`, computable `retainInt`/`retainExt`):
keep iff eligible (`E`), drop otherwise, with
coverage/correspondence/sublist lemmas.
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>.
Adapted to `Nest`'s branch-tuple types (same shapes).
-/

/-- Computable keep/drop for internal branches (port).
`decE` decides eligibility per branch; `next` builds the sub-witness.
Termination is structural on the branch list.
Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def retainInt (E : SessionType → Prop) (P : SessionType → SessionType → Prop)
    (bs : List (Role × Lab × DataSort × SessionType))
    (decE : ∀ r l s T, (r, l, s, T) ∈ bs → Decidable (E T))
    (next : ∀ r l s T, (r, l, s, T) ∈ bs → E T → {U // P T U}) :
    {kept // KRint E P bs kept} := by
  induction bs with
  | nil => exact ⟨[], .nil⟩
  | cons b bs ih =>
      rcases b with ⟨r, l, s, T⟩
      let rest := ih
        (fun r l s T hm => decE r l s T (List.mem_cons_of_mem _ hm))
        (fun r l s T hm => next r l s T (List.mem_cons_of_mem _ hm))
      letI := decE r l s T List.mem_cons_self
      by_cases he : E T
      · let child := next r l s T List.mem_cons_self he
        exact ⟨(r, l, s, child.val) :: rest.val, .keep he child.property rest.property⟩
      · exact ⟨rest.val, .drop he rest.property⟩

/-- Computable keep/drop for external branches (port; see `retainInt` for credit). -/
def retainExt (E : SessionType → Prop) (P : SessionType → SessionType → Prop)
    (bs : List (Lab × DataSort × SessionType))
    (decE : ∀ l s T, (l, s, T) ∈ bs → Decidable (E T))
    (next : ∀ l s T, (l, s, T) ∈ bs → E T → {U // P T U}) :
    {kept // KRext E P bs kept} := by
  induction bs with
  | nil => exact ⟨[], .nil⟩
  | cons b bs ih =>
      rcases b with ⟨l, s, T⟩
      let rest := ih
        (fun l s T hm => decE l s T (List.mem_cons_of_mem _ hm))
        (fun l s T hm => next l s T (List.mem_cons_of_mem _ hm))
      letI := decE l s T List.mem_cons_self
      by_cases he : E T
      · let child := next l s T List.mem_cons_self he
        exact ⟨(l, s, child.val) :: rest.val, .keep he child.property rest.property⟩
      · exact ⟨rest.val, .drop he rest.property⟩


/-- Completeness of the guardedness check: `Guarded` implies `guardedCheck`. -/
theorem SessionType.guardedCheck_complete {X : String} {T : SessionType}
    (h : SessionType.Guarded X T) : SessionType.guardedCheck X T = true := by
  cases T with
  | tEnd => rfl
  | tVar Y =>
    simp only [SessionType.guardedCheck]
    have h' : X ≠ Y := h
    simp [h']
  | internalChoice _ => rfl
  | externalChoice _ _ => rfl
  | tRec Y T' =>
    simp only [SessionType.guardedCheck]
    exact SessionType.guardedCheck_complete (h : SessionType.Guarded X T')

/-- `wfCheckInt` is true when every branch target checks. -/
theorem SessionType.wfCheckInt_complete {bound : List String}
    {bs : List (Role × Lab × DataSort × SessionType)}
    (hall : ∀ x ∈ bs, SessionType.wfCheck bound x.2.2.2 = true) :
    SessionType.wfCheckInt bound bs = true := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [SessionType.wfCheckInt, Bool.and_eq_true]
    constructor
    · exact hall _ (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (fun x hx => hall x (List.mem_cons.mpr (Or.inr hx)))

/-- `wfCheckExt` is true when every branch target checks. -/
theorem SessionType.wfCheckExt_complete {bound : List String}
    {bs : List (Lab × DataSort × SessionType)}
    (hall : ∀ x ∈ bs, SessionType.wfCheck bound x.2.2 = true) :
    SessionType.wfCheckExt bound bs = true := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [SessionType.wfCheckExt, Bool.and_eq_true]
    constructor
    · exact hall _ (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (fun x hx => hall x (List.mem_cons.mpr (Or.inr hx)))

/-- Forward: branch-target free variables occur in the choice. -/
private theorem fv_goInt_fwd {bs : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} {T0 : SessionType} {Y : String}
    (hmem : (p, lab, S, T0) ∈ bs) (hY : Y ∈ T0.fv) :
    Y ∈ SessionType.fv (SessionType.internalChoice bs) := by
  induction bs with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨p', lab', S', T'⟩
    simp only [SessionType.fv, SessionType.fv.goInt, List.mem_append] at *
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | hmem
    · exact Or.inl hY
    · exact Or.inr (ih hmem)

/-- Forward (external): branch-target free variables occur in the choice. -/
private theorem fv_goExt_fwd {p : Role} {bs : List (Lab × DataSort × SessionType)}
    {lab : Lab} {S : DataSort} {T0 : SessionType} {Y : String}
    (hmem : (lab, S, T0) ∈ bs) (hY : Y ∈ T0.fv) :
    Y ∈ SessionType.fv (SessionType.externalChoice p bs) := by
  induction bs with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨lab', S', T'⟩
    simp only [SessionType.fv, SessionType.fv.goExt, List.mem_append] at *
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
    · exact Or.inl hY
    · exact Or.inr (ih hmem)

/-- Completeness auxiliary: `NoDupl` + `Contractive` + free variables in
scope imply `wfCheck`. By induction on a size fuel bound (mirrors
`wfCheck_sound_aux` in `Nest/MonitorCo.lean`). -/
theorem SessionType.wfCheck_complete_aux (n : Nat) : ∀ (bound : List String) (T : SessionType),
    sizeOf T < n → T.NoDupl → T.Contractive →
    (∀ X, X ∈ T.fv → X ∈ bound) → T.wfCheck bound = true := by
  induction n with
  | zero =>
    intro bound T hlt _ _ _
    omega
  | succ n ih =>
    intro bound T hlt hND hCo hfv
    cases T with
    | tEnd => rfl
    | tVar X =>
      simp only [SessionType.wfCheck]
      have hfvX : X ∈ (SessionType.tVar X).fv := by simp [SessionType.fv]
      have hX : X ∈ bound := hfv X hfvX
      simp [hX]
    | internalChoice branches =>
      have hND' : SessionType.NoDupl (SessionType.internalChoice branches) := hND
      cases hND' with
      | internalChoice h_nodup h_nonempty h_branches =>
        have heq : SessionType.wfCheck bound (SessionType.internalChoice branches) =
            (decide (branches ≠ []) &&
            decide ((branches.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)).Nodup) &&
            SessionType.wfCheckInt bound branches) := rfl
        rw [heq]
        simp only [Bool.and_eq_true]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simp [h_nonempty]
        · simp [h_nodup]
        · apply SessionType.wfCheckInt_complete
          intro x hx
          obtain ⟨r, l, s, T0⟩ := x
          have hmem : sizeOf T0 < n := by
            have h1 := sizeOf_SessionType_lt_sizeOf_internalChoice hx
            omega
          have hND0 := h_branches _ hx
          have hCo0 : T0.Contractive := by
            cases hCo with
            | internalChoice h => exact h _ hx
          have hfv0 : ∀ X, X ∈ T0.fv → X ∈ bound := by
            intro X hX
            apply hfv
            exact fv_goInt_fwd hx hX
          exact ih _ _ hmem hND0 hCo0 hfv0
    | externalChoice p branches =>
      have hND' : SessionType.NoDupl (SessionType.externalChoice p branches) := hND
      cases hND' with
      | externalChoice h_nodup h_nonempty h_branches =>
        have heq : SessionType.wfCheck bound (SessionType.externalChoice p branches) =
            (decide (branches ≠ []) &&
            decide ((branches.map fun x : Lab × DataSort × SessionType => x.1).Nodup) &&
            SessionType.wfCheckExt bound branches) := rfl
        rw [heq]
        simp only [Bool.and_eq_true]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simp [h_nonempty]
        · simp [h_nodup]
        · apply SessionType.wfCheckExt_complete
          intro x hx
          obtain ⟨l, s, T0⟩ := x
          have hmem : sizeOf T0 < n := by
            have h1 := sizeOf_SessionType_lt_sizeOf_externalChoice (p := p) hx
            omega
          have hND0 := h_branches _ hx
          have hCo0 : T0.Contractive := by
            cases hCo with
            | externalChoice h => exact h _ hx
          have hfv0 : ∀ X, X ∈ T0.fv → X ∈ bound := by
            intro X hX
            apply hfv
            exact fv_goExt_fwd hx hX
          exact ih _ _ hmem hND0 hCo0 hfv0
    | tRec X B =>
      have hNDB : B.NoDupl := by
        cases hND with
        | tRec h => exact h
      have hCoB : B.Contractive := by
        cases hCo with
        | tRec hC _ => exact hC
      have hG : SessionType.Guarded X B := by
        cases hCo with
        | tRec _ hG => exact hG
      have hBsize : sizeOf B < n := by
        have h1 : sizeOf B < sizeOf (SessionType.tRec X B) := by simp
        omega
      have hfvB : ∀ Y, Y ∈ B.fv → Y ∈ X :: bound := by
        intro Y hY
        by_cases heq : Y = X
        · subst heq; simp
        · exact List.mem_cons.mpr (Or.inr (hfv Y (by simp [SessionType.fv, heq, hY])))
      simp only [SessionType.wfCheck, Bool.and_eq_true]
      exact ⟨ih _ _ hBsize hNDB hCoB hfvB, SessionType.guardedCheck_complete hG⟩

/-- Completeness of the executable check: `WellFormed` implies `wfCheck`. -/
theorem SessionType.wfCheck_complete {T : SessionType}
    (h : T.WellFormed) : T.wfCheck [] = true := by
  obtain ⟨hND, hCl, hCo⟩ := h
  apply SessionType.wfCheck_complete_aux (sizeOf T + 1) [] T (Nat.lt_succ_self _) hND hCo
  intro X hX
  unfold SessionType.IsClosed at hCl
  rw [hCl] at hX
  exact absurd hX (by simp)

-- ================================================================
-- Executable choice/rest/observe.
-- Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
-- Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>.
-- `Drainability.PruneStep` vs top-level `PruneStep`: we use the top-level
-- `PruneStep` from `MonitorCoBase` (same shape as `Drainability.PruneStep`)
-- for consistency with `traversalNodes`.
-- ================================================================

/-- Base observation at head (port; see header for credit). -/
private def baseAtHead (H : SessionType) (wf : H.WellFormed) (normal : IsHeadNF H)
    (g : ext_tag) : PSum {V // mon_tr_yes_base H g V} (∀ V, ¬ mon_tr_yes_base H g V) := by
  cases H with
  | internalChoice bs =>
      cases g with
      | recv q l s => exact .inr (by intro V hb; cases hb)
      | send p l s =>
          by_cases hm : ∃ b ∈ bs, int_key3 b = (p, l, s)
          · let b := List.chooseX (fun b => int_key3 b = (p, l, s)) bs hm
            apply PSum.inl
            refine ⟨b.val.2.2.2, .intC wf.1.triple_nodup_of_internalChoice ?_⟩
            have eq : (p, l, s, b.val.2.2.2) = b.val := by
              have hk := b.property.2
              simp only [int_key3, Prod.mk.injEq] at hk
              exact Prod.ext hk.1.symm (Prod.ext hk.2.1.symm (Prod.ext hk.2.2.symm rfl))
            rw [eq]
            exact b.property.1
          · exact .inr (by intro V hb; cases hb with | intC _ mem => exact hm ⟨_, mem, rfl⟩)
  | externalChoice p bs =>
      cases g with
      | send q l s => exact .inr (by intro V hb; cases hb)
      | recv q l s =>
          by_cases hp : p = q
          · subst q
            by_cases hm : ∃ b ∈ bs, ext_key2 b = (l, s)
            · let b := List.chooseX (fun b => ext_key2 b = (l, s)) bs hm
              apply PSum.inl
              refine ⟨b.val.2.2, .extC (nodup_ext_key2_of_wf wf) ?_⟩
              have eq : (l, s, b.val.2.2) = b.val := by
                have hk := b.property.2
                simp only [ext_key2, Prod.mk.injEq] at hk
                exact Prod.ext hk.1.symm (Prod.ext hk.2.symm rfl)
              rw [eq]
              exact b.property.1
            · exact .inr (by intro V hb; cases hb with | extC _ mem => exact hm ⟨_, mem, rfl⟩)
          · exact .inr (by intro V hb; cases hb; exact hp rfl)
  | tEnd => exact .inr (by intro V hb; cases hb)
  | tVar X => exact .inr (by intro V hb; cases hb)
  | tRec X B => exact normal.elim

private theorem intRequirements {bs : List (Role × Lab × DataSort × SessionType)} {q lab S : String}
    -- NOTE: `lab S` shadow outer names; keep explicit to match fold shape.
    (he : Ex (.internalChoice bs) (.recv q lab S)) :
    bs ≠ [] ∧ (∀ r l s T, (r, l, s, T) ∈ bs → q ≠ r) ∧
      ∃ r l s T, (r, l, s, T) ∈ bs ∧ Ex T (.recv q lab S) := by
  obtain ⟨V, he⟩ := he
  cases he with
  | base hb => cases hb
  | @pfxInt _ kept _ _ _ _ hne hno _ hall _ hkey =>
      obtain ⟨⟨r, l, s, U⟩, hm⟩ := List.exists_mem_of_ne_nil kept hne.2
      obtain ⟨T, ht⟩ := hkey r l s U hm
      exact ⟨hne.1, hno, r, l, s, T, ht, U, hall T U r l s ht hm⟩

private theorem extRequirements {p : Role} {bs : List (Lab × DataSort × SessionType)}
    {q lab S : String}
    (he : Ex (.externalChoice p bs) (.recv q lab S))
    (noBase : ∀ V, ¬ mon_tr_yes_base (.externalChoice p bs) (.recv q lab S) V) :
    bs ≠ [] ∧ q ≠ p ∧ ∃ l s T, (l, s, T) ∈ bs ∧ Ex T (.recv q lab S) := by
  obtain ⟨V, he⟩ := he
  cases he with
  | base hb => exact (noBase _ hb).elim
  | @pfxExt _ _ kept _ _ _ _ hne hneq _ hall _ hkey =>
      obtain ⟨⟨l, s, U⟩, hm⟩ := List.exists_mem_of_ne_nil kept hne.2
      obtain ⟨T, ht⟩ := hkey l s U hm
      exact ⟨hne.1, hneq, l, s, T, ht, U, hall T U l s ht hm⟩

private def buildPrefix {G H q lab S} (wf : H.WellFormed) (normal : IsHeadNF H)
    (eligible : Ex H (.recv q lab S))
    (noBase : ∀ V, ¬ mon_tr_yes_base H (.recv q lab S) V)
    (decE : ∀ C, PruneStep H C → Decidable (Ex C (.recv q lab S)))
    (next : ∀ C, PruneStep H C → Ex C (.recv q lab S) →
      {V // fchild G C (.recv q lab S) V}) : {V // fmon G H (.recv q lab S) V} := by
  cases H with
  | internalChoice bs =>
      let kept := retainInt (fun T => Ex T (.recv q lab S))
        (fun T U => fchild G T (.recv q lab S) U) bs
        (fun _ _ _ _ hm => decE _ (.intC hm))
        (fun _ _ _ _ hm he => next _ (.intC hm) he)
      refine ⟨.internalChoice kept.val, .fm_pfxInt (intRequirements eligible).1 ?_
        (intRequirements eligible).2.1 ?_ ?_ ?_ ?_ (KRint_sublist3 kept.property)⟩
      · obtain ⟨r, l, s, T, hm, he⟩ := (intRequirements eligible).2.2
        obtain ⟨U, hu, _⟩ := KRint_cover kept.property hm he
        exact List.ne_nil_of_mem hu
      · intro T U r l s hm hu
        obtain ⟨T', hm', _, hp⟩ := KRint_kept_mem kept.property hu
        have eq := unique_target_of_nodup_int wf.1.triple_nodup_of_internalChoice hm hm'
        subst T'
        exact hp
      · exact (KRint_sublist2 kept.property).nodup (nodup_int_key_of_wf wf)
      · intro r l s U hu
        obtain ⟨T, hm, he, _⟩ := KRint_kept_mem kept.property hu
        exact ⟨T, hm, he⟩
      · intro r l s T hm he
        obtain ⟨U, hu, _⟩ := KRint_cover kept.property hm he
        exact ⟨U, hu⟩
  | externalChoice p bs =>
      let kept := retainExt (fun T => Ex T (.recv q lab S))
        (fun T U => fchild G T (.recv q lab S) U) bs
        (fun _ _ _ hm => decE _ (.extC hm))
        (fun _ _ _ hm he => next _ (.extC hm) he)
      refine ⟨.externalChoice p kept.val,
        .fm_pfxExt (extRequirements eligible noBase).1 ?_
          (extRequirements eligible noBase).2.1 ?_ ?_ ?_ ?_ (KRext_sublist2 kept.property)⟩
      · obtain ⟨l, s, T, hm, he⟩ := (extRequirements eligible noBase).2.2
        obtain ⟨U, hu, _⟩ := KRext_cover kept.property hm he
        exact List.ne_nil_of_mem hu
      · intro T U l s hm hu
        obtain ⟨T', hm', _, hp⟩ := KRext_kept_mem kept.property hu
        have eq := unique_target_of_nodup_ext (nodup_ext_key2_of_wf wf) hm hm'
        subst T'
        exact hp
      · exact (KRext_sublist1 kept.property).nodup (nodup_ext_key_of_wf wf)
      · intro l s U hu
        obtain ⟨T, hm, he, _⟩ := KRext_kept_mem kept.property hu
        exact ⟨T, hm, he⟩
      · intro l s T hm he
        obtain ⟨U, hu, _⟩ := KRext_cover kept.property hm he
        exact ⟨U, hu⟩
  | tRec X B => exact normal.elim
  | tEnd =>
      have impossible : False := by obtain ⟨V, h⟩ := eligible; cases h with | base hb => cases hb
      exact impossible.elim
  | tVar X =>
      have impossible : False := by obtain ⟨V, h⟩ := eligible; cases h with | base hb => cases hb
      exact impossible.elim

private def selectBase
    (headFn : ∀ T : SessionType, T.WellFormed → {H // hnf T H})
    (T : SessionType) (wf : T.WellFormed) (g : ext_tag) :
    PSum {V // mon_tr_yes_base T g V} (∀ V, ¬ mon_tr_yes_base T g V) := by
  let H := headFn T wf
  cases baseAtHead H.val (SessionType.wellFormedUnfold wf H.property.1) H.property.2 g with
  | inl result => exact .inl ⟨result.val, base_unfoldstar_lift H.property.1 result.property⟩
  | inr absent =>
      apply PSum.inr
      intro V hb
      obtain ⟨K, hK, direct⟩ := base_hnf hb
      have eq : K = H.val := hnf_unique hK H.property
      subst eq
      exact absent V (base_of_hnf (hnf_self H.property.2) direct)

private def childFromFrame [DecidableEq SessionType] {g G C}
    (frame : C ∉ G.map Prod.fst → Ex C g → {V // fmon G C g V})
    (eligible : Ex C g) : {V // fchild G C g V} := by
  by_cases hin : C ∈ G.map Prod.fst
  · have found : ∃ b ∈ G, b.1 = C := by
      obtain ⟨b, hm, eq⟩ := List.mem_map.mp hin
      exact ⟨b, hm, eq⟩
    let b := List.chooseX (fun b : SessionType × String => b.1 = C) G found
    refine ⟨.tVar b.val.2, .fc_fold ?_⟩
    have eq : (C, b.val.2) = b.val := Prod.ext b.property.2.symm rfl
    rw [eq]
    exact b.property.1
  · let result := frame hin eligible
    exact ⟨result.val, .fc_go hin result.property⟩


private theorem preserveReach {R : SessionType → Prop}
    (step : ∀ T U, R T → PruneStep T U → R U) {T U}
    (hR : R T) (path : Relation.ReflTransGen PruneStep T U) : R U := by
  induction path with
  | refl => exact hR
  | tail hs hu ih => exact step _ _ ih hu

private def choiceFrame [DecidableEq SessionType] {G T g}
    (choice : IsChoice T) (wf : T.WellFormed) (eligible : Ex T g)
    (decE : ∀ C, PruneStep T C → Decidable (Ex C g))
    (next : ∀ C, PruneStep T C → C ∉ G.map Prod.fst → Ex C g →
      {V // fmon G C g V}) : {V // fmon G T g V} := by
  have normal : IsHeadNF T := by cases T <;> simp_all [IsChoice, IsHeadNF]
  cases baseAtHead T wf normal g with
  | inl result => exact ⟨result.val, .fm_base result.property⟩
  | inr absent =>
      cases g with
      | send p l s =>
          have impossible : False := by
            obtain ⟨V, hb⟩ := Ex_send_base eligible
            exact absent V hb
          exact impossible.elim
      | recv q lab S =>
          exact buildPrefix wf normal eligible absent decE
            (fun C hs he => childFromFrame (next C hs) he)

private def buildFrame [DecidableEq SessionType]
    (R : SessionType → Prop)
    (wf : ∀ T, R T → T.WellFormed)
    (step : ∀ T U, R T → PruneStep T U → R U)
    (headFn : ∀ T : SessionType, T.WellFormed → {H // hnf T H})
    (g : ext_tag) (decE : ∀ T, R T → Decidable (Ex T g))
    (L : Finset SessionType) (G : FCtx) (T : SessionType)
    (cover : ∀ U, R U → U ∉ G.map Prod.fst → U ∈ L)
    (hR : R T) (fresh : T ∉ G.map Prod.fst) (eligible : Ex T g) :
    {V // fmon G T g V} := by
  have hW := wf T hR
  cases T with
  | internalChoice bs =>
      apply choiceFrame (T := .internalChoice bs) trivial hW eligible
        (fun C hs => decE C (step _ C hR hs))
      intro C hs freshC eligibleC
      have smaller : sizeOf C < sizeOf (.internalChoice bs : SessionType) := by
        cases hs with
        | intC hm => exact sizeOf_SessionType_lt_sizeOf_internalChoice hm
      exact buildFrame R wf step headFn g decE L G C cover
        (step _ C hR hs) freshC eligibleC
  | externalChoice p bs =>
      apply choiceFrame (T := .externalChoice p bs) trivial hW eligible
        (fun C hs => decE C (step _ C hR hs))
      intro C hs freshC eligibleC
      have smaller : sizeOf C < sizeOf (.externalChoice p bs : SessionType) := by
        cases hs with
        | extC hm => exact sizeOf_SessionType_lt_sizeOf_externalChoice hm
      exact buildFrame R wf step headFn g decE L G C cover
        (step _ C hR hs) freshC eligibleC
  | tEnd =>
      have impossible : False := by obtain ⟨V, h⟩ := eligible; cases h with | base hb => cases hb
      exact impossible.elim
  | tVar X =>
      have impossible : False := by obtain ⟨V, h⟩ := eligible; cases h with | base hb => cases hb
      exact impossible.elim
  | tRec X B =>
      cases selectBase headFn (.tRec X B) hW g with
      | inl result => exact ⟨result.val, .fm_base result.property⟩
      | inr absent =>
          let H := headFn (.tRec X B) hW
          let G' : FCtx := ((.tRec X B, fvar G.length) :: G)
          let L' := L.erase (.tRec X B)
          have cover' : ∀ U, R U → U ∉ G'.map Prod.fst → U ∈ L' := by
            intro U hU hnU
            apply Finset.mem_erase.mpr
            constructor
            · intro eq
              subst U
              exact hnU (by simp [G'])
            · exact cover U hU (fun hm => hnU (by simp [G', hm]))
          have hRH := preserveReach step hR (unfoldstar_prune H.property.1)
          have hWH := wf H.val hRH
          have hEH := (Ex_unfoldstar H.property.1).mp eligible
          have body : {V // fmon G' H.val g V} := by
            cases g with
            | send p l s =>
                have impossible : False := by
                  obtain ⟨V, hbase⟩ := Ex_send_base hEH
                  exact absent V (base_unfoldstar_lift H.property.1 hbase)
                exact impossible.elim
            | recv q lab S =>
                apply buildPrefix hWH H.property.2 hEH
                  (fun V hbase => absent V (base_unfoldstar_lift H.property.1 hbase))
                  (fun C hs => decE C (step H.val C hRH hs))
                intro C hs eligibleC
                apply childFromFrame ?_ eligibleC
                intro freshC eligibleC
                exact buildFrame R wf step headFn (.recv q lab S) decE L' G' C cover'
                  (step H.val C hRH hs) freshC eligibleC
          exact ⟨mkRec (fvar G.length) body.val, .fm_rec H.property.1 H.property.2 body.property⟩
termination_by (L.card, sizeOf T)
decreasing_by
  · apply Prod.Lex.right
    subst T
    exact smaller
  · apply Prod.Lex.right
    subst T
    exact smaller
  · exact Prod.Lex.left _ _ (Finset.card_erase_lt_of_mem (cover _ hR fresh))

namespace FmonCompute
/-- Construct one fold residual when eligibility holds (see header for credit). -/
def residual (T : SessionType) (wf : T.WellFormed) (g : ext_tag)
    (eligible : Ex T g) : {U // fmon [] T g U} := by
  let R := fun U => Relation.ReflTransGen PruneStep T U
  have wfR : ∀ U, R U → U.WellFormed := by
    intro U path
    induction path with
    | refl => exact wf
    | tail _ next ih => exact prune_step_wf next ih
  let decE (U : SessionType) (reach : R U) : Decidable (Ex U g) :=
    if he : eligibility U g = true then
      .isTrue ((eligibility_correct (wfR U reach)).mp he)
    else .isFalse (fun he' => he ((eligibility_correct (wfR U reach)).mpr he'))
  let nodes := (traversalNodes [] T).toFinset
  have cover : ∀ U, R U → U ∉ ([] : FCtx).map Prod.fst → U ∈ nodes := by
    intro U reach _
    apply List.mem_toFinset.mpr
    induction reach with
    | refl => simpa [ssubst_nil] using traversalNodes_root T []
    | tail _ next ih => exact traversalNodes_closed wf.2.1 (ih (by simp)) next
  exact buildFrame R wfR (fun _ _ path next => path.tail next)
    (fun U wfU => ⟨head U, head_correct wfU⟩)
    g decE nodes [] T cover .refl (by simp) eligible

/-- A terminating observation procedure (port; see header for credit).
`none` means the observation is rejected. -/
def observe (T : SessionType) (wf : T.WellFormed) (g : ext_tag) : Option SessionType :=
  if he : eligibility T g = true then
    some (residual T wf g ((eligibility_correct wf).mp he)).val
  else none

/-- Head tags (see header for credit). -/
def headTags : SessionType → List ext_tag
  | .internalChoice bs => bs.map fun b => .send b.1 b.2.1 b.2.2.1
  | .externalChoice p bs => bs.map fun b => .recv p b.1 b.2.1
  | _ => []

/-- The finite observation alphabet (port; see header for credit). -/
def alphabet (T : SessionType) : List ext_tag :=
  ((traversalNodes [] T).flatMap headTags).dedup

/-- All accepted observations, each paired with a computed fold residual
(port; see header for credit). -/
def outgoing (T : SessionType) (wf : T.WellFormed) : List (ext_tag × SessionType) :=
  (alphabet T).filterMap fun g => (observe T wf g).map (g, ·)
end FmonCompute

/-- Executable monitor transition function.
Based on work by Jules Jacobs <jules.jacobs@inf.ethz.ch> and
Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>. -/
def mon_tr_yes_co_fun (T : SessionType) : List (ext_tag × SessionType) :=
  if h : T.wfCheck [] = true then
    FmonCompute.outgoing T (SessionType.wfCheck_sound h)
  else []

/-- `mon_tr_yes_co_fun` agrees with `outgoing` on well-formed types (via
`wfCheck_complete`). -/
theorem mon_tr_yes_co_fun_eq_outgoing {T : SessionType} (hT : T.WellFormed) :
    mon_tr_yes_co_fun T = FmonCompute.outgoing T hT := by
  unfold mon_tr_yes_co_fun
  have hcheck : T.wfCheck [] = true := SessionType.wfCheck_complete hT
  simp [hcheck]

/-- Every `observe` success carries an `fmon` derivation. -/
theorem observe_sound {T : SessionType} {wf : T.WellFormed} {g : ext_tag} {T' : SessionType}
    (h : FmonCompute.observe T wf g = some T') : fmon [] T g T' := by
  unfold FmonCompute.observe at h
  split at h
  · next he =>
    have hres := (FmonCompute.residual T wf g ((eligibility_correct wf).mp he)).property
    simp at h
    subst h
    exact hres
  · simp at h

/-- Every `outgoing` pair carries an `fmon` derivation. -/
theorem outgoing_sound {T : SessionType} {wf : T.WellFormed} {g : ext_tag} {T' : SessionType}
    (hmem : (g, T') ∈ FmonCompute.outgoing T wf) : fmon [] T g T' := by
  unfold FmonCompute.outgoing at hmem
  rw [List.mem_filterMap] at hmem
  obtain ⟨g', _, hmap⟩ := hmem
  cases hobs : FmonCompute.observe T wf g' with
  | none =>
    simp [hobs] at hmap
  | some T'' =>
    simp [hobs] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    exact observe_sound hobs

/-- Well-formedness of `mon_tr_yes_co_fun` outputs. -/
theorem mon_tr_yes_co_fun_wf {T : SessionType} {γ : ext_tag} {T' : SessionType}
    (hT : T.WellFormed) (hmem : (γ, T') ∈ mon_tr_yes_co_fun T) :
    T'.WellFormed := by
  rw [mon_tr_yes_co_fun_eq_outgoing hT] at hmem
  exact fmon_preserves_wf hT (outgoing_sound hmem)

-- ================================================================
-- Soundness.
-- ================================================================


/-- Soundness of `mon_tr_yes_co_fun` outputs. -/
theorem mon_tr_yes_co_fun_sound {T : SessionType} {γ : ext_tag} {T' : SessionType}
    (hT : T.WellFormed) (hmem : (γ, T') ∈ mon_tr_yes_co_fun T) :
    mon_tr_yes_co T γ T' hT (mon_tr_yes_co_fun_wf hT hmem) := by
  have hWf : T'.WellFormed := mon_tr_yes_co_fun_wf hT hmem
  have hmem_out : (γ, T') ∈ FmonCompute.outgoing T hT := by
    rw [← mon_tr_yes_co_fun_eq_outgoing hT]
    exact hmem
  exact fmon_implies_mon_tr_yes_co hT hWf (outgoing_sound hmem_out)

-- ================================================================
-- Alphabet membership + completeness.
-- Credit: Jules Jacobs <jules.jacobs@inf.ethz.ch> and
-- Nate Foster <nate.foster@epfl.ch> and Kristýna Petrlíková <auburn@kam.mff.cuni.cz>.
-- `mon_tr_yes_co_fun_complete` is an assembly proof.
-- ================================================================

private theorem base_tag_reachable {T U : SessionType} {g : ext_tag}
    (step : mon_tr_yes_base T g U) :
    ∃ H, Relation.ReflTransGen PruneStep T H ∧ g ∈ FmonCompute.headTags H := by
  induction step with
  | intC _ member => exact ⟨_, .refl, List.mem_map.mpr ⟨_, member, rfl⟩⟩
  | extC _ member => exact ⟨_, .refl, List.mem_map.mpr ⟨_, member, rfl⟩⟩
  | tRec _ ih =>
      obtain ⟨H, path, member⟩ := ih
      exact ⟨H, (Relation.ReflTransGen.single .trec).trans path, member⟩

private theorem exist_tag_reachable {T U : SessionType} {g : ext_tag}
    (step : mon_tr_yes_exist T g U) :
    ∃ H, Relation.ReflTransGen PruneStep T H ∧ g ∈ FmonCompute.headTags H := by
  induction step with
  | base step => exact base_tag_reachable step
  | @pfxInt branches kept q l s V nonempty off eq all unique keys ih =>
      obtain ⟨⟨r, a, b, W⟩, retained⟩ := List.exists_mem_of_ne_nil kept nonempty.2
      obtain ⟨U, member⟩ := keys r a b W retained
      obtain ⟨H, path, tag⟩ := ih U W r a b member retained
      exact ⟨H, (Relation.ReflTransGen.single (.intC member)).trans path, tag⟩
  | @pfxExt p branches kept q l s V nonempty off eq all unique keys ih =>
      obtain ⟨⟨a, b, W⟩, retained⟩ := List.exists_mem_of_ne_nil kept nonempty.2
      obtain ⟨U, member⟩ := keys a b W retained
      obtain ⟨H, path, tag⟩ := ih U W a b member retained
      exact ⟨H, (Relation.ReflTransGen.single (.extC member)).trans path, tag⟩
  | unfold _ ih =>
      obtain ⟨H, path, member⟩ := ih
      exact ⟨H, (Relation.ReflTransGen.single .trec).trans path, member⟩

theorem eligible_mem_alphabet {T : SessionType} {g : ext_tag}
    (closed : T.IsClosed) (eligible : Ex T g) : g ∈ FmonCompute.alphabet T := by
  obtain ⟨U, step⟩ := eligible
  obtain ⟨H, path, tag⟩ := exist_tag_reachable step
  have member : H ∈ traversalNodes [] T := by
    clear tag
    induction path with
    | refl => simpa only [ssubst_nil] using traversalNodes_root T []
    | tail path next ih => exact traversalNodes_closed closed ih next
  exact List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨H, member, tag⟩)

/-- `mon_tr_yes_co_fun` completeness up to `Eqv`: every coinductive step
    target is equivalent to a computed output. This is the `Eqv`-ending twin
    of `mon_tr_yes_co_fun_complete` (same assembly, no unfolding step). -/
theorem mon_tr_yes_co_fun_complete_eqv {T T' : SessionType} {γ : ext_tag}
    (hT : T.WellFormed) (hT' : T'.WellFormed)
    (h : mon_tr_yes_co T γ T' hT hT') :
    ∃ T'', (γ, T'') ∈ mon_tr_yes_co_fun T ∧ Eqv T' T'' := by
  have hPrune : Prune γ T T' := co_implies_Prune hT hT' h
  have hEx : Ex T γ := Ex_of_Prune hT hPrune
  have hAlpha : γ ∈ FmonCompute.alphabet T := eligible_mem_alphabet hT.2.1 hEx
  have hElig : eligibility T γ = true := (eligibility_correct hT).mpr hEx
  let T'' := (FmonCompute.residual T hT γ hEx).val
  have hFmon : fmon [] T γ T'' := (FmonCompute.residual T hT γ hEx).property
  have hT'' : T''.WellFormed := fmon_preserves_wf hT hFmon
  have hObs : FmonCompute.observe T hT γ = some T'' := by
    unfold FmonCompute.observe
    simp only [hElig, dite_true]
    rfl
  have hmem_out : (γ, T'') ∈ FmonCompute.outgoing T hT := by
    unfold FmonCompute.outgoing
    rw [List.mem_filterMap]
    exact ⟨γ, hAlpha, by simp [hObs]⟩
  have hmem_fun : (γ, T'') ∈ mon_tr_yes_co_fun T := by
    rw [mon_tr_yes_co_fun_eq_outgoing hT]
    exact hmem_out
  have hPrune2 : Prune γ T T'' := fmon_spec hT hFmon
  have hEqv : Eqv T' T'' := Prune_unique hT hPrune hPrune2
  exact ⟨T'', hmem_fun, hEqv⟩

theorem mon_tr_yes_co_fun_complete {T T' : SessionType} {γ : ext_tag}
    (hT : T.WellFormed) (hT' : T'.WellFormed)
    (h : mon_tr_yes_co T γ T' hT hT') :
    ∃ T'', (γ, T'') ∈ mon_tr_yes_co_fun T ∧ T'.UnfoldEquiv T'' := by
  obtain ⟨T'', hmem, hEqv⟩ := mon_tr_yes_co_fun_complete_eqv hT hT' h
  exact ⟨T'', hmem,
    eqv_implies_unfoldEquiv hT' (mon_tr_yes_co_fun_wf hT hmem) hEqv⟩
