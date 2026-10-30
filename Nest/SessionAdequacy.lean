import Nest.Drainability

/-!
# SessionAdequacy: monitor adequacy (prunability) and cover derivations.

Deep adequacy (`Prunable`, one-message prunability `PrunableOneMsg`, exposure
`ExposedFrom`) transported from `forced_step` cycles; `Has`-through-substitution
helpers; direct `Has` covers; fuel-free prune derivations (`go_unfold_rel`) with
maximal-derivation assembly; and the `monitor_fold_aux` absorption assembly feeding the comm correspondence.
Single prerequisite of the cover layer (`CoverDeep`) and the soundness
theorem: `Network.Prunable` is defined from `_root_.Prunable` here.
-/

section PrunableOneMsgDef

/-- Forced-step relation for a fixed target message `(p, lab, S)`: mirrors
    `go_unfold_rel` filtering without building monitor derivations. `trec` always
    unfolds; off-role (`extCQ`) and `intC` traversals keep `Has`-true branch
    targets only; owner-head choices (`extC_p`), misses, `tEnd`/`tVar` have
    no steps (they resolve by leaf rules needing no sub-derivation). -/
inductive forced_step (p : Role) (lab : Lab) (S : DataSort) :
    SessionType → SessionType → Prop where
  | trec {X : String} {B : SessionType} :
      forced_step p lab S (SessionType.tRec X B)
        (substSessionType B X (SessionType.tRec X B))
  | extCQ {q : Role} {branches : List (Lab × DataSort × SessionType)}
      {x : Lab × DataSort × SessionType} (hne : q ≠ p) (hmem : x ∈ branches)
      (hHas : pruneFirstInputDeepHas p lab S x.2.2 = true) :
      forced_step p lab S (SessionType.externalChoice q branches) x.2.2
  | intC {branches : List (Role × Lab × DataSort × SessionType)}
      {x : Role × Lab × DataSort × SessionType} (hmem : x ∈ branches)
      (hHas : pruneFirstInputDeepHas p lab S x.2.2.2 = true) :
      forced_step p lab S (SessionType.internalChoice branches) x.2.2.2

/-- One-message prunability for a fixed target message: no non-trivial
    forced-step cycle reachable from `T` (cycle = a step out of a reachable
    state that can return). Over the `Has`-filtered `forced_step` relation, so
    productive recursion (e.g. `CxT`-style, whose prune cycles never fire)
    is admitted while `KxT`-style `Has`-inherited loops are rejected. -/
def PrunableOneMsg (p : Role) (lab : Lab) (S : DataSort) (T : SessionType) : Prop :=
  ∀ (U V : SessionType), Relation.ReflTransGen (forced_step p lab S) T U →
    forced_step p lab S U V → ¬ Relation.ReflTransGen (forced_step p lab S) V U

end PrunableOneMsgDef

section DeepAdequacy

/-- Deep adequacy: reachability of an `externalChoice` offering by
    traversing only choices not involving its owner (inductive witness
    over branch descent, no booleans). -/
inductive ExposedFrom : SessionType → Role → Lab → DataSort → Prop where
  | extC_here {p : Role} {branches : List (Lab × DataSort × SessionType)}
      {lab : Lab} {S : DataSort} {T' : SessionType}
      (hmem : (lab, S, T') ∈ branches) :
      ExposedFrom (SessionType.externalChoice p branches) p lab S
  | extC_step {q : Role} {branches : List (Lab × DataSort × SessionType)}
      {p : Role} {lab : Lab} {S : DataSort} {x : Lab × DataSort × SessionType}
      (hne : q ≠ p) (hmem : x ∈ branches)
      (hsub : ExposedFrom x.2.2 p lab S) :
      ExposedFrom (SessionType.externalChoice q branches) p lab S
  | intC_step {branches : List (Role × Lab × DataSort × SessionType)}
      {p : Role} {lab : Lab} {S : DataSort}
      {x : Role × Lab × DataSort × SessionType}
      (hmem : x ∈ branches) (hne : x.1 ≠ p)
      (hsub : ExposedFrom x.2.2.2 p lab S) :
      ExposedFrom (SessionType.internalChoice branches) p lab S
  | trec {X : String} {B : SessionType} {p : Role} {lab : Lab} {S : DataSort}
      (hsub : ExposedFrom B p lab S) :
      ExposedFrom (SessionType.tRec X B) p lab S

/-- Deep adequacy: structural heredity (branch targets, unfolded bodies)
    plus, at every node, per-exposed-triple one-message prunability. The
    seen list bounds `tRec` traversal: fresh binders unfold once and are
    recorded, revisits close (cut) carrying only the prunability premise. -/
inductive Prunable : List SessionType → SessionType → Prop where
  | tEnd (seen : List SessionType) : Prunable seen SessionType.tEnd
  | tvar (seen : List SessionType) (X : String) :
      Prunable seen (SessionType.tVar X)
  | intC (seen : List SessionType)
      (branches : List (Role × Lab × DataSort × SessionType))
      (hPrunableBranch : ∀ x ∈ branches, Prunable seen x.2.2.2)
      (hOneMsgAll : ∀ (p : Role) (lab : Lab) (S : DataSort),
        ExposedFrom (SessionType.internalChoice branches) p lab S →
        PrunableOneMsg p lab S (SessionType.internalChoice branches)) :
      Prunable seen (SessionType.internalChoice branches)
  | extC (seen : List SessionType) (p : Role)
      (branches : List (Lab × DataSort × SessionType))
      (hPrunableBranch : ∀ x ∈ branches, Prunable seen x.2.2)
      (hOneMsgAll : ∀ (pm : Role) (lab : Lab) (S : DataSort),
        ExposedFrom (SessionType.externalChoice p branches) pm lab S →
        PrunableOneMsg pm lab S (SessionType.externalChoice p branches)) :
      Prunable seen (SessionType.externalChoice p branches)
  | trec_new (seen : List SessionType) (X : String) (B : SessionType)
      (hnmem : (SessionType.tRec X B) ∉ seen)
      (hPrunableSub : Prunable ((SessionType.tRec X B) :: seen)
        (substSessionType B X (SessionType.tRec X B)))
      (hOneMsgAll : ∀ (p : Role) (lab : Lab) (S : DataSort),
        ExposedFrom (SessionType.tRec X B) p lab S →
        PrunableOneMsg p lab S (SessionType.tRec X B)) :
      Prunable seen (SessionType.tRec X B)
  | trec_seen (seen : List SessionType) (X : String) (B : SessionType)
      (hmem : (SessionType.tRec X B) ∈ seen)
      (hOneMsgAll : ∀ (p : Role) (lab : Lab) (S : DataSort),
        ExposedFrom (SessionType.tRec X B) p lab S →
        PrunableOneMsg p lab S (SessionType.tRec X B)) :
      Prunable seen (SessionType.tRec X B)

-- Projection: deep adequacy delivers per-message acyclicity at exposed triples.
/-- Projection: deep adequacy delivers per-message prunability at exposed triples. -/
theorem deep_has_acyclic {seen : List SessionType} {T : SessionType}
    (hPrunable : Prunable seen T) :
    ∀ (p : Role) (lab : Lab) (S : DataSort),
    ExposedFrom T p lab S → PrunableOneMsg p lab S T := by
  cases hPrunable with
  | tEnd _ =>
    intro p lab S hexp
    cases hexp
  | tvar _ _ =>
    intro p lab S hexp
    cases hexp
  | intC _ _ _ hOneMsgAll =>
    intro p lab S hexp
    exact hOneMsgAll p lab S hexp
  | extC _ po bro _ hOneMsgAll =>
    intro p lab S hexp
    exact hOneMsgAll p lab S hexp
  | trec_new _ _ _ _ _ hOneMsgAll =>
    intro p lab S hexp
    exact hOneMsgAll p lab S hexp
  | trec_seen _ _ _ _ hOneMsgAll =>
    intro p lab S hexp
    exact hOneMsgAll p lab S hexp

end DeepAdequacy

section HasExposedBridge

-- Has-true implies exposure (proved, no fuel): a `Has`-true computation path
-- converts to an `ExposedFrom` derivation. Uses the in-file `any`-existence
-- shape plus size induction (`sizeOf` target < node, via list-membership).
/-- List-membership size bound: a member of an internal-choice branch list is no bigger than the
   list. -/
theorem sizeOf_mem_int_le (bs : List (Role × Lab × DataSort × SessionType))
    (x : Role × Lab × DataSort × SessionType) (hmem : x ∈ bs) :
    sizeOf x ≤ sizeOf bs := by
  induction bs with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp; omega
    · have h2 := ih hmem
      simp; omega

/-- List-membership size bound: a member of an external-choice branch list is no bigger than the
   list. -/
theorem sizeOf_mem_ext_le (bs : List (Lab × DataSort × SessionType))
    (x : Lab × DataSort × SessionType) (hmem : x ∈ bs) :
    sizeOf x ≤ sizeOf bs := by
  induction bs with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp; omega
    · have h2 := ih hmem
      simp; omega

/-- A true `pruneAllNonP` verdict means no branch is sent by `p`. -/
theorem prune_all_non_p_ne_of_true (p : Role)
    (bs : List (Role × Lab × DataSort × SessionType))
    (h : pruneAllNonP p bs = true) :
    ∀ x ∈ bs, x.1 ≠ p := by
  induction bs with
  | nil => intro x hx; simp at hx
  | cons hd tl ih =>
    obtain ⟨q0, l0, s0, U0⟩ := hd
    simp only [pruneAllNonP, Bool.and_eq_true] at h
    obtain ⟨hHd, hTl⟩ := h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · intro hcon
      have hq : q0 = p := by simpa using hcon
      exact (bne_iff_ne.mp hHd) hq
    · exact ih hTl x hmem

/-- A true internal-choice `Has`-verdict is witnessed by a `Has`-true branch target. -/
theorem prune_has_deep_int_any_exists_of_true (p : Role) (lab : Lab) (S : DataSort)
    (bs : List (Role × Lab × DataSort × SessionType))
    (h : pruneHasDeepIntAny p lab S bs = true) :
    ∃ x ∈ bs, pruneFirstInputDeepHas p lab S x.2.2.2 = true := by
  induction bs with
  | nil => simp [pruneHasDeepIntAny] at h
  | cons hd tl ih =>
    obtain ⟨q0, l0, s0, U0⟩ := hd
    simp only [pruneHasDeepIntAny] at h
    have hOr : pruneFirstInputDeepHas p lab S U0 = true ∨
        pruneHasDeepIntAny p lab S tl = true := by
      cases hU : pruneFirstInputDeepHas p lab S U0 <;> simp_all
    rcases hOr with hU | hTl
    · exact ⟨(q0, l0, s0, U0), List.mem_cons.mpr (Or.inl rfl), hU⟩
    · obtain ⟨x, hmem, hHas⟩ := ih hTl
      exact ⟨x, List.mem_cons.mpr (Or.inr hmem), hHas⟩

/-- A true external-choice `Has`-verdict is witnessed by a `Has`-true branch target. -/
theorem prune_has_deep_ext_exists_of_true (p : Role) (lab : Lab) (S : DataSort)
    (bs : List (Lab × DataSort × SessionType))
    (h : pruneHasDeepExt p lab S bs = true) :
    ∃ x ∈ bs, pruneFirstInputDeepHas p lab S x.2.2 = true := by
  induction bs with
  | nil => simp [pruneHasDeepExt] at h
  | cons hd tl ih =>
    obtain ⟨l0, s0, U0⟩ := hd
    simp only [pruneHasDeepExt] at h
    have hOr : pruneFirstInputDeepHas p lab S U0 = true ∨
        pruneHasDeepExt p lab S tl = true := by
      cases hU : pruneFirstInputDeepHas p lab S U0 <;> simp_all
    rcases hOr with hU | hTl
    · exact ⟨(l0, s0, U0), List.mem_cons.mpr (Or.inl rfl), hU⟩
    · obtain ⟨x, hmem, hHas⟩ := ih hTl
      exact ⟨x, List.mem_cons.mpr (Or.inr hmem), hHas⟩

/-- A true boolean `any` scan for `(lab, S)` yields a matching branch target. -/
theorem direct_any_exists_of_true (lab : Lab) (S : DataSort)
    (bs : List (Lab × DataSort × SessionType))
    (h : bs.any (fun b => match b with | (l, S', _) => l == lab && S' == S) = true) :
    ∃ T', (lab, S, T') ∈ bs := by
  induction bs with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨l0, s0, U0⟩ := hd
    simp only [List.any_cons] at h
    simp only [Bool.or_eq_true] at h
    rcases h with hHd | hTl
    · have hBoth : (l0 == lab) = true ∧ (s0 == S) = true := by
        cases hl : (l0 == lab) <;> cases hs : (s0 == S) <;> simp_all
      have hl : l0 = lab := beq_iff_eq.mp hBoth.1
      have hs : s0 = S := beq_iff_eq.mp hBoth.2
      subst hl; subst hs
      exact ⟨U0, List.mem_cons.mpr (Or.inl rfl)⟩
    · obtain ⟨T', hmem⟩ := ih hTl
      exact ⟨T', List.mem_cons.mpr (Or.inr hmem)⟩

/-- `Has`-true implies exposure, by strong size induction: the `Has`-true computation path converts
   to an `ExposedFrom` derivation. -/
theorem has_to_exposed_aux (n : Nat) :
    ∀ (T : SessionType), sizeOf T < n → ∀ (p : Role) (lab : Lab) (S : DataSort),
    pruneFirstInputDeepHas p lab S T = true → ExposedFrom T p lab S := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hSize p lab S hHas
    cases T with
    | tEnd => simp [pruneFirstInputDeepHas] at hHas
    | tVar X => simp [pruneFirstInputDeepHas] at hHas
    | tRec X B =>
      simp only [pruneFirstInputDeepHas] at hHas
      have hlt : sizeOf B < sizeOf (SessionType.tRec X B) := by simp
      exact ExposedFrom.trec (ih _ hSize B hlt p lab S hHas)
    | internalChoice branches =>
      simp only [pruneFirstInputDeepHas, Bool.and_eq_true] at hHas
      obtain ⟨hAll, hAny⟩ := hHas
      obtain ⟨x, hmem, hHasX⟩ := prune_has_deep_int_any_exists_of_true p lab S branches hAny
      obtain ⟨r0, l0, s0, U0⟩ := x
      have hne : (r0, l0, s0, U0).1 ≠ p :=
        prune_all_non_p_ne_of_true p branches hAll _ hmem
      have hne' : r0 ≠ p := by simpa using hne
      have hlt : sizeOf U0 < sizeOf (SessionType.internalChoice branches) := by
        have h1 : sizeOf (r0, l0, s0, U0) ≤ sizeOf branches :=
          sizeOf_mem_int_le branches (r0, l0, s0, U0) hmem
        simp at h1 ⊢; omega
      have hsub := ih _ hSize U0 hlt p lab S hHasX
      exact ExposedFrom.intC_step hmem hne' hsub
    | externalChoice q branches =>
      by_cases heq : (q == p) = true
      · have hqp : q = p := beq_iff_eq.mp heq
        simp only [pruneFirstInputDeepHas, heq] at hHas
        obtain ⟨T', hmem⟩ := direct_any_exists_of_true lab S branches hHas
        subst hqp
        exact ExposedFrom.extC_here hmem
      · have hqp : q ≠ p := fun h => heq (beq_iff_eq.mpr h)
        simp only [pruneFirstInputDeepHas, heq] at hHas
        obtain ⟨x, hmem, hHasX⟩ := prune_has_deep_ext_exists_of_true p lab S branches hHas
        obtain ⟨l0, s0, U0⟩ := x
        have hlt : sizeOf U0 < sizeOf (SessionType.externalChoice q branches) := by
          have h1 : sizeOf (l0, s0, U0) ≤ sizeOf branches :=
            sizeOf_mem_ext_le branches (l0, s0, U0) hmem
          simp at h1 ⊢; omega
        have hsub := ih _ hSize U0 hlt p lab S hHasX
        exact ExposedFrom.extC_step hqp hmem hsub

/-- `Has`-true implies exposure: any `Has`-true type exposes the triple. -/
theorem has_to_exposed (p : Role) (lab : Lab) (S : DataSort) (T : SessionType)
    (h : pruneFirstInputDeepHas p lab S T = true) : ExposedFrom T p lab S :=
  has_to_exposed_aux (sizeOf T + 1) T (Nat.lt_succ_self _) p lab S h

-- Seen-growth monotonicity: a larger visited set only adds cuts, so `Deep`
-- persists. The `trec_new` case falls back to `trec_seen` when the binder is
-- already visited in the larger set.
/-- Seen-growth monotonicity: a larger visited set only adds cuts, so `Prunable` persists. -/
theorem deep_mono_grow : ∀ {seen seen' : List SessionType} {T : SessionType},
    seen.Sublist seen' → Prunable seen T → Prunable seen' T := by
  intro seen seen' T hsub hPrunable
  induction hPrunable generalizing seen' with
  | tEnd s =>
    exact Prunable.tEnd seen'
  | tvar s X =>
    exact Prunable.tvar seen' X
  | intC s branches hPrunableBranch hOneMsgAll ih =>
    exact Prunable.intC seen' branches (fun x hx => ih x hx hsub) hOneMsgAll
  | extC s p branches hPrunableBranch hOneMsgAll ih =>
    exact Prunable.extC seen' p branches (fun x hx => ih x hx hsub) hOneMsgAll
  | trec_new s X B hnmem hPrunableSub hOneMsgAll ih =>
    by_cases hmem' : (SessionType.tRec X B) ∈ seen'
    · exact Prunable.trec_seen seen' X B hmem' hOneMsgAll
    · exact Prunable.trec_new seen' X B hmem' (ih (hsub.cons_cons _)) hOneMsgAll
  | trec_seen s X B hmem hOneMsgAll =>
    exact Prunable.trec_seen seen' X B (hsub.subset hmem) hOneMsgAll

end HasExposedBridge

section HasLifting

/-- `Has`-premise lifting: a choice is one-message prunable if all its
    `Has`-true branch targets are. Cycles at/below the choice contradict
    successor prunability — `forced_step` premises always carry `Has`, so the
    first-step successor is covered via `has_to_exposed` + target
    `hOneMsgAll`. Needs no exposure hypothesis on the choice itself. -/
theorem firstStep_intC {branches : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} :
    ∀ {W : SessionType},
    Relation.ReflTransGen (forced_step p lab S) (SessionType.internalChoice branches) W →
    W = SessionType.internalChoice branches ∨
    ∃ x ∈ branches, pruneFirstInputDeepHas p lab S x.2.2.2 = true ∧
      Relation.ReflTransGen (forced_step p lab S) x.2.2.2 W := by
  intro W h
  induction h with
  | refl => exact Or.inl rfl
  | tail h' hs ih =>
    rcases ih with rfl | ⟨x, hmem, hHas, hRT⟩
    · cases hs with
      | @intC _ x hmem hHas =>
        exact Or.inr ⟨x, hmem, hHas, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨x, hmem, hHas,
        hRT.trans (Relation.ReflTransGen.single hs)⟩

/-- `Has`-premise lifting at `intC`: an internal choice is one-message prunable if all its
   `Has`-true branch targets are. -/
theorem prunable_one_msg_intC_of_succ
    (branches : List (Role × Lab × DataSort × SessionType))
    (p : Role) (lab : Lab) (S : DataSort)
    (hSucc : ∀ x ∈ branches,
      pruneFirstInputDeepHas p lab S x.2.2.2 = true →
      PrunableOneMsg p lab S x.2.2.2) :
    PrunableOneMsg p lab S (SessionType.internalChoice branches) := by
  intro U V hRTC hStep hBack
  have hFirst := firstStep_intC hRTC
  rcases hFirst with rfl | ⟨x, hmem, hHas, hRT⟩
  · cases hStep with
    | @intC _ x hmem hHas =>
      exact (hSucc x hmem hHas _ _ hBack (forced_step.intC hmem hHas)) hBack
  · exact (hSucc x hmem hHas _ _ hRT hStep) hBack

/-- First forced step out of an `extC` head: any reachable state is the head itself or past a first
   step. -/
theorem firstStep_extC {q : Role} {branches : List (Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} :
    ∀ {W : SessionType},
    Relation.ReflTransGen (forced_step p lab S) (SessionType.externalChoice q branches) W →
    W = SessionType.externalChoice q branches ∨
    ∃ x ∈ branches, pruneFirstInputDeepHas p lab S x.2.2 = true ∧
      Relation.ReflTransGen (forced_step p lab S) x.2.2 W := by
  intro W h
  induction h with
  | refl => exact Or.inl rfl
  | tail h' hs ih =>
    rcases ih with rfl | ⟨x, hmem, hHas, hRT⟩
    · cases hs with
      | @extCQ _ _ x _ hmem hHas =>
        exact Or.inr ⟨x, hmem, hHas, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨x, hmem, hHas,
        hRT.trans (Relation.ReflTransGen.single hs)⟩

/-- `Has`-premise lifting at off-owner `extC`: an external choice is one-message prunable if all its
   `Has`-true branch targets are. -/
theorem prunable_one_msg_extC_of_succ
    (q : Role) (branches : List (Lab × DataSort × SessionType))
    (p : Role) (lab : Lab) (S : DataSort) (hne : q ≠ p)
    (hSucc : ∀ x ∈ branches,
      pruneFirstInputDeepHas p lab S x.2.2 = true →
      PrunableOneMsg p lab S x.2.2) :
    PrunableOneMsg p lab S (SessionType.externalChoice q branches) := by
  intro U V hRTC hStep hBack
  have hFirst := firstStep_extC hRTC
  rcases hFirst with rfl | ⟨x, hmem, hHas, hRT⟩
  · cases hStep with
    | @extCQ _ _ x _ hmem hHas =>
      exact (hSucc x hmem hHas _ _ hBack (forced_step.extCQ hne hmem hHas)) hBack
  · exact (hSucc x hmem hHas _ _ hRT hStep) hBack

-- Owner-head externalChoice: nothing is reachable except itself (any step
-- out would need `q ≠ p`), and it has no steps, so acyclicity is vacuous.
/-- Owner-head external choice is unconditionally one-message prunable: nothing is reachable except
   itself and it has no steps. -/
theorem prunable_one_msg_extC_owner
    (p : Role) (branches : List (Lab × DataSort × SessionType))
    (lab : Lab) (S : DataSort) :
    PrunableOneMsg p lab S (SessionType.externalChoice p branches) := by
  have hEq : ∀ {W : SessionType},
      Relation.ReflTransGen (forced_step p lab S)
        (SessionType.externalChoice p branches) W →
      W = SessionType.externalChoice p branches := by
    intro W h
    induction h with
    | refl => rfl
    | tail h' hs ih =>
      subst ih
      cases hs with
      | @extCQ _ _ _ hne _ _ => exact (hne rfl).elim
  intro U V hRTC hStep hBack
  have hU := hEq hRTC
  subst hU
  cases hStep with
  | @extCQ _ _ _ hne _ _ => exact (hne rfl).elim

end HasLifting

section HasHelpers
/-- Local copies of the `private` `Has`/substitution
    helpers (needed for the direct consumer lemmas below;
    identical proofs, `private` dropped). -/

theorem subst_go_ext_eq_map (X : String) (R : SessionType)
    (l : List (Lab × DataSort × SessionType)) :
    substSessionType.goExt X R l =
      l.map (fun x : Lab × DataSort × SessionType =>
        (x.1, x.2.1, substSessionType x.2.2 X R)) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨lab, S, T'⟩ := hd
    simp [substSessionType.goExt, ih]

/-- `pruneAllNonP` commutes with branchwise substitution (substitution preserves the non-`p` sender
   test). -/
theorem prune_all_non_p_subst_go_int (p : Role) (X : String) (R : SessionType)
    (l : List (Role × Lab × DataSort × SessionType)) :
    pruneAllNonP p (substSessionType.goInt X R l) = pruneAllNonP p l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨q, l', s', T0⟩ := hd
    simp [pruneAllNonP, substSessionType.goInt, ih]

/-- A false `pruneHasDeepIntAny` verdict propagates to every member branch target. -/
theorem prune_has_deep_int_any_mem_false (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (bs : List (Role × Lab × DataSort × SessionType)),
    pruneHasDeepIntAny p lab S bs = false →
    ∀ (x : Role × Lab × DataSort × SessionType), x ∈ bs →
    pruneFirstInputDeepHas p lab S x.2.2.2 = false := by
  intro bs
  induction bs with
  | nil =>
    intro _ x hx
    simp at hx
  | cons hd tl ih =>
    intro h x hx
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneHasDeepIntAny] at h
    rcases List.mem_cons.mp hx with hxh | htl
    · subst hxh
      cases hUV : pruneFirstInputDeepHas p lab S U <;> simp_all
    · have hTl : pruneHasDeepIntAny p lab S tl = false := by
        cases hTlV : pruneHasDeepIntAny p lab S tl <;> simp_all
      exact ih hTl _ htl

/-- A false `pruneHasDeepExt` verdict propagates to every member branch target. -/
theorem prune_has_deep_ext_mem_false (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (bs : List (Lab × DataSort × SessionType)),
    pruneHasDeepExt p lab S bs = false →
    ∀ (x : Lab × DataSort × SessionType), x ∈ bs →
    pruneFirstInputDeepHas p lab S x.2.2 = false := by
  intro bs
  induction bs with
  | nil =>
    intro _ x hx
    simp at hx
  | cons hd tl ih =>
    intro h x hx
    obtain ⟨l, S', U⟩ := hd
    simp only [pruneHasDeepExt] at h
    rcases List.mem_cons.mp hx with hxh | htl
    · subst hxh
      cases hUV : pruneFirstInputDeepHas p lab S U <;> simp_all
    · have hTl : pruneHasDeepExt p lab S tl = false := by
        cases hTlV : pruneHasDeepExt p lab S tl <;> simp_all
      exact ih hTl _ htl

/-- False `Has` verdicts survive substitution on internal-choice branch targets. -/
theorem prune_has_deep_int_any_map_subst_false (p : Role) (lab : Lab)
    (S : DataSort) (X : String) (R : SessionType) :
    ∀ (bs : List (Role × Lab × DataSort × SessionType)),
    (∀ (U : SessionType), U ∈ bs.map (fun x => x.2.2.2) →
      pruneFirstInputDeepHas p lab S (substSessionType U X R) = false) →
    pruneHasDeepIntAny p lab S (bs.map (fun x : Role × Lab × DataSort × SessionType =>
      (x.1, x.2.1, x.2.2.1, substSessionType x.2.2.2 X R))) = false := by
  intro bs
  induction bs with
  | nil =>
    intro _
    rfl
  | cons hd tl ih =>
    intro hall
    obtain ⟨q, l, S', U⟩ := hd
    have hU : pruneFirstInputDeepHas p lab S
        (substSessionType U X R) = false :=
      hall U (List.mem_map.mpr
        ⟨(q, l, S', U), List.mem_cons.mpr (Or.inl rfl), rfl⟩)
    have hTl : ∀ (V : SessionType),
        V ∈ List.map (fun x : Role × Lab × DataSort × SessionType => x.2.2.2) tl →
        pruneFirstInputDeepHas p lab S (substSessionType V X R) = false := by
      intro V hV
      obtain ⟨x, hmemX, hxx⟩ := List.mem_map.mp hV
      exact hall V (List.mem_map.mpr
        ⟨x, List.mem_cons.mpr (Or.inr hmemX), hxx⟩)
    simp only [List.map_cons, pruneHasDeepIntAny]
    simp [hU, ih hTl]

/-- False `Has` verdicts survive substitution on external-choice branch targets. -/
theorem prune_has_deep_ext_map_subst_false (p : Role) (lab : Lab)
    (S : DataSort) (X : String) (R : SessionType) :
    ∀ (bs : List (Lab × DataSort × SessionType)),
    (∀ (U : SessionType), U ∈ bs.map (fun x => x.2.2) →
      pruneFirstInputDeepHas p lab S (substSessionType U X R) = false) →
    pruneHasDeepExt p lab S (bs.map (fun x : Lab × DataSort × SessionType =>
      (x.1, x.2.1, substSessionType x.2.2 X R))) = false := by
  intro bs
  induction bs with
  | nil =>
    intro _
    rfl
  | cons hd tl ih =>
    intro hall
    obtain ⟨l, S', U⟩ := hd
    have hU : pruneFirstInputDeepHas p lab S
        (substSessionType U X R) = false :=
      hall U (List.mem_map.mpr
        ⟨(l, S', U), List.mem_cons.mpr (Or.inl rfl), rfl⟩)
    have hTl : ∀ (V : SessionType),
        V ∈ List.map (fun x : Lab × DataSort × SessionType => x.2.2) tl →
        pruneFirstInputDeepHas p lab S (substSessionType V X R) = false := by
      intro V hV
      obtain ⟨x, hmemX, hxx⟩ := List.mem_map.mp hV
      exact hall V (List.mem_map.mpr
        ⟨x, List.mem_cons.mpr (Or.inr hmemX), hxx⟩)
    simp only [List.map_cons, pruneHasDeepExt]
    simp [hU, ih hTl]

/-- `Has`-falsity is preserved by grafting when both the body and the graft are `Has`-free. -/
theorem deep_has_subst_false (p : Role) (lab : Lab) (S : DataSort)
    (X : String) (R : SessionType)
    (hR : pruneFirstInputDeepHas p lab S R = false) (B : SessionType)
    (hHas : pruneFirstInputDeepHas p lab S B = false) :
    pruneFirstInputDeepHas p lab S (substSessionType B X R) = false := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop := fun B =>
    pruneFirstInputDeepHas p lab S B = false →
    pruneFirstInputDeepHas p lab S (substSessionType B X R) = false
  have hC : ∀ B, C B := by
    intro B
    refine hwf.induction (α := SessionType) (C := C) (a := B) ?step
    intro B ih hHas
    cases B with
    | tEnd =>
      simp [substSessionType, pruneFirstInputDeepHas]
    | tVar W =>
      by_cases heq : X = W
      · subst heq
        simpa [substSessionType] using hR
      · simpa [substSessionType, heq] using hHas
    | internalChoice branches =>
      have hEq : substSessionType (SessionType.internalChoice branches) X R =
          SessionType.internalChoice (substSessionType.goInt X R branches) := by
        simp [substSessionType]
      rw [hEq]
      simp only [pruneFirstInputDeepHas] at hHas ⊢
      rw [prune_all_non_p_subst_go_int]
      by_cases hAll : pruneAllNonP p branches = true
      · have hAny : pruneHasDeepIntAny p lab S branches = false := by
          cases hAB : pruneHasDeepIntAny p lab S branches <;> simp_all
        have hTgt : ∀ (U : SessionType),
            U ∈ List.map (fun x : Role × Lab × DataSort × SessionType => x.2.2.2)
              branches →
            pruneFirstInputDeepHas p lab S (substSessionType U X R) = false := by
          intro U hmem
          obtain ⟨x, hmemX, hxx⟩ := List.mem_map.mp hmem
          have hUx : pruneFirstInputDeepHas p lab S x.2.2.2 = false :=
            prune_has_deep_int_any_mem_false p lab S branches hAny x hmemX
          have hlt : sizeOf x.2.2.2 <
              sizeOf (SessionType.internalChoice branches) :=
            sizeOf_SessionType_lt_sizeOf_internalChoice hmemX
          have hSU := ih x.2.2.2 hlt hUx
          rwa [hxx] at hSU
        have hAnyF := prune_has_deep_int_any_map_subst_false p lab S X R branches hTgt
        rw [go_int_eq_map]
        simp [hAll, hAnyF]
      · have hAllF : pruneAllNonP p branches = false := by
          cases hAB : pruneAllNonP p branches <;> simp_all
        simp [hAllF]
    | externalChoice q branches =>
      by_cases hbeq : (q == p) = true
      · have hqp : q = p := beq_iff_eq.mp hbeq
        subst q
        have hEq : substSessionType (SessionType.externalChoice p branches) X R =
            SessionType.externalChoice p (substSessionType.goExt X R branches) := by
          simp [substSessionType]
        rw [hEq]
        have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
        simp only [pruneFirstInputDeepHas, hif, ite_true] at hHas ⊢
        rw [subst_go_ext_eq_map, List.any_map]
        have hcomp : (fun b => match b with
            | (l, S', _) => l == lab && S' == S) ∘
            (fun x : Lab × DataSort × SessionType =>
              (x.1, x.2.1, substSessionType x.2.2 X R)) =
            (fun b => match b with
              | (l, S', _) => l == lab && S' == S) := rfl
        rw [hcomp]
        exact hHas
      · have hqp : q ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
        have hEq : substSessionType (SessionType.externalChoice q branches) X R =
            SessionType.externalChoice q (substSessionType.goExt X R branches) := by
          simp [substSessionType]
        rw [hEq]
        simp only [pruneFirstInputDeepHas, ite_eq_right hbeq] at hHas ⊢
        have hTgt : ∀ (U : SessionType),
            U ∈ List.map (fun x : Lab × DataSort × SessionType => x.2.2) branches →
            pruneFirstInputDeepHas p lab S (substSessionType U X R) = false := by
          intro U hmem
          obtain ⟨x, hmemX, hxx⟩ := List.mem_map.mp hmem
          have hUx : pruneFirstInputDeepHas p lab S x.2.2 = false :=
            prune_has_deep_ext_mem_false p lab S branches hHas x hmemX
          have hlt : sizeOf x.2.2 <
              sizeOf (SessionType.externalChoice q branches) :=
            sizeOf_SessionType_lt_sizeOf_externalChoice (p := q) hmemX
          have hSU := ih x.2.2 hlt hUx
          rwa [hxx] at hSU
        have hExtF := prune_has_deep_ext_map_subst_false p lab S X R branches hTgt
        rw [subst_go_ext_eq_map]
        exact hExtF
    | tRec Y B0 =>
      by_cases heq : X = Y
      · simpa [substSessionType, heq] using hHas
      · have hHasB0 : pruneFirstInputDeepHas p lab S B0 = false := by
          simpa [pruneFirstInputDeepHas] using hHas
        have hlt : sizeOf B0 < sizeOf (SessionType.tRec Y B0) := by simp
        have hsub := ih B0 hlt hHasB0
        simpa [substSessionType, heq, pruneFirstInputDeepHas] using hsub
  exact hC B hHas

/-- Free variables of an internal-choice branch target are free in the whole choice. -/
lemma fv_mem_of_mem_intBranches_early
    {branches : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType} {y : String}
    (hmem : x ∈ branches) (hy : y ∈ SessionType.fv x.2.2.2) :
    y ∈ SessionType.fv (SessionType.internalChoice branches) := by
  revert hmem hy
  induction branches with
  | nil =>
    intro hmem hy
    simp at hmem
  | cons b bs ih =>
    intro hmem hy
    simp at hmem
    simp only [SessionType.fv]
    rcases hmem with rfl | hmem
    · exact List.mem_append.mpr (Or.inl hy)
    · exact List.mem_append.mpr (Or.inr (ih hmem hy))

/-- Free variables of an external-choice branch target are free in the whole choice. -/
lemma fv_mem_of_mem_extBranches_early
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType} {y : String}
    (hmem : x ∈ branches) (hy : y ∈ SessionType.fv x.2.2) :
    y ∈ SessionType.fv (SessionType.externalChoice p branches) := by
  revert hmem hy
  induction branches with
  | nil =>
    intro hmem hy
    simp at hmem
  | cons b bs ih =>
    intro hmem hy
    simp at hmem
    simp only [SessionType.fv]
    rcases hmem with rfl | hmem
    · exact List.mem_append.mpr (Or.inl hy)
    · exact List.mem_append.mpr (Or.inr (ih hmem hy))

/-- Well-formedness of an internal choice descends to every member branch target. -/
theorem wf_of_mem_intBranches_early
    {branches : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType}
    (hmem : x ∈ branches)
    (hWF : (SessionType.internalChoice branches).WellFormed) :
    x.2.2.2.WellFormed := by
  obtain ⟨hND, hCl, hCt⟩ := hWF
  cases hND with
  | internalChoice _ _ hbr =>
    cases hCt with
    | internalChoice hct =>
      refine ⟨hbr _ hmem, ?_, hct _ hmem⟩
      show SessionType.fv _ = []
      cases hfv : SessionType.fv x.2.2.2 with
      | nil => rfl
      | cons y ys =>
        have hmy : y ∈ SessionType.fv x.2.2.2 := by
          rw [hfv]
          simp
        have hpar := fv_mem_of_mem_intBranches_early hmem hmy
        have hCl' : SessionType.fv
            (SessionType.internalChoice branches) = [] := hCl
        rw [hCl'] at hpar
        simp at hpar

/-- Well-formedness of an external choice descends to every member branch target. -/
theorem wf_of_mem_extBranches_early
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType}
    (hmem : x ∈ branches)
    (hWF : (SessionType.externalChoice p branches).WellFormed) :
    x.2.2.WellFormed := by
  obtain ⟨hND, hCl, hCt⟩ := hWF
  cases hND with
  | externalChoice _ _ hbr =>
    cases hCt with
    | externalChoice hct =>
      refine ⟨hbr _ hmem, ?_, hct _ hmem⟩
      show SessionType.fv _ = []
      cases hfv : SessionType.fv x.2.2 with
      | nil => rfl
      | cons y ys =>
        have hmy : y ∈ SessionType.fv x.2.2 := by
          rw [hfv]
          simp
        have hpar := fv_mem_of_mem_extBranches_early (p := p) hmem hmy
        have hCl' : SessionType.fv
            (SessionType.externalChoice p branches) = [] := hCl
        rw [hCl'] at hpar
        simp at hpar

/-- `pruneAllNonP` holds when no branch is sent by `p`. -/
theorem prune_all_non_p_true_of_all_ne (p : Role) :
    ∀ (bs : List (Role × Lab × DataSort × SessionType)),
    (∀ br ∈ bs, br.1 ≠ p) → pruneAllNonP p bs = true := by
  intro bs
  induction bs with
  | nil =>
    intro _
    rfl
  | cons hd tl ih =>
    intro hAll
    obtain ⟨q, l, S', U⟩ := hd
    have hqp : q ≠ p := hAll _ (List.mem_cons.mpr (Or.inl rfl))
    have h1 : (q != p) = true := bne_iff_ne.mpr hqp
    have h2 := ih (fun br hmem => hAll br (List.mem_cons.mpr (Or.inr hmem)))
    simp [pruneAllNonP, h1, h2]

/-- A `Has`-true branch target makes the whole internal-choice list `Has`-true. -/
theorem prune_has_deep_int_any_true_of_mem (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (bs : List (Role × Lab × DataSort × SessionType))
    (q : Role) (l : Lab) (S' : DataSort) (U : SessionType),
    pruneFirstInputDeepHas p lab S U = true →
    (q, l, S', U) ∈ bs → pruneHasDeepIntAny p lab S bs = true := by
  intro bs
  induction bs with
  | nil =>
    intro q l S' U hU hm
    simp at hm
  | cons hd tl ih =>
    intro q l S' U hU hm
    obtain ⟨q0, l0, S0, U0⟩ := hd
    simp only [pruneHasDeepIntAny]
    rcases List.mem_cons.mp hm with h | h
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp [hU]
    · have h2 := ih _ _ _ _ hU h
      simp [h2]

/-- A `Has`-true branch target makes the whole external-choice list `Has`-true. -/
theorem prune_has_deep_ext_true_of_mem (p : Role) (lab : Lab)
    (S : DataSort) (l : Lab) (S' : DataSort) (U : SessionType)
    (hU : pruneFirstInputDeepHas p lab S U = true) :
    ∀ (bs : List (Lab × DataSort × SessionType)),
    (l, S', U) ∈ bs → pruneHasDeepExt p lab S bs = true := by
  intro bs
  induction bs with
  | nil =>
    intro hm
    exact False.elim (List.not_mem_nil hm)
  | cons hd tl ih =>
    intro hm
    obtain ⟨l0, S0, U0⟩ := hd
    simp only [pruneHasDeepExt]
    rcases List.mem_cons.mp hm with h | h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp [hU]
    · have h2 := ih h
      simp [h2]

end HasHelpers

section DirectCover
/-- Direct base cover (no adequacy): a base yes-transition for a
    `recv` tag forces `Has`-true. Induction on the base
    derivation: `intC` (send tag) contradicts the `recv` tag;
    `extC` resolves the key directly; `tRec` uses the IH at the
    unfolded type plus the `subst_false` contrapositive. -/
theorem baseHas_direct (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (T : SessionType) (γ : ext_tag) (V : SessionType),
    T.WellFormed → mon_tr_yes_base T γ V →
    γ = ext_tag.recv p lab S → pruneFirstInputDeepHas p lab S T = true := by
  intro T γ V hWF h hγ
  induction h with
  | intC _ _ =>
    cases hγ
  | extC _ hmem =>
    cases hγ
    have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
    simp only [pruneFirstInputDeepHas, hif, ite_true]
    rw [List.any_eq_true]
    exact ⟨_, hmem, by simp⟩
  | @tRec X B _ _ hsub ih =>
    have hWFsub : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
      SessionType.wellFormedUnfold hWF
        (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
    have hSubT : pruneFirstInputDeepHas p lab S
        (substSessionType B X (SessionType.tRec X B)) = true :=
      ih hWFsub hγ
    by_cases hBHas : pruneFirstInputDeepHas p lab S B = true
    · simpa [pruneFirstInputDeepHas] using hBHas
    · have hBf : pruneFirstInputDeepHas p lab S B = false := by
        cases hBB : pruneFirstInputDeepHas p lab S B <;> simp_all
      have hRf : pruneFirstInputDeepHas p lab S (SessionType.tRec X B) = false := by
        simpa [pruneFirstInputDeepHas] using hBf
      have hSubF := deep_has_subst_false p lab S X (SessionType.tRec X B) hRf B hBf
      rw [hSubF] at hSubT
      simp at hSubT
/-- Direct existential cover (no adequacy): a yes-existence
    derivation for a `recv` tag forces `Has`-true. Induction on
    the derivation: `base` delegates; prefix rules pick a kept
    branch (nonempty kept + key back-mapping), apply the
    hereditary IH (branch WF/BalW from public inversions), and
    rebuild `Has` via the `any`-lemmas; `unfold` mirrors the
    base `tRec` case. The tag is fixed, so prefix roles unify
    away (no tag-equality hypothesis needed). -/
theorem existHas_direct (p : Role) (lab : Lab) (S : DataSort) :
    ∀ (T : SessionType) (γ : ext_tag) (V : SessionType),
    T.WellFormed → mon_tr_yes_exist T γ V →
    γ = ext_tag.recv p lab S → pruneFirstInputDeepHas p lab S T = true := by
  intro T γ V hWF h hγ
  induction h with
  | base hb =>
    exact baseHas_direct p lab S _ _ _ hWF hb hγ
  | @pfxInt branches kept q labS SS T' hne hno hkept hall hNodup hkey hall_ih =>
    cases hγ
    have hAllP : pruneAllNonP p branches = true :=
      prune_all_non_p_true_of_all_ne p branches (fun br hm => by
        obtain ⟨p', l', s', T0⟩ := br
        exact Ne.symm (hno p' l' s' T0 hm))
    obtain ⟨brK, hmemK⟩ := List.exists_mem_of_ne_nil kept hne.2
    obtain ⟨r, l, s, V'⟩ := brK
    obtain ⟨T0, hmem0⟩ := hkey r l s V' hmemK
    have hWFU : T0.WellFormed := wf_of_mem_intBranches_early hmem0 hWF
    have hHasT0 : pruneFirstInputDeepHas p lab S T0 = true :=
      hall_ih T0 V' r l s hmem0 hmemK hWFU rfl
    have hAny : pruneHasDeepIntAny p lab S branches = true :=
      prune_has_deep_int_any_true_of_mem p lab S branches _ _ _ _ hHasT0 hmem0
    simp [pruneFirstInputDeepHas, hAllP, hAny]
  | @pfxExt pr branches kept q labS SS T' hne hneq hkept hall hNodup hkey hall_ih =>
    cases hγ
    by_cases hbeq : (pr == p) = true
    · have hqp : pr = p := beq_iff_eq.mp hbeq
      subst hqp
      exact absurd rfl hneq
    · have hqp : pr ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
      obtain ⟨brK, hmemK⟩ := List.exists_mem_of_ne_nil kept hne.2
      obtain ⟨l, s, V'⟩ := brK
      obtain ⟨T0, hmem0⟩ := hkey l s V' hmemK
      have hWFU : T0.WellFormed := wf_of_mem_extBranches_early hmem0 hWF
      have hHasT0 : pruneFirstInputDeepHas p lab S T0 = true :=
        hall_ih T0 V' l s hmem0 hmemK hWFU rfl
      simp only [pruneFirstInputDeepHas, ite_eq_right hbeq]
      exact prune_has_deep_ext_true_of_mem p lab S _ _ _ hHasT0 _ hmem0
  | @unfold X B _ _ hsub ih =>
    have hWFsub : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
      SessionType.wellFormedUnfold hWF
        (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
    have hSubT : pruneFirstInputDeepHas p lab S
        (substSessionType B X (SessionType.tRec X B)) = true :=
      ih hWFsub hγ
    by_cases hBHas : pruneFirstInputDeepHas p lab S B = true
    · simpa [pruneFirstInputDeepHas] using hBHas
    · have hBf : pruneFirstInputDeepHas p lab S B = false := by
        cases hBB : pruneFirstInputDeepHas p lab S B <;> simp_all
      have hRf : pruneFirstInputDeepHas p lab S (SessionType.tRec X B) = false := by
        simpa [pruneFirstInputDeepHas] using hBf
      have hSubF := deep_has_subst_false p lab S X (SessionType.tRec X B) hRf B hBf
      rw [hSubF] at hSubT
      simp at hSubT

end DirectCover

section go_unfold_relation
/-- Reverse `allNonP` (from the source at `ProofsNormalization`
    791–808): a true check means every branch sender differs. -/
theorem prune_all_non_p_all_ne (p : Role) :
    ∀ (bs : List (Role × Lab × DataSort × SessionType)),
    pruneAllNonP p bs = true → ∀ br ∈ bs, br.1 ≠ p := by
  intro bs
  induction bs with
  | nil =>
    intro _ br hm
    simp at hm
  | cons hd tl ih =>
    intro h br hm
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneAllNonP] at h
    simp at h
    obtain ⟨hqp, hTl⟩ := h
    rcases List.mem_cons.mp hm with hxh | htl
    · subst hxh
      exact hqp
    · exact ih hTl _ htl

/-- A true deep-`any` check yields a reaching branch target. -/
theorem prune_has_deep_int_any_exists (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (bs : List (Role × Lab × DataSort × SessionType)),
    pruneHasDeepIntAny p lab S bs = true →
    ∃ (q : Role) (l : Lab) (S' : DataSort) (U : SessionType),
      (q, l, S', U) ∈ bs ∧ pruneFirstInputDeepHas p lab S U = true := by
  intro bs
  induction bs with
  | nil =>
    intro h
    simp [pruneHasDeepIntAny] at h
  | cons hd tl ih =>
    intro h
    obtain ⟨q, l, S', U⟩ := hd
    simp only [pruneHasDeepIntAny] at h
    simp at h
    rcases h with hU | hTl
    · exact ⟨q, l, S', U, List.mem_cons.mpr (Or.inl rfl), hU⟩
    · obtain ⟨q2, l2, S2, U2, hm2, hHasU2⟩ := ih hTl
      exact ⟨q2, l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), hHasU2⟩

/-- A true deep external check yields a reaching branch target. -/
theorem prune_has_deep_ext_exists (p : Role) (lab : Lab)
    (S : DataSort) :
    ∀ (bs : List (Lab × DataSort × SessionType)),
    pruneHasDeepExt p lab S bs = true →
    ∃ (l : Lab) (S' : DataSort) (U : SessionType),
      (l, S', U) ∈ bs ∧ pruneFirstInputDeepHas p lab S U = true := by
  intro bs
  induction bs with
  | nil =>
    intro h
    simp [pruneHasDeepExt] at h
  | cons hd tl ih =>
    intro h
    obtain ⟨l, S', U⟩ := hd
    simp only [pruneHasDeepExt] at h
    simp at h
    rcases h with hU | hTl
    · exact ⟨l, S', U, List.mem_cons.mpr (Or.inl rfl), hU⟩
    · obtain ⟨l2, S2, U2, hm2, hHasU2⟩ := ih hTl
      exact ⟨l2, S2, U2, List.mem_cons.mpr (Or.inr hm2), hHasU2⟩

/-- Fuel-free deep-prune relation (mirror of
    `pruneFirstInputDeepGoU` equations minus fuel): `tRec`
    always unfolds (subst-subderivation, explicit subterm);
    choice traversals keep `Has`-true branches only
    (matching `GoU` filtering, so `pfx`-kept aligns);
    `extC_p` resolves to its target directly; `tEnd`/`tVar`
    resolve to themselves. No fuel (nothing exhausts, no
    garbage by construction) and no cut constructor (derivations
    are finite trees; use sites close repeats by impossibility). -/
inductive go_unfold_rel (p : Role) (lab : Lab) (S : DataSort) :
    Nat → SessionType → SessionType → Prop where
  | tEnd (n : Nat) : go_unfold_rel p lab S n .tEnd .tEnd
  | tvar (n : Nat) (X : String) : go_unfold_rel p lab S n (.tVar X) (.tVar X)
  | trec (n : Nat) (X : String) (B : SessionType) (U : SessionType)
      (hsub : go_unfold_rel p lab S n (substSessionType B X (SessionType.tRec X B)) U) :
      go_unfold_rel p lab S (n + 1) (SessionType.tRec X B) U
  | intC (n : Nat) (branches kept : List (Role × Lab × DataSort × SessionType))
      (hall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
        (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
          pruneFirstInputDeepHas p lab S T0 = true → go_unfold_rel p lab S n T0 T1)
      (hkey : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
        (r, l, s, T1) ∈ kept → ∃ T0, (r, l, s, T0) ∈ branches ∧
          pruneFirstInputDeepHas p lab S T0 = true)
      (hNodupKept : List.Nodup (kept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))))
      (horder : List.Sublist (kept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)))
        (branches.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))))
      (horder3 : List.Sublist (kept.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
        (branches.map (λ x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))))
      (hfull : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
        (r, l, s, T0) ∈ branches → pruneFirstInputDeepHas p lab S T0 = true →
        ∃ T1, (r, l, s, T1) ∈ kept) :
      go_unfold_rel p lab S (n + 1) (SessionType.internalChoice branches)
        (SessionType.internalChoice kept)
  | extC_p (n : Nat) (q : Role) (branches : List (Lab × DataSort × SessionType))
      {T' : SessionType} (hq : q = p) (hmem : (lab, S, T') ∈ branches) :
      go_unfold_rel p lab S n (SessionType.externalChoice q branches) T'
  | extC_p_miss (n : Nat) (q : Role) (branches : List (Lab × DataSort × SessionType))
      (hq : q = p)
      (hmiss : ∀ x ∈ branches, ((x.1 == lab && x.2.1 == S) = false)) :
      go_unfold_rel p lab S n (SessionType.externalChoice q branches) SessionType.tEnd
  | extC_q (n : Nat) (q : Role) (branches kept : List (Lab × DataSort × SessionType))
      (hq : q ≠ p)
      (hall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
        (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
          pruneFirstInputDeepHas p lab S T0 = true → go_unfold_rel p lab S n T0 T1)
      (hkey : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
        (l, s, T1) ∈ kept → ∃ T0, (l, s, T0) ∈ branches ∧
          pruneFirstInputDeepHas p lab S T0 = true)
      (hNodupKept : List.Nodup (kept.map (λ x : Lab × DataSort × SessionType => x.1)))
      (horder : List.Sublist (kept.map (λ x : Lab × DataSort × SessionType => x.1))
        (branches.map (λ x : Lab × DataSort × SessionType => x.1)))
      (horder3 : List.Sublist (kept.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1)))
        (branches.map (λ x : Lab × DataSort × SessionType => (x.1, x.2.1))))
      (hfull : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
        (l, s, T0) ∈ branches → pruneFirstInputDeepHas p lab S T0 = true →
        ∃ T1, (l, s, T1) ∈ kept) :
      go_unfold_rel p lab S (n + 1) (SessionType.externalChoice q branches)
        (SessionType.externalChoice q kept)

end go_unfold_relation

/-- Height subsumption: derivations lift to any greater height
    (structural induction; halls re-bound pointwise). Lets callers pad
    branch heights to a uniform max. -/
theorem go_unfold_rel.mono_le (p : Role) (lab : Lab) (S : DataSort) :
    ∀ {n m : Nat} {T U : SessionType} (_d : go_unfold_rel p lab S n T U),
      n ≤ m → go_unfold_rel p lab S m T U := by
  intro n m T U _d
  induction _d generalizing m with
  | tEnd n => intro _; exact go_unfold_rel.tEnd m
  | tvar n X => intro _; exact go_unfold_rel.tvar m X
  | trec n X B U hsub ih =>
    intro hle
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact go_unfold_rel.trec k X B U (ih (by omega))
  | intC n branches kept hall hkey hNodupKept horder horder3 hfull hall_ih =>
    intro hle
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact go_unfold_rel.intC k branches kept
      (fun T0 T1 r l s hB hK hH => hall_ih T0 T1 r l s hB hK hH (by omega))
      hkey hNodupKept horder horder3 hfull
  | extC_p n q branches hq hmem =>
    intro _
    exact go_unfold_rel.extC_p m q branches hq hmem
  | extC_p_miss n q branches hq hmiss =>
    intro _
    exact go_unfold_rel.extC_p_miss m q branches hq hmiss
  | extC_q n q branches kept hq hall hkey hNodupKept horder horder3 hfull hall_ih =>
    intro hle
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact go_unfold_rel.extC_q k q branches kept hq
      (fun T0 T1 l s hB hK hH => hall_ih T0 T1 l s hB hK hH (by omega))
      hkey hNodupKept horder horder3 hfull



section MpRelation

/-- `DeepHas` pushes forward through substitution (needed for
    the `trec` case of `mp`-Relation, where `Has` must travel from the
    `tRec`-head to its unfolding). -/
theorem deep_has_subst_forward (p : Role) (lab : Lab) (S : DataSort)
    (B : SessionType) {X : String} {R : SessionType}
    (hHas : pruneFirstInputDeepHas p lab S B = true) :
    pruneFirstInputDeepHas p lab S (substSessionType B X R) = true := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop := fun B =>
    pruneFirstInputDeepHas p lab S B = true →
    pruneFirstInputDeepHas p lab S (substSessionType B X R) = true
  have hC : ∀ B, C B := by
    intro B
    refine hwf.induction (α := SessionType) (C := C) (a := B) ?step
    intro B ih hHas
    cases B with
    | tEnd =>
      simp [pruneFirstInputDeepHas] at hHas
    | tVar W =>
      simp [pruneFirstInputDeepHas] at hHas
    | internalChoice branches =>
      have hEq : substSessionType (SessionType.internalChoice branches) X R =
          SessionType.internalChoice (substSessionType.goInt X R branches) := by
        simp [substSessionType]
      rw [hEq]
      simp only [pruneFirstInputDeepHas] at hHas ⊢
      simp at hHas
      obtain ⟨hAllB, hAnyB⟩ := hHas
      have hAllEq : pruneAllNonP p (substSessionType.goInt X R branches) = true := by
        rw [prune_all_non_p_subst_go_int]
        exact hAllB
      obtain ⟨q0, l0, S0, U0, hmem0, hHasU0⟩ :=
        prune_has_deep_int_any_exists p lab S branches hAnyB
      have hlt : sizeOf U0 < sizeOf (SessionType.internalChoice branches) :=
        sizeOf_SessionType_lt_sizeOf_internalChoice hmem0
      have hHasU0' := ih U0 hlt hHasU0
      have hmemU0' : (q0, l0, S0, substSessionType U0 X R) ∈
          substSessionType.goInt X R branches := by
        rw [go_int_eq_map]
        exact List.mem_map.mpr ⟨(q0, l0, S0, U0), hmem0, rfl⟩
      have hAny' := prune_has_deep_int_any_true_of_mem p lab S _ _ _ _ _ hHasU0' hmemU0'
      simp [hAllEq, hAny']
    | externalChoice q branches =>
      by_cases hbeq : (q == p) = true
      · have hqp : q = p := beq_iff_eq.mp hbeq
        subst q
        have hEq : substSessionType (SessionType.externalChoice p branches) X R =
            SessionType.externalChoice p (substSessionType.goExt X R branches) := by
          simp [substSessionType]
        rw [hEq]
        have hif : ((p == p) = true) := beq_iff_eq.mpr rfl
        simp only [pruneFirstInputDeepHas, hif, ite_true] at hHas ⊢
        rw [List.any_eq_true] at hHas
        obtain ⟨w, hmem, hpred⟩ := hHas
        obtain ⟨l0, S0, T0⟩ := w
        have hkeys : l0 = lab ∧ S0 = S := by
          have h1 : ((l0 == lab) && (S0 == S)) = true := by
            simpa using hpred
          simp at h1
          exact h1
        obtain ⟨hlEq, hSEq⟩ := hkeys
        subst l0
        subst S0
        have hmem' : (lab, S, substSessionType T0 X R) ∈
            substSessionType.goExt X R branches := by
          rw [subst_go_ext_eq_map]
          exact List.mem_map.mpr ⟨(lab, S, T0), hmem, rfl⟩
        rw [List.any_eq_true]
        exact ⟨_, hmem', by simp⟩
      · have hqp : q ≠ p := fun h => hbeq (beq_iff_eq.mpr h)
        have hEq : substSessionType (SessionType.externalChoice q branches) X R =
            SessionType.externalChoice q (substSessionType.goExt X R branches) := by
          simp [substSessionType]
        rw [hEq]
        simp only [pruneFirstInputDeepHas, ite_eq_right hbeq] at hHas ⊢
        obtain ⟨l0, S0, U0, hmem0, hHasU0⟩ :=
          prune_has_deep_ext_exists p lab S branches hHas
        have hlt : sizeOf U0 < sizeOf (SessionType.externalChoice q branches) :=
          sizeOf_SessionType_lt_sizeOf_externalChoice (p := q) hmem0
        have hHasU0' := ih U0 hlt hHasU0
        have hmemU0' : (l0, S0, substSessionType U0 X R) ∈
            substSessionType.goExt X R branches := by
          rw [subst_go_ext_eq_map]
          exact List.mem_map.mpr ⟨(l0, S0, U0), hmem0, rfl⟩
        exact prune_has_deep_ext_true_of_mem p lab S _ _ _ hHasU0' _ hmemU0'
    | tRec Y B0 =>
      by_cases heq : X = Y
      · simpa [substSessionType, heq] using hHas
      · have hHasB0 : pruneFirstInputDeepHas p lab S B0 = true := by
          simpa [pruneFirstInputDeepHas] using hHas
        have hlt : sizeOf B0 < sizeOf (SessionType.tRec Y B0) := by simp
        have hsub := ih B0 hlt hHasB0
        simpa [substSessionType, heq, pruneFirstInputDeepHas] using hsub
  exact hC B hHas
/-- Same-key entries coincide under key-`Nodup` (revert + plain
    list induction; head/tail cross-cases contradict `Nodup`-membership). -/
theorem entry_unique_of_nodupkeys {α : Type} {β : Type} (key : α → β)
    {bs : List α} (hND : (bs.map key).Nodup) {e1 e2 : α}
    (h1 : e1 ∈ bs) (h2 : e2 ∈ bs) (hke : key e1 = key e2) : e1 = e2 := by
  revert hND h1 h2
  induction bs with
  | nil =>
    intro hND h1 h2
    simp at h1
  | cons hd tl ih =>
    intro hND h1 h2
    simp only [List.mem_cons] at h1 h2
    simp only [List.map_cons, List.nodup_cons] at hND
    rcases h1 with rfl | h1
    · rcases h2 with rfl | h2
      · rfl
      · exfalso
        have hmem : key e2 ∈ tl.map key := List.mem_map.mpr ⟨_, h2, rfl⟩
        rw [← hke] at hmem
        exact hND.1 hmem
    · rcases h2 with rfl | h2
      · exfalso
        have hmem : key e1 ∈ tl.map key := List.mem_map.mpr ⟨_, h1, rfl⟩
        rw [hke] at hmem
        exact hND.1 hmem
      · exact ih hND.2 h1 h2
end MpRelation

section Maximal

/-- Maximal-construction: a `go_unfold_rel`-derivation plus source-`Has`
    (plus WF/BalW) yields an `mon_tr_yes_exist` at the derivation value
    together with its maximality proof. Derivation-structural
    induction mirroring `mp` (`hno`/`hall`/`hkey` assembly, branch
    disambiguation by WF-`Nodup`); `hcover` via `existHas_direct`
    (acceptable ⟹ `Has`-true) + `hfull` (kept-completeness);
    `horder` is the derivation's triple-order; `hallMax` hereditary
    via the induction pairs (transported across proof-irrelevance).
    `tEnd`/`tvar`/`extC_p_miss` by `Has`-contra; `trec` via `unfold`;
    `extC_p_hit` by `base`. -/
theorem go_unfold_rel.toMaximal (p : Role) (lab : Lab) (S : DataSort)
    {n : Nat} {T U : SessionType} (d : go_unfold_rel p lab S n T U)
    (hHasT : pruneFirstInputDeepHas p lab S T = true)
    (hWF : T.WellFormed) :
    ∃ (E : mon_tr_yes_exist T (ext_tag.recv p lab S) U), mon_tr_yes_max_deriv E := by
  revert hHasT hWF
  induction d with
  | tEnd =>
    intro hHasT _hWF
    simp [pruneFirstInputDeepHas] at hHasT
  | tvar n X =>
    intro hHasT _hWF
    simp [pruneFirstInputDeepHas] at hHasT
  | trec n X B U hsub ih =>
    intro hHasT hWF
    have hHasB : pruneFirstInputDeepHas p lab S B = true := by
      simpa [pruneFirstInputDeepHas] using hHasT
    have hHasSub : pruneFirstInputDeepHas p lab S
        (substSessionType B X (SessionType.tRec X B)) = true :=
      deep_has_subst_forward p lab S B hHasB
    have hWFsub : (substSessionType B X (SessionType.tRec X B)).WellFormed :=
      SessionType.wellFormedUnfold hWF
        (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
    obtain ⟨Esub, hMsub⟩ := ih hHasSub hWFsub
    exact ⟨mon_tr_yes_exist.unfold Esub, mon_tr_yes_max_deriv.unfold hMsub⟩
  | intC n branches kept hall hkey hNodupKept horder horder3 hfull hall_ih =>
    intro hHasT hWF
    simp only [pruneFirstInputDeepHas] at hHasT
    simp at hHasT
    obtain ⟨hAllB, hAnyB⟩ := hHasT
    have hAll : ∀ br ∈ branches, br.1 ≠ p := prune_all_non_p_all_ne p branches hAllB
    have hno : ∀ (p' : Role) (lab' : Lab) (S' : DataSort) (T0 : SessionType),
        (p', lab', S', T0) ∈ branches → p ≠ p' := by
      intro p' lab' S' T0 hm
      exact Ne.symm (hAll _ hm)
    obtain ⟨q0, l0, S0, U0, hmem0, hHasU0⟩ :=
      prune_has_deep_int_any_exists p lab S branches hAnyB
    obtain ⟨T1w, hmemKw⟩ := hfull q0 l0 S0 U0 hmem0 hHasU0
    have hneK : kept ≠ [] := List.ne_nil_of_mem hmemKw
    have hneB : branches ≠ [] := hWF.1.ne_of_internalChoice
    have hNDb : (SessionType.internalChoice branches).NoDupl := hWF.1
    have hNDpair : (branches.map
        (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))).Nodup := by
      cases hNDb with
      | internalChoice hpair _ _ => exact hpair
    have hHall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
        (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
        mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1 := by
      intro T0 T1 r l s hmemB hmemK
      obtain ⟨T0', hmemB', hHasT0'⟩ := hkey r l s T1 hmemK
      have heq : (r, l, s, T0) = (r, l, s, T0') :=
        entry_unique_of_nodupkeys _ hNDpair hmemB hmemB' rfl
      have hTeq : T0 = T0' :=
        congrArg (fun x : Role × Lab × DataSort × SessionType => x.2.2.2) heq
      subst hTeq
      have hWFT0 : T0.WellFormed := wf_of_mem_intBranches_early hmemB hWF
      obtain ⟨E0, -⟩ := hall_ih T0 T1 r l s hmemB hmemK hHasT0' hHasT0' hWFT0
      exact E0
    have hkeyE : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
        (r, l, s, T1) ∈ kept → ∃ T0, (r, l, s, T0) ∈ branches := by
      intro r l s T1 hK
      obtain ⟨T0, hB, -⟩ := hkey r l s T1 hK
      exact ⟨T0, hB⟩
    have hHallMax : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort)
        (hmemB : (r, l, s, T0) ∈ branches) (hmemK : (r, l, s, T1) ∈ kept)
        (hsub : mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1),
        mon_tr_yes_max_deriv hsub := by
      intro T0 T1 r l s hmemB hmemK hsub
      obtain ⟨T0', hmemB', hHasT0'⟩ := hkey r l s T1 hmemK
      have heq : (r, l, s, T0) = (r, l, s, T0') :=
        entry_unique_of_nodupkeys _ hNDpair hmemB hmemB' rfl
      have hTeq : T0 = T0' :=
        congrArg (fun x : Role × Lab × DataSort × SessionType => x.2.2.2) heq
      subst hTeq
      have hWFT0 : T0.WellFormed := wf_of_mem_intBranches_early hmemB hWF
      obtain ⟨E0, hM0⟩ := hall_ih T0 T1 r l s hmemB hmemK hHasT0' hHasT0' hWFT0
      have heqE : E0 = hsub := proof_irrel _ _
      subst heqE
      exact hM0
    have hcover : ∀ (r : Role) (l : Lab) (s : DataSort) (T0 : SessionType),
        (r, l, s, T0) ∈ branches → (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1) →
        ∃ T1, (r, l, s, T1) ∈ kept := by
      intro r l s T0 hmemB hAcc
      obtain ⟨T1, hE⟩ := hAcc
      have hWFT0 : T0.WellFormed := wf_of_mem_intBranches_early hmemB hWF
      have hHasT0 : pruneFirstInputDeepHas p lab S T0 = true :=
        existHas_direct p lab S T0 _ _ hWFT0 hE rfl
      exact hfull r l s T0 hmemB hHasT0
    have hE : mon_tr_yes_exist (SessionType.internalChoice branches)
        (ext_tag.recv p lab S) (SessionType.internalChoice kept) :=
      mon_tr_yes_exist.pfxInt ⟨hneB, hneK⟩ hno rfl hHall hNodupKept hkeyE
    exact ⟨hE, mon_tr_yes_max_deriv.pfxInt (hne := ⟨hneB, hneK⟩) (hno := hno)
      (hkept := rfl) (hall := hHall) (hNodupKept := hNodupKept) (hkey := hkeyE)
      hHallMax hcover horder3⟩
  | extC_p n q branches hq hmem =>
    intro _hHasT hWF
    subst hq
    have hNDb : (SessionType.externalChoice q branches).NoDupl := hWF.1
    cases hNDb with
    | externalChoice hnod _ _ =>
      have hB : mon_tr_yes_base (SessionType.externalChoice q branches)
          (ext_tag.recv q lab S) _ :=
        mon_tr_yes_base.extC (nodup_of_nodup_labels hnod) hmem
      exact ⟨mon_tr_yes_exist.base hB, @mon_tr_yes_max_deriv.base _ _ _ hB⟩
  | extC_p_miss n q branches hq hmiss =>
    intro hHasT _hWF
    subst hq
    have hif : ((q == q) = true) := beq_iff_eq.mpr rfl
    simp only [pruneFirstInputDeepHas, hif, ite_true] at hHasT
    rw [List.any_eq_true] at hHasT
    obtain ⟨⟨l, S', T0⟩, hmem, hpred⟩ := hHasT
    have hT : ((l == lab) && (S' == S)) = true := by simpa using hpred
    have hF : ((l == lab) && (S' == S)) = false := by
      have h := hmiss (l, S', T0) hmem
      simpa using h
    simp [hT] at hF
  | extC_q n q branches kept hq hall hkey hNodupKept horder horder3 hfull hall_ih =>
    intro hHasT hWF
    have hbeq : ¬ ((q == p) = true) := fun h => hq (beq_iff_eq.mp h)
    simp only [pruneFirstInputDeepHas, ite_eq_right hbeq] at hHasT
    obtain ⟨l0, S0, U0, hmem0, hHasU0⟩ :=
      prune_has_deep_ext_exists p lab S branches hHasT
    obtain ⟨T1w, hmemKw⟩ := hfull l0 S0 U0 hmem0 hHasU0
    have hneK : kept ≠ [] := List.ne_nil_of_mem hmemKw
    have hneB : branches ≠ [] := hWF.1.ne_of_externalChoice
    have hNDb : (SessionType.externalChoice q branches).NoDupl := hWF.1
    have hNDlab : (branches.map
        (fun x : Lab × DataSort × SessionType => x.1)).Nodup := by
      cases hNDb with
      | externalChoice hnod _ _ => exact hnod
    have hHall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
        (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
        mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1 := by
      intro T0 T1 l s hmemB hmemK
      obtain ⟨T0', hmemB', hHasT0'⟩ := hkey l s T1 hmemK
      have heq : (l, s, T0) = (l, s, T0') :=
        entry_unique_of_nodupkeys _ hNDlab hmemB hmemB' rfl
      have hTeq : T0 = T0' :=
        congrArg (fun x : Lab × DataSort × SessionType => x.2.2) heq
      subst hTeq
      have hWFT0 : T0.WellFormed := wf_of_mem_extBranches_early hmemB hWF
      obtain ⟨E0, -⟩ := hall_ih T0 T1 l s hmemB hmemK hHasT0' hHasT0' hWFT0
      exact E0
    have hkeyE : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
        (l, s, T1) ∈ kept → ∃ T0, (l, s, T0) ∈ branches := by
      intro l s T1 hK
      obtain ⟨T0, hB, -⟩ := hkey l s T1 hK
      exact ⟨T0, hB⟩
    have hHallMax : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
        (hmemB : (l, s, T0) ∈ branches) (hmemK : (l, s, T1) ∈ kept)
        (hsub : mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1),
        mon_tr_yes_max_deriv hsub := by
      intro T0 T1 l s hmemB hmemK hsub
      obtain ⟨T0', hmemB', hHasT0'⟩ := hkey l s T1 hmemK
      have heq : (l, s, T0) = (l, s, T0') :=
        entry_unique_of_nodupkeys _ hNDlab hmemB hmemB' rfl
      have hTeq : T0 = T0' :=
        congrArg (fun x : Lab × DataSort × SessionType => x.2.2) heq
      subst hTeq
      have hWFT0 : T0.WellFormed := wf_of_mem_extBranches_early hmemB hWF
      obtain ⟨E0, hM0⟩ := hall_ih T0 T1 l s hmemB hmemK hHasT0' hHasT0' hWFT0
      have heqE : E0 = hsub := proof_irrel _ _
      subst heqE
      exact hM0
    have hcover : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
        (l, s, T0) ∈ branches → (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv p lab S) T1) →
        ∃ T1, (l, s, T1) ∈ kept := by
      intro l s T0 hmemB hAcc
      obtain ⟨T1, hE⟩ := hAcc
      have hWFT0 : T0.WellFormed := wf_of_mem_extBranches_early hmemB hWF
      have hHasT0 : pruneFirstInputDeepHas p lab S T0 = true :=
        existHas_direct p lab S T0 _ _ hWFT0 hE rfl
      exact hfull l s T0 hmemB hHasT0
    have hE : mon_tr_yes_exist (SessionType.externalChoice q branches)
        (ext_tag.recv p lab S) (SessionType.externalChoice q kept) :=
      mon_tr_yes_exist.pfxExt ⟨hneB, hneK⟩ (Ne.symm hq) rfl hHall hNodupKept hkeyE
    exact ⟨hE, mon_tr_yes_max_deriv.pfxExt (hne := ⟨hneB, hneK⟩) (hneq := Ne.symm hq)
      (hkept := rfl) (hall := hHall) (hNodupKept := hNodupKept) (hkey := hkeyE)
      hHallMax hcover horder3⟩

end Maximal

section UncondAssembly
/-- Absorption head-lift across one unfold (nonempty queues): the first
    yes-step at a `tRec` head inverts (same target), the tail is
    untouched. The nil case is correctly absent — empty absorption
    identifies the endpoint and cannot lift. Feeds the nested spine
    inductions below (unfold chains terminate by guardedness). -/
theorem monitor_fold_aux_cons_unfold_lift {T M : SessionType} {m : QueueMessage}
    {rest : Queue} {X : String} {B : SessionType}
    (hT : T = SessionType.tRec X B)
    (h : monitor_fold_aux (m :: rest) T M) :
    monitor_fold_aux (m :: rest)
      (substSessionType B X (SessionType.tRec X B)) M := by
  subst hT
  obtain ⟨p, lab, S⟩ := m
  simp only [monitor_fold_aux] at h ⊢
  obtain ⟨Tmid, hYes, hTail⟩ := h
  exact ⟨Tmid, mon_tr_yes_trec_inv hYes, hTail⟩

/-- Output-liveness for a send step, general (mirror of
    `monitor_fold_aux_out_aux_norec` with `WellFormed` for `NoRec`/`NoDupl`):
    outer queue induction with `T` generalized; `tRec`-headed entries
    discharge by nested spine inductions (nil and cons queues fixed
    separately — the nil case needs no absorption lift, the cons case
    lifts one unfold). Needs only well-formedness. -/
theorem monitor_fold_aux_out_aux_general {Q : Queue} {T T' M : SessionType}
    {p : Role} {lab : Lab} {S : DataSort}
    (hTWF : T.WellFormed)
    (hST : st_trans T (st_label.out p lab S) T')
    (hEnc : monitor_fold (T, Q) M)
    (hAcc : ∃ M', monitor_fold (T', Q) M') :
    ∃ M', monitor_fold (T', Q) M' ∧ mon_tr_yes M (ext_tag.send p lab S) M' := by
  induction Q generalizing T T' M hTWF hST with
  | nil =>
    have nestedNil : ∀ (sp : Nat) (U M : SessionType), U.spine ≤ sp →
        U.WellFormed → st_trans U (st_label.out p lab S) T' →
        monitor_fold (U, []) M → (∃ M', monitor_fold (T', []) M') →
        ∃ M', monitor_fold (T', []) M' ∧ mon_tr_yes M (ext_tag.send p lab S) M' := by
      intro sp
      induction sp using Nat.strong_induction_on with
      | _ sp ihSp =>
        intro U M hspine hWFU hSTU hEncU hAccU
        cases U with
        | tEnd => cases hSTU
        | tVar X => cases hSTU
        | tRec X B =>
          cases hSTU with
          | tRec hsub =>
            have hCo : (SessionType.tRec X B).Contractive := hWFU.2.2
            have hG : SessionType.Guarded X B := by
              cases hCo with
              | tRec _ hG => exact hG
            have hspineSub : (substSessionType B X
                (SessionType.tRec X B)).spine < sp := by
              have h1 : (substSessionType B X
                  (SessionType.tRec X B)).spine ≤ B.spine :=
                spine_subst_le B X _ (guarded_not_mem_headVars B X hG)
              have h2 : B.spine < (SessionType.tRec X B).spine := by
                simp [SessionType.spine]
              omega
            have hWFSub : (substSessionType B X
                (SessionType.tRec X B)).WellFormed :=
              SessionType.wellFormedUnfold hWFU
                (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
            simp only [monitor_fold, monitor_fold_aux] at hEncU
            subst hEncU
            obtain ⟨M', hAcc', hYesSub⟩ := ihSp _ hspineSub _ _
              (Nat.le_refl _) hWFSub hsub rfl hAccU
            exact ⟨M', hAcc', mon_tr_yes_unfold_lift
              (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _)) hYesSub⟩
        | internalChoice branches =>
          cases hSTU with
          | intC hmem =>
            simp only [monitor_fold, monitor_fold_aux] at hEncU
            subst hEncU
            obtain ⟨Macc, hAccWit⟩ := hAccU
            have htriple : List.Nodup (List.map
                (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) branches) := by
              cases hWFU.1 with
              | internalChoice hnp _ _ => exact nodup_triple_of_nodup_pair hnp
            have hb : mon_tr_yes_base (SessionType.internalChoice branches)
                (ext_tag.send p lab S) T' := mon_tr_yes_base.intC htriple hmem
            have hMEq : Macc = T' := by simpa only [monitor_fold, monitor_fold_aux] using hAccWit
            refine ⟨Macc, hAccWit, ?_⟩
            rw [hMEq]
            exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩
        | externalChoice q branches =>
          cases hSTU
    exact nestedNil T.spine T M (Nat.le_refl _) hTWF hST hEnc hAcc
  | cons msg rest ihOut =>
    have nestedCons : ∀ (sp : Nat) (U : SessionType), U.spine ≤ sp →
        U.WellFormed → st_trans U (st_label.out p lab S) T' →
        monitor_fold (U, msg :: rest) M → (∃ M', monitor_fold (T', msg :: rest) M') →
        ∃ M', monitor_fold (T', msg :: rest) M' ∧
          mon_tr_yes M (ext_tag.send p lab S) M' := by
      intro sp
      induction sp using Nat.strong_induction_on with
      | _ sp ihSp =>
        intro U hspine hWFU hSTU hEncU hAccU
        cases U with
        | tEnd => cases hSTU
        | tVar X => cases hSTU
        | tRec X B =>
          cases hSTU with
          | tRec hsub =>
            have hCo : (SessionType.tRec X B).Contractive := hWFU.2.2
            have hG : SessionType.Guarded X B := by
              cases hCo with
              | tRec _ hG => exact hG
            have hspineSub : (substSessionType B X
                (SessionType.tRec X B)).spine < sp := by
              have h1 : (substSessionType B X
                  (SessionType.tRec X B)).spine ≤ B.spine :=
                spine_subst_le B X _ (guarded_not_mem_headVars B X hG)
              have h2 : B.spine < (SessionType.tRec X B).spine := by
                simp [SessionType.spine]
              omega
            have hWFSub : (substSessionType B X
                (SessionType.tRec X B)).WellFormed :=
              SessionType.wellFormedUnfold hWFU
                (UnfoldStar.step Unfold1.tRec (UnfoldStar.refl _))
            have hEncSub : monitor_fold (substSessionType B X
                (SessionType.tRec X B), msg :: rest) M :=
              monitor_fold_aux_cons_unfold_lift rfl hEncU
            exact ihSp _ hspineSub _ (Nat.le_refl _) hWFSub hsub hEncSub hAccU
        | internalChoice branches =>
          have hT'WF : T'.WellFormed :=
            SessionType.wellFormedPreserved _ _ _ hWFU hSTU
          cases hSTU with
          | intC hmem =>
            simp only [monitor_fold, monitor_fold_aux] at hEncU
            obtain ⟨Tmid, hRecv, hRest⟩ := hEncU
            obtain ⟨Macc, hAccWit⟩ := hAccU
            simp only [monitor_fold, monitor_fold_aux] at hAccWit
            obtain ⟨TmidAcc, hRecvAcc, hRestAcc⟩ := hAccWit
            obtain ⟨X', hSTmid, hRecv'⟩ :=
              intPfx_diamond (st_trans.intC hmem) hRecv ⟨_, hRecvAcc.1⟩
            have hTmidWF : Tmid.WellFormed :=
              mon_tr_yes_preserves_wf hRecv hWFU
            have hXeq : X' = TmidAcc :=
              mon_tr_yes_target_unique hT'WF hRecv' hRecvAcc
            rw [hXeq] at hSTmid hRecv'
            obtain ⟨M', hEnc', hSend⟩ :=
              ihOut hTmidWF hSTmid hRest ⟨_, hRestAcc⟩
            exact ⟨M', ⟨TmidAcc, hRecvAcc, hEnc'⟩, hSend⟩
        | externalChoice q branches =>
          cases hSTU
    exact nestedCons T.spine T (Nat.le_refl _) hTWF hST hEnc hAcc
end UncondAssembly

section PrunableImpliesMonitorable

/-- Closing substitution: fold single substitutions left-to-right. -/
def closeSubst (T : SessionType) (σ : List (String × SessionType)) : SessionType :=
  σ.foldl (fun acc p => substSessionType acc p.1 p.2) T

theorem closeSubst_nil (T : SessionType) : closeSubst T [] = T := by
  simp [closeSubst]

/-- Occurrence-closure collection (finite, prune-closed). -/
noncomputable def collect : SessionType → List (String × SessionType) → Finset SessionType
  | .tEnd, σ => {closeSubst .tEnd σ}
  | .tVar X, σ => {closeSubst (.tVar X) σ}
  | .internalChoice branches, σ =>
      {closeSubst (.internalChoice branches) σ} ∪ collectInt branches σ
  | .externalChoice p branches, σ =>
      {closeSubst (.externalChoice p branches) σ} ∪ collectExt branches σ
  | .tRec X B, σ =>
      let R := closeSubst (.tRec X B) σ
      let σ' := (σ.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]
      {R} ∪ collect B σ'
where
  collectInt : List (Role × Lab × DataSort × SessionType) →
      List (String × SessionType) → Finset SessionType
    | [], _ => ∅
    | x :: xs, σ => collect x.2.2.2 σ ∪ collectInt xs σ
  collectExt : List (Lab × DataSort × SessionType) →
      List (String × SessionType) → Finset SessionType
    | [], _ => ∅
    | x :: xs, σ => collect x.2.2 σ ∪ collectExt xs σ

theorem mem_close_collect (T0 : SessionType) (σ : List (String × SessionType)) :
    closeSubst T0 σ ∈ collect T0 σ := by
  cases T0 with
  | tEnd => simp [collect]
  | tVar X => simp [collect]
  | internalChoice branches => simp [collect]
  | externalChoice p branches => simp [collect]
  | tRec X B => simp [collect]

theorem collect_subset_parent_intC {branches : List (Role × Lab × DataSort × SessionType)}
    {σ : List (String × SessionType)} {x : Role × Lab × DataSort × SessionType}
    (hmem : x ∈ branches) :
    collect x.2.2.2 σ ⊆ collect (.internalChoice branches) σ := by
  have hInt : collect x.2.2.2 σ ⊆ collect.collectInt branches σ := by
    induction branches with
    | nil => simp at hmem
    | cons hd tl ih =>
      simp only [collect.collectInt]
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih hmem) Finset.subset_union_right
  simp only [collect]
  exact Finset.Subset.trans hInt Finset.subset_union_right

theorem collect_subset_parent_extC {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {σ : List (String × SessionType)} {x : Lab × DataSort × SessionType}
    (hmem : x ∈ branches) :
    collect x.2.2 σ ⊆ collect (.externalChoice p branches) σ := by
  have hExt : collect x.2.2 σ ⊆ collect.collectExt branches σ := by
    induction branches with
    | nil => simp at hmem
    | cons hd tl ih =>
      simp only [collect.collectExt]
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih hmem) Finset.subset_union_right
  simp only [collect]
  exact Finset.Subset.trans hExt Finset.subset_union_right

theorem collect_subset_parent_trec {X : String} {B : SessionType}
    {σ : List (String × SessionType)} :
    let R := closeSubst (.tRec X B) σ
    let σ' := (σ.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]
    collect B σ' ⊆ collect (.tRec X B) σ := by
  simp only [collect]
  exact Finset.subset_union_right

inductive ReachCollect :
    SessionType → List (String × SessionType) →
    SessionType → List (String × SessionType) → Prop where
  | refl (T : SessionType) (σ : List (String × SessionType)) : ReachCollect T σ T σ
  | stepInt {T : SessionType} {σ : List (String × SessionType)}
      {branches : List (Role × Lab × DataSort × SessionType)}
      {x : Role × Lab × DataSort × SessionType}
      (hEq : T = .internalChoice branches) (hmem : x ∈ branches) :
      ReachCollect T σ x.2.2.2 σ
  | stepExt {T : SessionType} {σ : List (String × SessionType)}
      {p : Role} {branches : List (Lab × DataSort × SessionType)}
      {x : Lab × DataSort × SessionType}
      (hEq : T = .externalChoice p branches) (hmem : x ∈ branches) :
      ReachCollect T σ x.2.2 σ
  | stepRec {X : String} {B : SessionType} {σ : List (String × SessionType)}
      (R : SessionType) (hR : R = closeSubst (.tRec X B) σ)
      (σ' : List (String × SessionType))
      (hσ' : σ' = (σ.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]) :
      ReachCollect (.tRec X B) σ B σ'
  | trans {T1 T2 T3 : SessionType} {σ1 σ2 σ3 : List (String × SessionType)} :
      ReachCollect T1 σ1 T2 σ2 → ReachCollect T2 σ2 T3 σ3 →
      ReachCollect T1 σ1 T3 σ3

theorem reachCollect_subset {T1 T2 : SessionType} {σ1 σ2 : List (String × SessionType)}
    (h : ReachCollect T1 σ1 T2 σ2) :
    collect T2 σ2 ⊆ collect T1 σ1 := by
  induction h with
  | refl T σ => exact Finset.Subset.refl _
  | stepInt hEq hmem =>
    subst hEq
    exact collect_subset_parent_intC hmem
  | stepExt hEq hmem =>
    subst hEq
    exact collect_subset_parent_extC hmem
  | stepRec R hR σ' hσ' =>
    subst hR; subst hσ'
    exact collect_subset_parent_trec
  | trans _ _ ih1 ih2 => exact Finset.Subset.trans ih2 ih1

theorem pruneStep_not_from_tEnd {U : SessionType} :
    ¬ Drainability.PruneStep SessionType.tEnd U := by
  intro h; cases h

theorem pruneStep_not_from_tVar (X : String) {U : SessionType} :
    ¬ Drainability.PruneStep (SessionType.tVar X) U := by
  intro h; cases h

theorem pruneStep_intC_inv {branches : List (Role × Lab × DataSort × SessionType)}
    {V : SessionType} (h : Drainability.PruneStep (SessionType.internalChoice branches) V) :
    ∃ x ∈ branches, V = x.2.2.2 := by
  cases h with
  | intC hmem => exact ⟨_, hmem, rfl⟩

theorem pruneStep_extC_inv {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {V : SessionType} (h : Drainability.PruneStep (SessionType.externalChoice p branches) V) :
    ∃ x ∈ branches, V = x.2.2 := by
  cases h with
  | extC hmem => exact ⟨_, hmem, rfl⟩

theorem pruneStep_trec_inv {X : String} {B V : SessionType}
    (h : Drainability.PruneStep (SessionType.tRec X B) V) :
    V = substSessionType B X (SessionType.tRec X B) := by
  cases h with
  | trec => rfl

theorem closeSubst_intC_eq_map (branches : List (Role × Lab × DataSort × SessionType))
    (σ : List (String × SessionType)) :
    ∃ branches', closeSubst (.internalChoice branches) σ = .internalChoice branches' ∧
      branches' = branches.map (fun x => (x.1, x.2.1, x.2.2.1, closeSubst x.2.2.2 σ)) := by
  induction σ generalizing branches with
  | nil =>
    exact ⟨branches, by simp [closeSubst], by simp [closeSubst]⟩
  | cons hd tl ih =>
    obtain ⟨Y, RY⟩ := hd
    have hdist : ∀ l : List (Role × Lab × DataSort × SessionType),
        substSessionType (.internalChoice l) Y RY =
          .internalChoice (l.map fun x => (x.1, x.2.1, x.2.2.1, substSessionType x.2.2.2 Y RY)) := by
      intro l
      simp [substSessionType, go_int_eq_map]
    have hfold : ∀ (T : SessionType),
        closeSubst T ((Y, RY) :: tl) = closeSubst (substSessionType T Y RY) tl := by
      intro T
      simp [closeSubst, List.foldl_cons]
    rw [hfold, hdist]
    obtain ⟨branches', hEq, hmap2⟩ := ih _
    exact ⟨branches', hEq, by simp [hmap2, List.map_map, Function.comp_apply, ← hfold]⟩

/-- `closeSubst` distributes over `externalChoice` branch targets. -/
theorem closeSubst_extC_eq_map (p : Role) (branches : List (Lab × DataSort × SessionType))
    (σ : List (String × SessionType)) :
    ∃ branches', closeSubst (.externalChoice p branches) σ = .externalChoice p branches' ∧
      branches' = branches.map (fun x => (x.1, x.2.1, closeSubst x.2.2 σ)) := by
  induction σ generalizing p branches with
  | nil =>
    exact ⟨branches, by simp [closeSubst], by simp [closeSubst]⟩
  | cons hd tl ih =>
    obtain ⟨Y, RY⟩ := hd
    have hdist : ∀ (q : Role) (l : List (Lab × DataSort × SessionType)),
        substSessionType (.externalChoice q l) Y RY =
          .externalChoice q (l.map fun x => (x.1, x.2.1, substSessionType x.2.2 Y RY)) := by
      intro q l
      simp [substSessionType, go_ext_eq_map]
    have hfold : ∀ (T : SessionType),
        closeSubst T ((Y, RY) :: tl) = closeSubst (substSessionType T Y RY) tl := by
      intro T
      simp [closeSubst, List.foldl_cons]
    rw [hfold, hdist]
    obtain ⟨branches', hEq, hmap2⟩ := ih _ _
    exact ⟨branches', hEq, by simp [hmap2, List.map_map, Function.comp_apply, ← hfold]⟩

/-- Any mapping in a reachable environment was introduced by an ancestor `tRec`
    on the path (most recent binder wins via filtering), or was already present
    in the starting environment. General start env (variable) so induction works. -/
theorem find_intro_general {Top T0 : SessionType}
    {σ_start σ_path : List (String × SessionType)}
    (hReach : ReachCollect Top σ_start T0 σ_path) {X : String} {R : SessionType}
    (hMem : (X, R) ∈ σ_path) :
    (∃ Tanc σanc Banc, ReachCollect Top σ_start Tanc σanc ∧ Tanc = .tRec X Banc ∧
      R = closeSubst Tanc σanc ∧
      ReachCollect Tanc σanc Banc
        ((σanc.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)])) ∨
      (X, R) ∈ σ_start := by
  induction hReach with
  | refl T σ => exact Or.inr hMem
  | stepInt hEq hmem =>
    subst hEq
    exact Or.inr hMem
  | stepExt hEq hmem =>
    subst hEq
    exact Or.inr hMem
  | stepRec R' hR σ' hσ' =>
    subst hR; subst hσ'
    rw [List.mem_append] at hMem
    rcases hMem with hmemFilt | hmemSingle
    · have hmemOrig : (X, R) ∈ _ :=
        (List.mem_filter.mp hmemFilt).1
      exact Or.inr hmemOrig
    · simp at hmemSingle
      obtain ⟨rfl, rfl⟩ := hmemSingle
      refine Or.inl ⟨_, _, _, ReachCollect.refl _ _,
        rfl, rfl, ReachCollect.stepRec _ rfl _ rfl⟩
  | trans h1 h2 ih1 ih2 =>
    rcases ih2 hMem with ⟨Tanc, σanc, Banc, hPref2, hTanc, hR, hIntro⟩ | hMid
    · exact Or.inl ⟨Tanc, σanc, Banc,
        ReachCollect.trans h1 hPref2, hTanc, hR, hIntro⟩
    · rcases ih1 hMid with ⟨Tanc, σanc, Banc, hPref1, hTanc, hR, hIntro⟩ | hStart
      · exact Or.inl ⟨Tanc, σanc, Banc, hPref1, hTanc, hR, hIntro⟩
      · exact Or.inr hStart

/-- Specialized to empty start env: the "already in start env" alternative is
    impossible, so every mapping was introduced on the path. -/
theorem find_intro_nil {Top T0 : SessionType} {σ_path : List (String × SessionType)}
    (hReach : ReachCollect Top [] T0 σ_path) {X : String} {R : SessionType}
    (hMem : (X, R) ∈ σ_path) :
    ∃ Tanc σanc Banc, ReachCollect Top [] Tanc σanc ∧ Tanc = .tRec X Banc ∧
      R = closeSubst Tanc σanc ∧
      ReachCollect Tanc σanc Banc
        ((σanc.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]) := by
  rcases find_intro_general hReach hMem with ⟨Tanc, σanc, Banc, hPref, hTanc, hR, hIntro⟩ | hStart
  · exact ⟨Tanc, σanc, Banc, hPref, hTanc, hR, hIntro⟩
  · simp at hStart

/-- Fold/unfold for `closeSubst` (single head entry). -/
theorem closeSubst_cons (T : SessionType) (Y : String) (RY : SessionType)
    (tl : List (String × SessionType)) :
    closeSubst T ((Y, RY) :: tl) = closeSubst (substSessionType T Y RY) tl := by
  simp [closeSubst, List.foldl_cons]

/-- `closeSubst` preserves `tEnd`. -/
theorem closeSubst_tEnd (σ : List (String × SessionType)) :
    closeSubst .tEnd σ = .tEnd := by
  induction σ with
  | nil => simp [closeSubst]
  | cons hd tl ih =>
    obtain ⟨Y, RY⟩ := hd
    rw [closeSubst_cons]
    simp only [substSessionType]
    exact ih

/-- `closeSubst` preserves `tRec` head (shadowing entries leave it unchanged,
    others push inside; only non-shadowed entries affect the body). -/
theorem closeSubst_trec_shape (X : String) (B : SessionType)
    (σ : List (String × SessionType)) :
    closeSubst (.tRec X B) σ =
      .tRec X (closeSubst B (σ.filter (fun p => decide (p.1 ≠ X)))) := by
  induction σ generalizing B with
  | nil => simp [closeSubst]
  | cons hd tl ih =>
    obtain ⟨Y, RY⟩ := hd
    by_cases hYX : Y = X
    · subst hYX
      rw [closeSubst_cons]
      simp only [substSessionType, ↓reduceIte]
      rw [ih]
      have hfil : ((Y, RY) :: tl).filter (fun p => decide (p.1 ≠ Y)) =
          tl.filter (fun p => decide (p.1 ≠ Y)) := by
        apply List.filter_cons_of_neg
        simp
      rw [hfil]
    · rw [closeSubst_cons]
      simp only [substSessionType, hYX, ↓reduceIte]
      rw [ih]
      have hfil : ((Y, RY) :: tl).filter (fun p => decide (p.1 ≠ X)) =
          (Y, RY) :: tl.filter (fun p => decide (p.1 ≠ X)) := by
        apply List.filter_cons_of_pos
        simp [hYX]
      rw [hfil, ← closeSubst_cons]

/-- Unmapped `tVar` is unchanged by `closeSubst`. -/
theorem closeSubst_tVar_nmem (X : String) (σ : List (String × SessionType))
    (hnotin : X ∉ σ.map Prod.fst) :
    closeSubst (.tVar X) σ = .tVar X := by
  induction σ with
  | nil => simp [closeSubst]
  | cons hd tl ih =>
    obtain ⟨Y, RY⟩ := hd
    have hYX : Y ≠ X := by
      intro h
      apply hnotin
      simp [h]
    have hnotin_tl : X ∉ tl.map Prod.fst := by
      intro h
      apply hnotin
      simp [h]
    rw [closeSubst_cons]
    simp only [substSessionType, hYX, ↓reduceIte]
    exact ih hnotin_tl

/-- Reachability preserves key-nodup (filtering + fresh append). -/
theorem reach_nodup_keys {T T0 : SessionType} {σ σ_path : List (String × SessionType)}
    (hReach : ReachCollect T σ T0 σ_path)
    (hND : (σ.map Prod.fst).Nodup) :
    (σ_path.map Prod.fst).Nodup := by
  induction hReach with
  | refl T σ => exact hND
  | stepInt hEq hmem =>
    subst hEq
    exact hND
  | stepExt hEq hmem =>
    subst hEq
    exact hND
  | stepRec R hR σ' hσ' =>
    rename_i Xanc Banc σpar
    subst hR; subst hσ'
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · have hsub : List.Sublist
          ((σpar.filter (fun p => decide (p.1 ≠ Xanc))).map Prod.fst)
          (σpar.map Prod.fst) :=
        List.Sublist.map Prod.fst List.filter_sublist
      exact hsub.nodup hND
    · intro a ha b hb
      have hbEq : b = Xanc := by simpa using hb
      rw [hbEq]
      obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp ha
      have hcond : decide (p.1 ≠ Xanc) = true :=
        (List.mem_filter.mp hp_mem).2
      simp at hcond hp_eq
      rw [hp_eq] at hcond
      exact hcond
  | trans h1 h2 ih1 ih2 => exact ih2 (ih1 hND)

/-- `closeSubst` over appended environments splits. -/
theorem closeSubst_append (T : SessionType) (l₁ l₂ : List (String × SessionType)) :
    closeSubst T (l₁ ++ l₂) = closeSubst (closeSubst T l₁) l₂ := by
  simp [closeSubst, List.foldl_append]

/-- `closeSubst` on a closed term is the identity (via `subst_noop`). -/
theorem closeSubst_closed_id {R : SessionType} (hR : R.IsClosed)
    (σ : List (String × SessionType)) : closeSubst R σ = R := by
  induction σ with
  | nil => simp [closeSubst]
  | cons hd tl ih =>
    obtain ⟨Y, RY⟩ := hd
    rw [closeSubst_cons, subst_noop R Y RY (by rw [hR]; simp), ih]

/-- Mapped `tVar` resolves to its (closed) entry under key-nodup. -/
theorem closeSubst_tVar_mem_eq {X : String} {R : SessionType}
    {σ : List (String × SessionType)}
    (hND : (σ.map Prod.fst).Nodup) (hMem : (X, R) ∈ σ) (hCR : R.IsClosed) :
    closeSubst (.tVar X) σ = R := by
  induction σ with
  | nil => simp at hMem
  | cons hd tl ih =>
    obtain ⟨Y, RY⟩ := hd
    have hNDcons := (List.nodup_cons.mp hND)
    have hNDtl : (tl.map Prod.fst).Nodup := hNDcons.2
    have hYnotin : Y ∉ tl.map Prod.fst := hNDcons.1
    rw [List.mem_cons] at hMem
    rcases hMem with heq | hMemTl
    · obtain ⟨rfl, rfl⟩ : (X, R) = (Y, RY) := by simpa using heq
      rw [closeSubst_cons]
      simp only [substSessionType, ↓reduceIte]
      exact closeSubst_closed_id hCR tl
    · have hXintail : X ∈ tl.map Prod.fst :=
        List.mem_map.mpr ⟨(X, R), hMemTl, rfl⟩
      have hYX : Y ≠ X := by
        intro hYX
        rw [hYX] at hYnotin
        exact hYnotin hXintail
      have hXY : X ≠ Y := fun h => hYX h.symm
      rw [closeSubst_cons]
      simp only [substSessionType, hYX]
      exact ih hNDtl hMemTl

/-- Branch targets of a closed internal choice are closed. -/
theorem closed_intC_of_mem {branches' : List (Role × Lab × DataSort × SessionType)}
    (hC : (SessionType.internalChoice branches').IsClosed)
    {x' : Role × Lab × DataSort × SessionType} (hmem : x' ∈ branches') :
    (x'.2.2.2).IsClosed := by
  have hfv : SessionType.fv.goInt branches' = [] := by
    have h := hC
    simpa [SessionType.IsClosed, SessionType.fv] using h
  clear hC
  induction branches' with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨p, lab, S, Tt⟩ := hd
    simp only [SessionType.fv.goInt] at hfv
    have hboth := List.append_eq_nil_iff.mp hfv
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmemTl
    · exact hboth.1
    · exact ih hmemTl hboth.2

/-- Branch targets of a closed external choice are closed. -/
theorem closed_extC_of_mem {p : Role} {branches' : List (Lab × DataSort × SessionType)}
    (hC : (SessionType.externalChoice p branches').IsClosed)
    {x' : Lab × DataSort × SessionType} (hmem : x' ∈ branches') :
    (x'.2.2).IsClosed := by
  have hfv : SessionType.fv.goExt branches' = [] := by
    have h := hC
    simpa [SessionType.IsClosed, SessionType.fv] using h
  clear hC
  induction branches' with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨lab, S, Tt⟩ := hd
    simp only [SessionType.fv.goExt] at hfv
    have hboth := List.append_eq_nil_iff.mp hfv
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmemTl
    · exact hboth.1
    · exact ih hmemTl hboth.2

/-- Closedness of `closeSubst` is preserved along `ReachCollect` paths. -/
theorem closed_preserve {T : SessionType} {σ : List (String × SessionType)}
    {T0 : SessionType} {σ_path : List (String × SessionType)}
    (hReach : ReachCollect T σ T0 σ_path)
    (hC : (closeSubst T σ).IsClosed) : (closeSubst T0 σ_path).IsClosed := by
  induction hReach with
  | refl T σ => exact hC
  | stepInt hEq hmem =>
    rename_i Tpar σpar branchespar xpar
    subst hEq
    obtain ⟨branches', hEqC, hmap⟩ := closeSubst_intC_eq_map _ _
    have hC' : (SessionType.internalChoice branches').IsClosed := by
      rw [← hEqC]; exact hC
    have hmem' : (xpar.1, xpar.2.1, xpar.2.2.1, closeSubst xpar.2.2.2 σpar) ∈ branches' := by
      rw [hmap]
      exact List.mem_map.mpr ⟨xpar, hmem, rfl⟩
    have hclosed := closed_intC_of_mem hC' hmem'
    simpa using hclosed
  | stepExt hEq hmem =>
    rename_i Tpar σpar ppar branchespar xpar
    subst hEq
    obtain ⟨branches', hEqC, hmap⟩ := closeSubst_extC_eq_map ppar branchespar σpar
    have hC' : (SessionType.externalChoice ppar branches').IsClosed := by
      rw [← hEqC]; exact hC
    have hmem' : (xpar.1, xpar.2.1, closeSubst xpar.2.2 σpar) ∈ branches' := by
      rw [hmap]
      exact List.mem_map.mpr ⟨xpar, hmem, rfl⟩
    have hclosed := closed_extC_of_mem hC' hmem'
    simpa using hclosed
  | stepRec R hR σ' hσ' =>
    rename_i Xanc Banc σpar
    subst hR; subst hσ'
    have hRclosed : (closeSubst (SessionType.tRec Xanc Banc) σpar).IsClosed := hC
    have hshape := closeSubst_trec_shape Xanc Banc σpar
    have hCtrec : (SessionType.tRec Xanc (closeSubst Banc
      (σpar.filter (fun p => decide (p.1 ≠ Xanc))))).IsClosed := by
      rw [← hshape]; exact hC
    have hfvbody : ((closeSubst Banc
      (σpar.filter (fun p => decide (p.1 ≠ Xanc)))).fv.filter
      (fun x => x != Xanc)) = [] := by
      have h := hCtrec
      simpa [SessionType.IsClosed, SessionType.fv] using h
    rw [closeSubst_append]
    have hsing : ∀ (B' : SessionType) (X : String) (Rc : SessionType),
        closeSubst B' [(X, Rc)] = substSessionType B' X Rc := by
      intro B' X Rc
      simp [closeSubst]
    rw [hsing]
    have hfv : ((substSessionType (closeSubst Banc
      (σpar.filter (fun p => decide (p.1 ≠ Xanc)))) Xanc
      (closeSubst (SessionType.tRec Xanc Banc) σpar)).fv) =
      (((closeSubst Banc
      (σpar.filter (fun p => decide (p.1 ≠ Xanc)))).fv.filter
      (fun x => x != Xanc))) :=
      fv_subst_aux _ Xanc _ hRclosed
    have hgoal : ((substSessionType (closeSubst Banc
      (σpar.filter (fun p => decide (p.1 ≠ Xanc)))) Xanc
      (closeSubst (SessionType.tRec Xanc Banc) σpar)).fv) = [] := by
      rw [hfv]; exact hfvbody
    exact hgoal
  | trans h1 h2 ih1 ih2 => exact ih2 (ih1 hC)

/-- Every entry of a `Top`-reachable environment is a closed ancestor unfolding. -/
theorem entries_closed {Top : SessionType} (hTop : Top.IsClosed)
    {T0 : SessionType} {σ_path : List (String × SessionType)}
    (hReach : ReachCollect Top [] T0 σ_path)
    {Y : String} {S : SessionType} (hMem : (Y, S) ∈ σ_path) : S.IsClosed := by
  obtain ⟨Tanc, σanc, Banc, hPref, hTanc, hR, hIntro⟩ :=
    find_intro_nil hReach hMem
  have hTopClosed : (closeSubst Top []).IsClosed := by
    rw [closeSubst_nil]; exact hTop
  have hCanc : (closeSubst Tanc σanc).IsClosed :=
    closed_preserve hPref hTopClosed
  rw [hR]; exact hCanc

/-- Unfolding a `tRec` close element gives the body close element
    (append-split plus singleton fold). -/
theorem closeSubst_trec_unfold_eq {X : String} {B : SessionType}
    {σ : List (String × SessionType)} :
    closeSubst B
      ((σ.filter (fun p => decide (p.1 ≠ X))) ++
        [(X, closeSubst (SessionType.tRec X B) σ)]) =
      substSessionType
        (closeSubst B (σ.filter (fun p => decide (p.1 ≠ X))))
        X (closeSubst (SessionType.tRec X B) σ) := by
  rw [closeSubst_append]
  simp [closeSubst]

/-- Successors of a `Top`-reachable close element stay in `collect Top []`.
    Direct head-case analysis (no induction): each successor is exhibited as
    the close element of an explicitly reachable node. -/
theorem close_mem_closed {Top : SessionType} (hTop : Top.IsClosed)
    {T0 : SessionType} {σ_path : List (String × SessionType)}
    (hReach : ReachCollect Top [] T0 σ_path)
    {V : SessionType} (hStep : Drainability.PruneStep (closeSubst T0 σ_path) V) :
    V ∈ collect Top [] := by
  have hTopClosed : (closeSubst Top []).IsClosed := by
    rw [closeSubst_nil]; exact hTop
  have hND : (σ_path.map Prod.fst).Nodup := reach_nodup_keys hReach (by simp)
  cases T0 with
  | tEnd =>
    have hU : closeSubst SessionType.tEnd σ_path = SessionType.tEnd :=
      closeSubst_tEnd σ_path
    rw [hU] at hStep
    exact absurd hStep pruneStep_not_from_tEnd
  | tVar X =>
    by_cases hEx : ∃ R, (X, R) ∈ σ_path
    · obtain ⟨R, hMem⟩ := hEx
      have hRclosed : R.IsClosed := entries_closed hTop hReach hMem
      have hU : closeSubst (SessionType.tVar X) σ_path = R :=
        closeSubst_tVar_mem_eq hND hMem hRclosed
      rw [hU] at hStep
      obtain ⟨Tanc, σanc, Banc, hPref, hTanc, hRanc, hIntro⟩ :=
        find_intro_nil hReach hMem
      have hRshape := closeSubst_trec_shape X Banc σanc
      rw [hRanc, hTanc, hRshape] at hStep
      have hVeq := pruneStep_trec_inv hStep
      have hReq : R = closeSubst (SessionType.tRec X Banc) σanc := by
        rw [hRanc, hTanc]
      have hunfold := closeSubst_trec_unfold_eq (X := X) (B := Banc) (σ := σanc)
      have hReachBody : ReachCollect Top [] Banc
          ((σanc.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]) :=
        ReachCollect.trans hPref hIntro
      have hmemBody : closeSubst Banc
          ((σanc.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]) ∈
          collect Banc
          ((σanc.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]) :=
        mem_close_collect _ _
      have hsub := reachCollect_subset hReachBody
      have hVin : V ∈ collect Banc
          ((σanc.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]) := by
        have hVV : V = closeSubst Banc
            ((σanc.filter (fun p => decide (p.1 ≠ X))) ++ [(X, R)]) := by
          rw [hReq, hunfold, hRshape]
          exact hVeq
        rw [hVV]; exact hmemBody
      exact hsub hVin
    · have hnotin : X ∉ σ_path.map Prod.fst := by
        intro hcon
        obtain ⟨p, hpmem, hpeq⟩ := List.mem_map.mp hcon
        obtain ⟨Y, RY⟩ := p
        simp at hpeq
        subst hpeq
        exact hEx ⟨RY, hpmem⟩
      have hU : closeSubst (SessionType.tVar X) σ_path = SessionType.tVar X :=
        closeSubst_tVar_nmem X σ_path hnotin
      rw [hU] at hStep
      exact absurd hStep (pruneStep_not_from_tVar X)
  | internalChoice branches =>
    obtain ⟨branches', hEqC, hmap⟩ := closeSubst_intC_eq_map branches σ_path
    rw [hEqC] at hStep
    obtain ⟨x', hmem', rfl⟩ := pruneStep_intC_inv hStep
    rw [hmap] at hmem'
    obtain ⟨x, hmemx, hxeq⟩ := List.mem_map.mp hmem'
    have hVx : x'.2.2.2 = closeSubst x.2.2.2 σ_path := by rw [← hxeq]
    rw [hVx]
    have hstep : ReachCollect (SessionType.internalChoice branches) σ_path
        x.2.2.2 σ_path :=
      ReachCollect.stepInt rfl hmemx
    have hReachT : ReachCollect Top [] x.2.2.2 σ_path :=
      ReachCollect.trans hReach hstep
    exact reachCollect_subset hReachT (mem_close_collect _ _)
  | externalChoice p branches =>
    obtain ⟨branches', hEqC, hmap⟩ := closeSubst_extC_eq_map p branches σ_path
    rw [hEqC] at hStep
    obtain ⟨x', hmem', rfl⟩ := pruneStep_extC_inv hStep
    rw [hmap] at hmem'
    obtain ⟨x, hmemx, hxeq⟩ := List.mem_map.mp hmem'
    have hVx : x'.2.2 = closeSubst x.2.2 σ_path := by rw [← hxeq]
    rw [hVx]
    have hstep : ReachCollect (SessionType.externalChoice p branches) σ_path
        x.2.2 σ_path :=
      ReachCollect.stepExt rfl hmemx
    have hReachT : ReachCollect Top [] x.2.2 σ_path :=
      ReachCollect.trans hReach hstep
    exact reachCollect_subset hReachT (mem_close_collect _ _)
  | tRec X B =>
    have hshape := closeSubst_trec_shape X B σ_path
    rw [hshape] at hStep
    have hVeq := pruneStep_trec_inv hStep
    have hU0 : closeSubst (SessionType.tRec X B) σ_path =
        SessionType.tRec X (closeSubst B
          (σ_path.filter (fun p => decide (p.1 ≠ X)))) := hshape
    have hbody := closeSubst_trec_unfold_eq (X := X) (B := B) (σ := σ_path)
    have hstep : ReachCollect (SessionType.tRec X B) σ_path B
        ((σ_path.filter (fun p => decide (p.1 ≠ X))) ++
          [(X, closeSubst (SessionType.tRec X B) σ_path)]) :=
      ReachCollect.stepRec _ rfl _ rfl
    have hReachB : ReachCollect Top [] B
        ((σ_path.filter (fun p => decide (p.1 ≠ X))) ++
          [(X, closeSubst (SessionType.tRec X B) σ_path)]) :=
      ReachCollect.trans hReach hstep
    have hVin : V ∈ collect B
        ((σ_path.filter (fun p => decide (p.1 ≠ X))) ++
          [(X, closeSubst (SessionType.tRec X B) σ_path)]) := by
      have hVV : V = closeSubst B
          ((σ_path.filter (fun p => decide (p.1 ≠ X))) ++
            [(X, closeSubst (SessionType.tRec X B) σ_path)]) := by
        rw [hbody, hU0]
        exact hVeq
      rw [hVV]; exact mem_close_collect _ _
    exact reachCollect_subset hReachB hVin

/-- Elements of an internal-branch collection come from some branch target. -/
theorem mem_collectInt_imp {branches : List (Role × Lab × DataSort × SessionType)}
    {σ : List (String × SessionType)} {U : SessionType}
    (h : U ∈ collect.collectInt branches σ) :
    ∃ x ∈ branches, U ∈ collect x.2.2.2 σ := by
  induction branches with
  | nil => simp [collect.collectInt] at h
  | cons hd tl ih =>
    simp only [collect.collectInt, Finset.mem_union] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨x, hmem, hx⟩ := ih h
      exact ⟨x, List.mem_cons.mpr (Or.inr hmem), hx⟩

/-- Elements of an external-branch collection come from some branch target. -/
theorem mem_collectExt_imp {branches : List (Lab × DataSort × SessionType)}
    {σ : List (String × SessionType)} {U : SessionType}
    (h : U ∈ collect.collectExt branches σ) :
    ∃ x ∈ branches, U ∈ collect x.2.2 σ := by
  induction branches with
  | nil => simp [collect.collectExt] at h
  | cons hd tl ih =>
    simp only [collect.collectExt, Finset.mem_union] at h
    rcases h with h | h
    · exact ⟨hd, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨x, hmem, hx⟩ := ih h
      exact ⟨x, List.mem_cons.mpr (Or.inr hmem), hx⟩

/-- Internal branch targets are strictly smaller than the choice. -/
theorem sizeOf_branch_int_lt (branches : List (Role × Lab × DataSort × SessionType))
    (x : Role × Lab × DataSort × SessionType) (hmem : x ∈ branches) :
    sizeOf x.2.2.2 < sizeOf (SessionType.internalChoice branches) := by
  induction branches with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨p, lab, S, Tt⟩ := hd
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmemTl
    · simp_wf
      omega
    · have h1 := ih hmemTl
      have h2 : sizeOf (SessionType.internalChoice tl) <
          sizeOf (SessionType.internalChoice ((p, lab, S, Tt) :: tl)) := by
        simp_wf
      omega

/-- External branch targets are strictly smaller than the choice. -/
theorem sizeOf_branch_ext_lt {p : Role} (branches : List (Lab × DataSort × SessionType))
    (x : Lab × DataSort × SessionType) (hmem : x ∈ branches) :
    sizeOf x.2.2 < sizeOf (SessionType.externalChoice p branches) := by
  induction branches with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨lab, S, Tt⟩ := hd
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmemTl
    · simp_wf
      omega
    · have h1 := ih hmemTl
      have h2 : sizeOf (SessionType.externalChoice p tl) <
          sizeOf (SessionType.externalChoice p ((lab, S, Tt) :: tl)) := by
        simp_wf
      omega

/-- All `Top`-collect elements are prune-closed (size induction on the
    occurrence head; close elements via `close_mem_closed`). -/
theorem all_mem_closed_aux {Top : SessionType} (hTop : Top.IsClosed) :
    ∀ (n : Nat) (T0 : SessionType) (σ_path : List (String × SessionType)),
    sizeOf T0 < n → ReachCollect Top [] T0 σ_path →
    ∀ (U : SessionType), U ∈ collect T0 σ_path → ∀ (V : SessionType),
      Drainability.PruneStep U V → V ∈ collect Top [] := by
  intro n
  induction n with
  | zero =>
    intro T0 σ_path hlt hReach U hU V hStep
    exact absurd hlt (Nat.not_lt_zero _)
  | succ n ih =>
    intro T0 σ_path hlt hReach U hU V hStep
    cases T0 with
    | tEnd =>
      simp only [collect, Finset.mem_singleton] at hU
      subst hU
      exact close_mem_closed hTop hReach hStep
    | tVar X =>
      simp only [collect, Finset.mem_singleton] at hU
      subst hU
      exact close_mem_closed hTop hReach hStep
    | internalChoice branches =>
      simp only [collect, Finset.mem_union, Finset.mem_singleton] at hU
      rcases hU with rfl | hUint
      · exact close_mem_closed hTop hReach hStep
      · obtain ⟨x, hmemx, hUx⟩ := mem_collectInt_imp hUint
        have hstrict := sizeOf_branch_int_lt branches x hmemx
        have hltn : sizeOf x.2.2.2 < n := by omega
        have hReachT : ReachCollect Top [] x.2.2.2 σ_path :=
          ReachCollect.trans hReach (ReachCollect.stepInt rfl hmemx)
        exact ih _ _ hltn hReachT _ hUx _ hStep
    | externalChoice p branches =>
      simp only [collect, Finset.mem_union, Finset.mem_singleton] at hU
      rcases hU with rfl | hUext
      · exact close_mem_closed hTop hReach hStep
      · obtain ⟨x, hmemx, hUx⟩ := mem_collectExt_imp hUext
        have hstrict := sizeOf_branch_ext_lt (p := p) branches x hmemx
        have hltn : sizeOf x.2.2 < n := by omega
        have hReachT : ReachCollect Top [] x.2.2 σ_path :=
          ReachCollect.trans hReach (ReachCollect.stepExt rfl hmemx)
        exact ih _ _ hltn hReachT _ hUx _ hStep
    | tRec X B =>
      have hEq : collect (SessionType.tRec X B) σ_path =
          {closeSubst (SessionType.tRec X B) σ_path} ∪
          collect B ((σ_path.filter (fun p => decide (p.1 ≠ X))) ++
            [(X, closeSubst (SessionType.tRec X B) σ_path)]) := rfl
      rw [hEq, Finset.mem_union, Finset.mem_singleton] at hU
      rcases hU with rfl | hUB
      · exact close_mem_closed hTop hReach hStep
      · have hstrict : sizeOf B < sizeOf (SessionType.tRec X B) := by
          simp_wf
        have hltn : sizeOf B < n := by omega
        have hReachB : ReachCollect Top [] B
            ((σ_path.filter (fun p => decide (p.1 ≠ X))) ++
              [(X, closeSubst (SessionType.tRec X B) σ_path)]) :=
          ReachCollect.trans hReach
            (ReachCollect.stepRec _ rfl _ rfl)
        exact ih _ _ hltn hReachB _ hUB _ hStep

/-- Every element of `collect Top []` is prune-closed. -/
theorem collect_closed {Top : SessionType} (hTop : Top.IsClosed)
    {U : SessionType} (hU : U ∈ collect Top [])
    {V : SessionType} (hStep : Drainability.PruneStep U V) :
    V ∈ collect Top [] :=
  all_mem_closed_aux hTop (sizeOf Top + 1) Top [] (Nat.lt_succ_self _)
    (ReachCollect.refl _ _) U hU V hStep

/-- A prune-closed finite set containing `Top` makes `Top` monitorable. -/
theorem monitorable_of_prune_closed_set {Top : SessionType} (hTop : Top.IsClosed) :
    Drainability.Monitorable Top := by
  have hmem : Top ∈ collect Top [] := by
    simpa [closeSubst_nil] using mem_close_collect Top []
  have hclosed : ∀ U ∈ collect Top [], ∀ V : SessionType,
      Drainability.PruneStep U V → V ∈ collect Top [] := by
    intro U hU V hStep
    exact collect_closed hTop hU hStep
  have key : ∀ {U : SessionType},
      Relation.ReflTransGen Drainability.PruneStep Top U → U ∈ collect Top [] := by
    intro U hU
    induction hU with
    | refl => exact hmem
    | tail hRTC hStep ih => exact hclosed _ ih _ hStep
  have hsub : {U : SessionType | Relation.ReflTransGen Drainability.PruneStep Top U} ⊆
      ↑(collect Top []) := by
    intro U hU
    exact Finset.mem_coe.mpr (key hU)
  exact Set.Finite.subset (Finset.finite_toSet (collect Top [])) hsub

/-- Well-formed closed prunable types are monitorable. -/
theorem prunable_implies_monitorable {T : SessionType}
    (hWF : T.WellFormed) (_hPr : Prunable [] T) :
    Drainability.Monitorable T :=
  monitorable_of_prune_closed_set hWF.2.1
