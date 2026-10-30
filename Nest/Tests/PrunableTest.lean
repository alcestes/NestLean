import Nest.SessionUtils
import Nest.Drainability
import Nest.SessionAdequacy
/-!
# PrunableTest: step-premise lifting and `PrunableOneMsg` witnesses.
-/

/-- Step-premise lifting (one-message closers, strengthened form): a choice
    is one-message prunable if all its *actual step* successors are.
    Strictly more applicable than the `Has`-premise form
    (`firstStep_intC` in `Nest.SessionAdequacy`): owner-blocked
    `Has`-true targets contribute no steps and no premise. Needs no
    exposure hypothesis. -/
theorem firstStep_intC_step {branches : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} :
    ∀ {W : SessionType},
    Relation.ReflTransGen (forced_step p lab S) (SessionType.internalChoice branches) W →
    W = SessionType.internalChoice branches ∨
    ∃ V, forced_step p lab S (SessionType.internalChoice branches) V ∧
      Relation.ReflTransGen (forced_step p lab S) V W := by
  intro W h
  induction h with
  | refl => exact Or.inl rfl
  | tail h' hs ih =>
    rcases ih with rfl | ⟨V, hStepV, hRT⟩
    · exact Or.inr ⟨_, hs, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨V, hStepV, hRT.trans (Relation.ReflTransGen.single hs)⟩

/-- Step-premise lifting at `internalChoice`: the choice is one-message prunable if all its
   actual forced-step successors are. -/
theorem prunable_one_msg_intC_of_step
    (branches : List (Role × Lab × DataSort × SessionType))
    (p : Role) (lab : Lab) (S : DataSort)
    (hSucc : ∀ {V : SessionType},
      forced_step p lab S (SessionType.internalChoice branches) V →
      PrunableOneMsg p lab S V) :
    PrunableOneMsg p lab S (SessionType.internalChoice branches) := by
  intro U V hRTC hStep hBack
  have hFirst := firstStep_intC_step hRTC
  rcases hFirst with rfl | ⟨W, hStepW, hRT⟩
  · exact (hSucc hStep _ _ hBack hStep) hBack
  · exact (hSucc hStepW _ _ hRT hStep) hBack

/-- First forced step out of an `externalChoice` head: any reachable state is the head itself or
   past a first step. -/
theorem firstStep_extC_step {q : Role} {branches : List (Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} :
    ∀ {W : SessionType},
    Relation.ReflTransGen (forced_step p lab S) (SessionType.externalChoice q branches) W →
    W = SessionType.externalChoice q branches ∨
    ∃ V, forced_step p lab S (SessionType.externalChoice q branches) V ∧
      Relation.ReflTransGen (forced_step p lab S) V W := by
  intro W h
  induction h with
  | refl => exact Or.inl rfl
  | tail h' hs ih =>
    rcases ih with rfl | ⟨V, hStepV, hRT⟩
    · exact Or.inr ⟨_, hs, Relation.ReflTransGen.refl⟩
    · exact Or.inr ⟨V, hStepV, hRT.trans (Relation.ReflTransGen.single hs)⟩

/-- Step-premise lifting at `externalChoice`: the choice is one-message prunable if all its
   actual forced-step successors are. -/
theorem prunable_one_msg_extC_of_step
    (q : Role) (branches : List (Lab × DataSort × SessionType))
    (p : Role) (lab : Lab) (S : DataSort)
    (hSucc : ∀ {V : SessionType},
      forced_step p lab S (SessionType.externalChoice q branches) V →
      PrunableOneMsg p lab S V) :
    PrunableOneMsg p lab S (SessionType.externalChoice q branches) := by
  intro U V hRTC hStep hBack
  have hFirst := firstStep_extC_step hRTC
  rcases hFirst with rfl | ⟨W, hStepW, hRT⟩
  · exact (hSucc hStep _ _ hBack hStep) hBack
  · exact (hSucc hStepW _ _ hRT hStep) hBack

/-- Lifting for `tRec`: prunability of the unfolding implies prunability of
    the recursion (a cycle through `tRec` closes to a cycle at its
    unfolding, since the `trec` step is deterministic). -/
theorem firstStep_trec {X : String} {B : SessionType}
    {p : Role} {lab : Lab} {S : DataSort} :
    ∀ {W : SessionType},
    Relation.ReflTransGen (forced_step p lab S) (SessionType.tRec X B) W →
    W = SessionType.tRec X B ∨
      Relation.ReflTransGen (forced_step p lab S)
        (substSessionType B X (SessionType.tRec X B)) W := by
  intro W h
  induction h with
  | refl => exact Or.inl rfl
  | tail h' hs ih =>
    rcases ih with rfl | hRT
    · cases hs with
      | trec => exact Or.inr Relation.ReflTransGen.refl
    · exact Or.inr (hRT.trans (Relation.ReflTransGen.single hs))

/-- Step-premise lifting at `tRec`: prunability of the unfolding gives prunability of the
   recursion. -/
theorem prunable_one_msg_trec_of_succ {X : String} {B : SessionType}
    (p : Role) (lab : Lab) (S : DataSort)
    (hOneMsgSub : PrunableOneMsg p lab S (substSessionType B X (SessionType.tRec X B))) :
    PrunableOneMsg p lab S (SessionType.tRec X B) := by
  intro U V hRTC hStep hBack
  have hFirst := firstStep_trec hRTC
  rcases hFirst with rfl | hRT
  · cases hStep with
    | trec => exact (hOneMsgSub _ _ hBack forced_step.trec) hBack
  · exact (hOneMsgSub _ _ hRT hStep) hBack

/-- Stuck heads are unconditionally one-message prunable (nothing is
    reachable except themselves, and they have no steps). -/
theorem prunable_one_msg_end
    (p : Role) (lab : Lab) (S : DataSort) :
    PrunableOneMsg p lab S SessionType.tEnd := by
  have hEq : ∀ {W : SessionType},
      Relation.ReflTransGen (forced_step p lab S) SessionType.tEnd W →
      W = SessionType.tEnd := by
    intro W h
    induction h with
    | refl => rfl
    | tail h' hs ih =>
      subst ih
      cases hs
  intro U V hRTC hStep hBack
  have hU := hEq hRTC
  subst hU
  cases hStep

/-- Stuck heads are unconditionally one-message prunable: nothing is reachable except themselves
   and they have no steps. -/
theorem prunable_one_msg_var (X : String)
    (p : Role) (lab : Lab) (S : DataSort) :
    PrunableOneMsg p lab S (SessionType.tVar X) := by
  have hEq : ∀ {W : SessionType},
      Relation.ReflTransGen (forced_step p lab S) (SessionType.tVar X) W →
      W = SessionType.tVar X := by
    intro W h
    induction h with
    | refl => rfl
    | tail h' hs ih =>
      subst ih
      cases hs
  intro U V hRTC hStep hBack
  have hU := hEq hRTC
  subst hU
  cases hStep

-- Certified-good recursive example (see also the `CxT`/`CxS` demo types).
/-- External offer by `p`: `(a, sa)` continuing into `externalChoice`; `(b, sb)` continuing into
   `externalChoice` (certified-good recursive example). -/
def CxB0 : SessionType :=
  SessionType.externalChoice "p"
    [("a", "sa", SessionType.externalChoice "q" [("x", "sx", SessionType.tVar "X")]),
     ("b", "sb", SessionType.externalChoice "q" [("y", "sy", SessionType.tVar "X")])]
/-- Recursive type: loop on `X` with body `CxB0` (certified-good recursive example). -/
def CxT : SessionType := SessionType.tRec "X" CxB0
/-- External offer by `q`: `(x, sx)` continuing as `CxT` (certified-good recursive example). -/
def CxTa : SessionType :=
  SessionType.externalChoice "q" [("x", "sx", CxT)]
/-- External offer by `q`: `(y, sy)` continuing as `CxT` (certified-good recursive example). -/
def CxTb : SessionType :=
  SessionType.externalChoice "q" [("y", "sy", CxT)]
/-- External offer by `p`: `(a, sa)` continuing as `CxTa`; `(b, sb)` continuing as `CxTb`
   (certified-good recursive example). -/
def CxS : SessionType :=
  SessionType.externalChoice "p" [("a", "sa", CxTa), ("b", "sb", CxTb)]

/-- Grafting equation: substituting `(SessionType.tRec "X" CxB0)` for `X` in `CxB0` yields
   `CxS`. -/
theorem CxS_subst : substSessionType CxB0 "X" (SessionType.tRec "X" CxB0) = CxS := rfl

/-- The prune `Has` check for (`q`, `x`, `sx`) on `CxTb` is `false` (absent from the type). -/
theorem Cx_has_Tb_x_false :
    pruneFirstInputDeepHas "q" "x" "sx" CxTb = false := by decide
/-- The prune `Has` check for (`q`, `y`, `sy`) on `CxTa` is `false` (absent from the type). -/
theorem Cx_has_Ta_y_false :
    pruneFirstInputDeepHas "q" "y" "sy" CxTa = false := by decide

-- One-message prunability trees per concrete exposed triple (lifting leaves:
-- owner-vacuous, `decide`-closed prunes, `trec` chains).
/-- One-message prunability of `CxTa` for (`q`, `x`, `sx`). -/
theorem CxFA_Ta_X : PrunableOneMsg "q" "x" "sx" CxTa :=
  prunable_one_msg_extC_owner "q" _ "x" "sx"
/-- One-message prunability of `CxTb` for (`q`, `x`, `sx`). -/
theorem CxFA_Tb_X : PrunableOneMsg "q" "x" "sx" CxTb :=
  prunable_one_msg_extC_owner "q" _ "x" "sx"
/-- One-message prunability of `CxS` for (`q`, `x`, `sx`). -/
theorem CxFA_S_X : PrunableOneMsg "q" "x" "sx" CxS := by
  apply prunable_one_msg_extC_of_step "p" _ "q" "x" "sx"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact CxFA_Ta_X
    · rw [Cx_has_Tb_x_false] at hHas
      cases hHas
/-- One-message prunability of `CxT` for (`q`, `x`, `sx`). -/
theorem CxFA_T_X : PrunableOneMsg "q" "x" "sx" CxT :=
  prunable_one_msg_trec_of_succ "q" "x" "sx" CxFA_S_X

/-- One-message prunability of `CxTb` for (`q`, `y`, `sy`). -/
theorem CxFA_Tb_Y : PrunableOneMsg "q" "y" "sy" CxTb :=
  prunable_one_msg_extC_owner "q" _ "y" "sy"
/-- One-message prunability of `CxTa` for (`q`, `y`, `sy`). -/
theorem CxFA_Ta_Y : PrunableOneMsg "q" "y" "sy" CxTa :=
  prunable_one_msg_extC_owner "q" _ "y" "sy"
/-- One-message prunability of `CxS` for (`q`, `y`, `sy`). -/
theorem CxFA_S_Y : PrunableOneMsg "q" "y" "sy" CxS := by
  apply prunable_one_msg_extC_of_step "p" _ "q" "y" "sy"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [Cx_has_Ta_y_false] at hHas
      cases hHas
    · exact CxFA_Tb_Y
/-- One-message prunability of `CxT` for (`q`, `y`, `sy`). -/
theorem CxFA_T_Y : PrunableOneMsg "q" "y" "sy" CxT :=
  prunable_one_msg_trec_of_succ "q" "y" "sy" CxFA_S_Y

/-- One-message prunability of `CxS` for (`p`, `a`, `sa`). -/
theorem CxFA_S_A : PrunableOneMsg "p" "a" "sa" CxS := by
  apply prunable_one_msg_extC_of_step "p" _ "p" "a" "sa"
  intro V hS
  cases hS with
  | @extCQ _ _ _ hne _ _ => exact absurd rfl hne
/-- One-message prunability of `CxT` for (`p`, `a`, `sa`). -/
theorem CxFA_T_A : PrunableOneMsg "p" "a" "sa" CxT :=
  prunable_one_msg_trec_of_succ "p" "a" "sa" CxFA_S_A
/-- One-message prunability of `CxTa` for (`p`, `a`, `sa`). -/
theorem CxFA_Ta_A : PrunableOneMsg "p" "a" "sa" CxTa := by
  apply prunable_one_msg_extC_of_step "q" _ "p" "a" "sa"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact CxFA_T_A
/-- One-message prunability of `CxTb` for (`p`, `a`, `sa`). -/
theorem CxFA_Tb_A : PrunableOneMsg "p" "a" "sa" CxTb := by
  apply prunable_one_msg_extC_of_step "q" _ "p" "a" "sa"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact CxFA_T_A

/-- One-message prunability of `CxS` for (`p`, `b`, `sb`). -/
theorem CxFA_S_B : PrunableOneMsg "p" "b" "sb" CxS := by
  apply prunable_one_msg_extC_of_step "p" _ "p" "b" "sb"
  intro V hS
  cases hS with
  | @extCQ _ _ _ hne _ _ => exact absurd rfl hne
/-- One-message prunability of `CxT` for (`p`, `b`, `sb`). -/
theorem CxFA_T_B : PrunableOneMsg "p" "b" "sb" CxT :=
  prunable_one_msg_trec_of_succ "p" "b" "sb" CxFA_S_B
/-- One-message prunability of `CxTa` for (`p`, `b`, `sb`). -/
theorem CxFA_Ta_B : PrunableOneMsg "p" "b" "sb" CxTa := by
  apply prunable_one_msg_extC_of_step "q" _ "p" "b" "sb"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact CxFA_T_B
/-- One-message prunability of `CxTb` for (`p`, `b`, `sb`). -/
theorem CxFA_Tb_B : PrunableOneMsg "p" "b" "sb" CxTb := by
  apply prunable_one_msg_extC_of_step "q" _ "p" "b" "sb"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact CxFA_T_B

-- `hfa` dispatchers: invert the exposure derivation to concrete triples
-- (paths die at `tVar` leaves), then dispatch to the trees above.
/-- One-message prunability fact. -/
theorem Cx_hfaT : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom CxT pm lab0 S0 → PrunableOneMsg pm lab0 S0 CxT := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact CxFA_T_A
      · exact CxFA_T_B
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact CxFA_T_X
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact CxFA_T_Y
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3

/-- One-message prunability fact. -/
theorem Cx_hfaTa : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom CxTa pm lab0 S0 → PrunableOneMsg pm lab0 S0 CxTa := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact CxFA_Ta_X
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "q" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact Cx_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem Cx_hfaTb : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom CxTb pm lab0 S0 → PrunableOneMsg pm lab0 S0 CxTb := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact CxFA_Tb_Y
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "q" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact Cx_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem Cx_hfaS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom CxS pm lab0 S0 → PrunableOneMsg pm lab0 S0 CxS := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact CxFA_S_A
    · exact CxFA_S_B
  | extC_step hne hmem hsub2 =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact CxFA_S_X
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        apply prunable_one_msg_extC_of_step "p" _ pm lab0 S0
        intro V hS
        cases hS with
        | @extCQ _ _ x _ hmem' hHas' =>
          obtain ⟨l, s, U⟩ := x
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact Cx_hfaTa _ _ _ (has_to_exposed _ _ _ _ hHas')
          · exact Cx_hfaTb _ _ _ (has_to_exposed _ _ _ _ hHas')
    · cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact CxFA_S_Y
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        apply prunable_one_msg_extC_of_step "p" _ pm lab0 S0
        intro V hS
        cases hS with
        | @extCQ _ _ x _ hmem' hHas' =>
          obtain ⟨l, s, U⟩ := x
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
          rcases hmem' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact Cx_hfaTa _ _ _ (has_to_exposed _ _ _ _ hHas')
          · exact Cx_hfaTb _ _ _ (has_to_exposed _ _ _ _ hHas')

-- Deep adequacy for `CxT`: `trec_new` over the unfolding, `trec_seen` cuts
-- for the recursive occurrences.
/-- Deep adequacy of `CxT` with empty seen set. -/
theorem Cx_deep : Prunable [] CxT := by
  apply Prunable.trec_new [] "X" CxB0 _ _ Cx_hfaT
  · simp
  · rw [CxS_subst]
    apply Prunable.extC [CxT] "p" _ _ Cx_hfaS
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl
    · apply Prunable.extC [CxT] "q" _ _ Cx_hfaTa
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain rfl := hmemY
      exact Prunable.trec_seen [CxT] "X" CxB0
        (List.mem_cons.mpr (Or.inl rfl)) Cx_hfaT
    · apply Prunable.extC [CxT] "q" _ _ Cx_hfaTb
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain rfl := hmemY
      exact Prunable.trec_seen [CxT] "X" CxB0
        (List.mem_cons.mpr (Or.inl rfl)) Cx_hfaT

-- Single good recursive branch under an off-role owner.
/-- External offer by `r`: `(a, sa)` continuing into `externalChoice` (single good recursive
   branch under an off-role owner). -/
def A1B : SessionType :=
  SessionType.externalChoice "r"
    [("a", "sa", SessionType.externalChoice "q" [("x", "sx", SessionType.tVar "X")])]
/-- Recursive type: loop on `X` with body `A1B` (single good recursive branch under an off-role
   owner). -/
def A1T : SessionType := SessionType.tRec "X" A1B
/-- External offer by `q`: `(x, sx)` continuing as `A1T` (single good recursive branch under an
   off-role owner). -/
def A1U : SessionType :=
  SessionType.externalChoice "q" [("x", "sx", A1T)]
/-- External offer by `r`: `(a, sa)` continuing as `A1U` (single good recursive branch under an
   off-role owner). -/
def A1S : SessionType :=
  SessionType.externalChoice "r" [("a", "sa", A1U)]

/-- Grafting equation: substituting `(SessionType.tRec "X" A1B)` for `X` in `A1B` yields `A1S`. -/
theorem A1S_subst : substSessionType A1B "X" (SessionType.tRec "X" A1B) = A1S := rfl

/-- One-message prunability of `A1U` for (`q`, `x`, `sx`). -/
theorem A1FA_U_X : PrunableOneMsg "q" "x" "sx" A1U :=
  prunable_one_msg_extC_owner "q" _ "x" "sx"
/-- One-message prunability of `A1S` for (`q`, `x`, `sx`). -/
theorem A1FA_S_X : PrunableOneMsg "q" "x" "sx" A1S := by
  apply prunable_one_msg_extC_of_step "r" _ "q" "x" "sx"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact A1FA_U_X
/-- One-message prunability of `A1T` for (`q`, `x`, `sx`). -/
theorem A1FA_T_X : PrunableOneMsg "q" "x" "sx" A1T :=
  prunable_one_msg_trec_of_succ "q" "x" "sx" A1FA_S_X

/-- One-message prunability of `A1S` for (`r`, `a`, `sa`). -/
theorem A1FA_S_A : PrunableOneMsg "r" "a" "sa" A1S := by
  apply prunable_one_msg_extC_of_step "r" _ "r" "a" "sa"
  intro V hS
  cases hS with
  | @extCQ _ _ _ hne _ _ => exact absurd rfl hne
/-- One-message prunability of `A1T` for (`r`, `a`, `sa`). -/
theorem A1FA_T_A : PrunableOneMsg "r" "a" "sa" A1T :=
  prunable_one_msg_trec_of_succ "r" "a" "sa" A1FA_S_A
/-- One-message prunability of `A1U` for (`r`, `a`, `sa`). -/
theorem A1FA_U_A : PrunableOneMsg "r" "a" "sa" A1U := by
  apply prunable_one_msg_extC_of_step "q" _ "r" "a" "sa"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact A1FA_T_A

/-- One-message prunability fact. -/
theorem A1_hfaT : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom A1T pm lab0 S0 → PrunableOneMsg pm lab0 S0 A1T := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact A1FA_T_A
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact A1FA_T_X
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        cases hsub3

/-- One-message prunability fact. -/
theorem A1_hfaU : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom A1U pm lab0 S0 → PrunableOneMsg pm lab0 S0 A1U := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact A1FA_U_X
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "q" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact A1_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem A1_hfaS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom A1S pm lab0 S0 → PrunableOneMsg pm lab0 S0 A1S := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact A1FA_S_A
  | extC_step hne hmem hsub2 =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    cases hsub2 with
    | extC_here hmem2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
      obtain ⟨rfl, rfl, rfl⟩ := hmem2
      exact A1FA_S_X
    | extC_step hne2 hmem2 hsub3 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
      obtain ⟨rfl, rfl, rfl⟩ := hmem2
      cases hsub3 with
      | trec hsub4 =>
        cases hsub4 with
        | extC_here hmem4 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
          obtain ⟨rfl, rfl, rfl⟩ := hmem4
          exact A1FA_S_A
        | extC_step hne4 hmem4 hsub5 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
          obtain ⟨rfl, rfl, rfl⟩ := hmem4
          cases hsub5 with
          | extC_here hmem6 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
            obtain ⟨rfl, rfl, rfl⟩ := hmem6
            exact A1FA_S_X
          | extC_step hne6 hmem6 hsub7 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
            obtain ⟨rfl, rfl, rfl⟩ := hmem6
            cases hsub7

/-- Deep adequacy of `A1T` with empty seen set. -/
theorem A1_deep : Prunable [] A1T := by
  apply Prunable.trec_new [] "X" A1B _ _ A1_hfaT
  · simp
  · rw [A1S_subst]
    apply Prunable.extC [A1T] "r" _ _ A1_hfaS
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain rfl := hmem
    apply Prunable.extC [A1T] "q" _ _ A1_hfaU
    intro y hmemY
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
    obtain rfl := hmemY
    exact Prunable.trec_seen [A1T] "X" A1B
      (List.mem_cons.mpr (Or.inl rfl)) A1_hfaT

-- Internal choice with a single recursive branch.
/-- Internal choice: `(p, a, sa)` continuing into `externalChoice` (internal choice with a
   single recursive branch). -/
def C1B : SessionType :=
  SessionType.internalChoice
    [("p", "a", "sa",
      SessionType.externalChoice "q" [("x", "sx", SessionType.tVar "X")])]
/-- Recursive type: loop on `X` with body `C1B` (internal choice with a single recursive
   branch). -/
def C1T : SessionType := SessionType.tRec "X" C1B
/-- External offer by `q`: `(x, sx)` continuing as `C1T` (internal choice with a single
   recursive branch). -/
def C1U : SessionType :=
  SessionType.externalChoice "q" [("x", "sx", C1T)]
/-- Internal choice: `(p, a, sa)` continuing as `C1U` (internal choice with a single recursive
   branch). -/
def C1S : SessionType :=
  SessionType.internalChoice [("p", "a", "sa", C1U)]

/-- Grafting equation: substituting `(SessionType.tRec "X" C1B)` for `X` in `C1B` yields `C1S`. -/
theorem C1S_subst : substSessionType C1B "X" (SessionType.tRec "X" C1B) = C1S := rfl

/-- One-message prunability of `C1U` for (`q`, `x`, `sx`). -/
theorem C1FA_U_X : PrunableOneMsg "q" "x" "sx" C1U :=
  prunable_one_msg_extC_owner "q" _ "x" "sx"
/-- One-message prunability of `C1S` for (`q`, `x`, `sx`). -/
theorem C1FA_S_X : PrunableOneMsg "q" "x" "sx" C1S := by
  apply prunable_one_msg_intC_of_step _ "q" "x" "sx"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact C1FA_U_X
/-- One-message prunability of `C1T` for (`q`, `x`, `sx`). -/
theorem C1FA_T_X : PrunableOneMsg "q" "x" "sx" C1T :=
  prunable_one_msg_trec_of_succ "q" "x" "sx" C1FA_S_X

/-- One-message prunability fact. -/
theorem C1_hfaT : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom C1T pm lab0 S0 → PrunableOneMsg pm lab0 S0 C1T := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | intC_step hmem hne hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
      cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact C1FA_T_X
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        cases hsub3

/-- One-message prunability fact. -/
theorem C1_hfaU : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom C1U pm lab0 S0 → PrunableOneMsg pm lab0 S0 C1U := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact C1FA_U_X
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "q" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact C1_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem C1_hfaS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom C1S pm lab0 S0 → PrunableOneMsg pm lab0 S0 C1S := by
  intro pm lab0 S0 hexp
  cases hexp with
  | intC_step hmem hne hsub2 =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    cases hsub2 with
    | extC_here hmem2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
      obtain ⟨rfl, rfl, rfl⟩ := hmem2
      exact C1FA_S_X
    | extC_step hne2 hmem2 hsub3 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
      obtain ⟨rfl, rfl, rfl⟩ := hmem2
      cases hsub3 with
      | trec hsub4 =>
        cases hsub4 with
        | intC_step hmem4 hne4 hsub5 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem4
          cases hsub5 with
          | extC_here hmem6 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
            obtain ⟨rfl, rfl, rfl⟩ := hmem6
            exact C1FA_S_X
          | extC_step hne6 hmem6 hsub7 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
            obtain ⟨rfl, rfl, rfl⟩ := hmem6
            cases hsub7

/-- Deep adequacy of `C1T` with empty seen set. -/
theorem C1_deep : Prunable [] C1T := by
  apply Prunable.trec_new [] "X" C1B _ _ C1_hfaT
  · simp
  · rw [C1S_subst]
    apply Prunable.intC [C1T] _ _ C1_hfaS
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain rfl := hmem
    apply Prunable.extC [C1T] "q" _ _ C1_hfaU
    intro y hmemY
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
    obtain rfl := hmemY
    exact Prunable.trec_seen [C1T] "X" C1B
      (List.mem_cons.mpr (Or.inl rfl)) C1_hfaT

-- Nested inner `tRec` looping back to the outer variable.
/-- External offer by `q`: `(x, sx)` looping on `X` (nested inner `tRec` looping back to the
   outer variable). -/
def B1B0 : SessionType :=
  SessionType.externalChoice "q" [("x", "sx", SessionType.tVar "X")]
/-- Recursive type: loop on `Y` with body `B1B0` (nested inner `tRec` looping back to the outer
   variable). -/
def B1U : SessionType :=
  SessionType.tRec "Y" B1B0
/-- External offer by `r`: `(a, sa)` continuing as `B1U` (nested inner `tRec` looping back to
   the outer variable). -/
def B1B : SessionType :=
  SessionType.externalChoice "r" [("a", "sa", B1U)]
/-- Recursive type: loop on `X` with body `B1B` (nested inner `tRec` looping back to the outer
   variable). -/
def B1T : SessionType := SessionType.tRec "X" B1B
/-- External offer by `q`: `(x, sx)` continuing as `B1T` (nested inner `tRec` looping back to
   the outer variable). -/
def B1V : SessionType :=
  SessionType.externalChoice "q" [("x", "sx", B1T)]
/-- Recursive type: loop on `Y` with body `B1V` (nested inner `tRec` looping back to the outer
   variable). -/
def B1Up : SessionType :=
  SessionType.tRec "Y" B1V
/-- External offer by `r`: `(a, sa)` continuing as `B1Up` (nested inner `tRec` looping back to
   the outer variable). -/
def B1S : SessionType :=
  SessionType.externalChoice "r" [("a", "sa", B1Up)]

/-- Grafting equation: substituting `(SessionType.tRec "X" B1B)` for `X` in `B1B` yields `B1S`. -/
theorem B1S_subst : substSessionType B1B "X" (SessionType.tRec "X" B1B) = B1S := rfl
/-- Grafting equation: substituting `(SessionType.tRec "Y" B1V)` for `Y` in `B1V` yields `B1V`. -/
theorem B1V_subst : substSessionType B1V "Y" (SessionType.tRec "Y" B1V) = B1V := rfl

/-- One-message prunability of `B1S` for (`r`, `a`, `sa`). -/
theorem B1FA_S_A : PrunableOneMsg "r" "a" "sa" B1S := by
  apply prunable_one_msg_extC_of_step "r" _ "r" "a" "sa"
  intro V hS
  cases hS with
  | @extCQ _ _ _ hne _ _ => exact absurd rfl hne
/-- One-message prunability of `B1T` for (`r`, `a`, `sa`). -/
theorem B1FA_T_A : PrunableOneMsg "r" "a" "sa" B1T :=
  prunable_one_msg_trec_of_succ "r" "a" "sa" B1FA_S_A
/-- One-message prunability of `B1V` for (`r`, `a`, `sa`). -/
theorem B1FA_V_A : PrunableOneMsg "r" "a" "sa" B1V := by
  apply prunable_one_msg_extC_of_step "q" _ "r" "a" "sa"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact B1FA_T_A
/-- One-message prunability of `B1Up` for (`r`, `a`, `sa`). -/
theorem B1FA_Up_A : PrunableOneMsg "r" "a" "sa" B1Up :=
  prunable_one_msg_trec_of_succ "r" "a" "sa" B1FA_V_A

/-- One-message prunability of `B1V` for (`q`, `x`, `sx`). -/
theorem B1FA_V_X : PrunableOneMsg "q" "x" "sx" B1V :=
  prunable_one_msg_extC_owner "q" _ "x" "sx"
/-- One-message prunability of `B1Up` for (`q`, `x`, `sx`). -/
theorem B1FA_Up_X : PrunableOneMsg "q" "x" "sx" B1Up :=
  prunable_one_msg_trec_of_succ "q" "x" "sx" B1FA_V_X
/-- One-message prunability of `B1S` for (`q`, `x`, `sx`). -/
theorem B1FA_S_X : PrunableOneMsg "q" "x" "sx" B1S := by
  apply prunable_one_msg_extC_of_step "r" _ "q" "x" "sx"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact B1FA_Up_X
/-- One-message prunability of `B1T` for (`q`, `x`, `sx`). -/
theorem B1FA_T_X : PrunableOneMsg "q" "x" "sx" B1T :=
  prunable_one_msg_trec_of_succ "q" "x" "sx" B1FA_S_X

/-- One-message prunability fact. -/
theorem B1_hfaT : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom B1T pm lab0 S0 → PrunableOneMsg pm lab0 S0 B1T := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact B1FA_T_A
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      cases hsub2 with
      | trec hsub3 =>
        cases hsub3 with
        | extC_here hmem3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
          obtain ⟨rfl, rfl, rfl⟩ := hmem3
          exact B1FA_T_X
        | extC_step hne3 hmem3 hsub4 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
          obtain ⟨rfl, rfl, rfl⟩ := hmem3
          cases hsub4

/-- One-message prunability fact. -/
theorem B1_hfaUp : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom B1Up pm lab0 S0 → PrunableOneMsg pm lab0 S0 B1Up := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact B1FA_Up_X
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      cases hsub2 with
      | trec hsub3 =>
        cases hsub3 with
        | extC_here hmem3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
          obtain ⟨rfl, rfl, rfl⟩ := hmem3
          exact B1FA_Up_A
        | extC_step hne3 hmem3 hsub4 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
          obtain ⟨rfl, rfl, rfl⟩ := hmem3
          cases hsub4 with
          | trec hsub5 =>
            cases hsub5 with
            | extC_here hmem5 =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem5
              obtain ⟨rfl, rfl, rfl⟩ := hmem5
              exact B1FA_Up_X
            | extC_step hne5 hmem5 hsub6 =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem5
              obtain ⟨rfl, rfl, rfl⟩ := hmem5
              cases hsub6

/-- One-message prunability fact. -/
theorem B1_hfaV : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom B1V pm lab0 S0 → PrunableOneMsg pm lab0 S0 B1V := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact B1FA_V_X
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "q" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact B1_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem B1_hfaS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom B1S pm lab0 S0 → PrunableOneMsg pm lab0 S0 B1S := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact B1FA_S_A
  | extC_step hne hmem hsub2 =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    cases hsub2 with
    | trec hsub3 =>
      cases hsub3 with
      | extC_here hmem3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
        obtain ⟨rfl, rfl, rfl⟩ := hmem3
        exact B1FA_S_X
      | extC_step hne3 hmem3 hsub4 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
        obtain ⟨rfl, rfl, rfl⟩ := hmem3
        cases hsub4 with
        | trec hsub5 =>
          cases hsub5 with
          | extC_here hmem5 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem5
            obtain ⟨rfl, rfl, rfl⟩ := hmem5
            exact B1FA_S_A
          | extC_step hne5 hmem5 hsub6 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem5
            obtain ⟨rfl, rfl, rfl⟩ := hmem5
            cases hsub6 with
            | trec hsub7 =>
              cases hsub7 with
              | extC_here hmem7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                obtain ⟨rfl, rfl, rfl⟩ := hmem7
                exact B1FA_S_X
              | extC_step hne7 hmem7 hsub8 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem7
                obtain ⟨rfl, rfl, rfl⟩ := hmem7
                cases hsub8

/-- Freshness: `B1Up` is distinct from the listed states. -/
theorem B1Up_fresh : B1Up ∉ [B1T] := by
  intro hcon
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hcon
  injection hcon with hXY _
  exact absurd hXY (by decide)

/-- Deep adequacy of `B1T` with empty seen set. -/
theorem B1_deep : Prunable [] B1T := by
  apply Prunable.trec_new [] "X" B1B _ _ B1_hfaT
  · simp
  · rw [B1S_subst]
    apply Prunable.extC [B1T] "r" _ _ B1_hfaS
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain rfl := hmem
    apply Prunable.trec_new [B1T] "Y" B1V _ _ B1_hfaUp
    · exact B1Up_fresh
    · rw [B1V_subst]
      apply Prunable.extC [B1Up, B1T] "q" _ _ B1_hfaV
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain rfl := hmemY
      exact Prunable.trec_seen [B1Up, B1T] "X" B1B
        (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))) B1_hfaT

-- `intC` recursion with symmetric branches (`Has`-false at `T` for both
-- messages, so `decide`-filters discharge the off branches).
/-- Internal choice: `(p, a, sa)` continuing into `externalChoice`; `(q, b, sb)` continuing into
   `externalChoice` (`intC` recursion with symmetric branches). -/
def ExB0 : SessionType :=
  SessionType.internalChoice
    [("p", "a", "sa",
      SessionType.externalChoice "p" [("x", "sx", SessionType.tVar "X")]),
     ("q", "b", "sb",
      SessionType.externalChoice "q" [("y", "sy", SessionType.tVar "X")])]
/-- Recursive type: loop on `X` with body `ExB0` (`intC` recursion with symmetric branches). -/
def ExT : SessionType := SessionType.tRec "X" ExB0
/-- External offer by `p`: `(x, sx)` continuing as `ExT` (`intC` recursion with symmetric
   branches). -/
def ExTa : SessionType :=
  SessionType.externalChoice "p" [("x", "sx", ExT)]
/-- External offer by `q`: `(y, sy)` continuing as `ExT` (`intC` recursion with symmetric
   branches). -/
def ExTb : SessionType :=
  SessionType.externalChoice "q" [("y", "sy", ExT)]
/-- Internal choice: `(p, a, sa)` continuing as `ExTa`; `(q, b, sb)` continuing as `ExTb`
   (`intC` recursion with symmetric branches). -/
def ExS : SessionType :=
  SessionType.internalChoice [("p", "a", "sa", ExTa), ("q", "b", "sb", ExTb)]

/-- Grafting equation: substituting `(SessionType.tRec "X" ExB0)` for `X` in `ExB0` yields
   `ExS`. -/
theorem ExS_subst : substSessionType ExB0 "X" (SessionType.tRec "X" ExB0) = ExS := rfl

/-- The prune `Has` check for (`p`, `x`, `sx`) on `ExT` is `false` (absent from the type). -/
theorem Ex_has_T_px_false :
    pruneFirstInputDeepHas "p" "x" "sx" ExT = false := by decide
/-- The prune `Has` check for (`q`, `y`, `sy`) on `ExT` is `false` (absent from the type). -/
theorem Ex_has_T_qy_false :
    pruneFirstInputDeepHas "q" "y" "sy" ExT = false := by decide
/-- The prune `Has` check for (`p`, `x`, `sx`) on `ExTb` is `false` (absent from the type). -/
theorem Ex_has_Tb_px_false :
    pruneFirstInputDeepHas "p" "x" "sx" ExTb = false := by decide
/-- The prune `Has` check for (`q`, `y`, `sy`) on `ExTa` is `false` (absent from the type). -/
theorem Ex_has_Ta_qy_false :
    pruneFirstInputDeepHas "q" "y" "sy" ExTa = false := by decide

/-- One-message prunability of `ExTa` for (`p`, `x`, `sx`). -/
theorem ExFA_Ta_X : PrunableOneMsg "p" "x" "sx" ExTa :=
  prunable_one_msg_extC_owner "p" _ "x" "sx"
/-- One-message prunability of `ExS` for (`p`, `x`, `sx`). -/
theorem ExFA_S_X : PrunableOneMsg "p" "x" "sx" ExS := by
  apply prunable_one_msg_intC_of_step _ "p" "x" "sx"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ExFA_Ta_X
    · rw [Ex_has_Tb_px_false] at hHas
      cases hHas
/-- One-message prunability of `ExT` for (`p`, `x`, `sx`). -/
theorem ExFA_T_X : PrunableOneMsg "p" "x" "sx" ExT :=
  prunable_one_msg_trec_of_succ "p" "x" "sx" ExFA_S_X

/-- One-message prunability of `ExTb` for (`q`, `y`, `sy`). -/
theorem ExFA_Tb_Y : PrunableOneMsg "q" "y" "sy" ExTb :=
  prunable_one_msg_extC_owner "q" _ "y" "sy"
/-- One-message prunability of `ExS` for (`q`, `y`, `sy`). -/
theorem ExFA_S_Y : PrunableOneMsg "q" "y" "sy" ExS := by
  apply prunable_one_msg_intC_of_step _ "q" "y" "sy"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [Ex_has_Ta_qy_false] at hHas
      cases hHas
    · exact ExFA_Tb_Y
/-- One-message prunability of `ExT` for (`q`, `y`, `sy`). -/
theorem ExFA_T_Y : PrunableOneMsg "q" "y" "sy" ExT :=
  prunable_one_msg_trec_of_succ "q" "y" "sy" ExFA_S_Y

/-- One-message prunability fact. -/
theorem Ex_hfaT : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom ExT pm lab0 S0 → PrunableOneMsg pm lab0 S0 ExT := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | intC_step hmem hne hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact ExFA_T_X
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact ExFA_T_Y
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3

/-- One-message prunability fact. -/
theorem Ex_hfaTa : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom ExTa pm lab0 S0 → PrunableOneMsg pm lab0 S0 ExTa := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ExFA_Ta_X
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "p" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact Ex_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem Ex_hfaTb : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom ExTb pm lab0 S0 → PrunableOneMsg pm lab0 S0 ExTb := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact ExFA_Tb_Y
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "q" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact Ex_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem Ex_hfaS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom ExS pm lab0 S0 → PrunableOneMsg pm lab0 S0 ExS := by
  intro pm lab0 S0 hexp
  cases hexp with
  | intC_step hmem hne hsub2 =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact ExFA_S_X
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        cases hsub3 with
        | trec hsub4 =>
          cases hsub4 with
          | intC_step hmem4 hne4 hsub5 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
            rcases hmem4 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · cases hsub5 with
              | extC_here hmem6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                exact ExFA_S_X
              | extC_step hne6 hmem6 hsub7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                cases hsub7
            · cases hsub5 with
              | extC_here hmem6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                exact ExFA_S_Y
              | extC_step hne6 hmem6 hsub7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                cases hsub7
    · cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact ExFA_S_Y
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        cases hsub3 with
        | trec hsub4 =>
          cases hsub4 with
          | intC_step hmem4 hne4 hsub5 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
            rcases hmem4 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · cases hsub5 with
              | extC_here hmem6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                exact ExFA_S_X
              | extC_step hne6 hmem6 hsub7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                cases hsub7
            · cases hsub5 with
              | extC_here hmem6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                exact ExFA_S_Y
              | extC_step hne6 hmem6 hsub7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                cases hsub7

/-- Deep adequacy of `ExT` with empty seen set. -/
theorem Ex_deep : Prunable [] ExT := by
  apply Prunable.trec_new [] "X" ExB0 _ _ Ex_hfaT
  · simp
  · rw [ExS_subst]
    apply Prunable.intC [ExT] _ _ Ex_hfaS
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl
    · apply Prunable.extC [ExT] "p" _ _ Ex_hfaTa
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain rfl := hmemY
      exact Prunable.trec_seen [ExT] "X" ExB0
        (List.mem_cons.mpr (Or.inl rfl)) Ex_hfaT
    · apply Prunable.extC [ExT] "q" _ _ Ex_hfaTb
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain rfl := hmemY
      exact Prunable.trec_seen [ExT] "X" ExB0
        (List.mem_cons.mpr (Or.inl rfl)) Ex_hfaT

-- `intC` recursion with shared owner.
/-- Internal choice: `(p, a, sa)` continuing into `externalChoice`; `(q, b, sb)` continuing into
   `externalChoice` (`intC` recursion with shared owner). -/
def FxB0 : SessionType :=
  SessionType.internalChoice
    [("p", "a", "sa",
      SessionType.externalChoice "r" [("x", "sx", SessionType.tVar "X")]),
     ("q", "b", "sb",
      SessionType.externalChoice "r" [("y", "sy", SessionType.tVar "X")])]
/-- Recursive type: loop on `X` with body `FxB0` (`intC` recursion with shared owner). -/
def FxT : SessionType := SessionType.tRec "X" FxB0
/-- External offer by `r`: `(x, sx)` continuing as `FxT` (`intC` recursion with shared owner). -/
def FxTa : SessionType :=
  SessionType.externalChoice "r" [("x", "sx", FxT)]
/-- External offer by `r`: `(y, sy)` continuing as `FxT` (`intC` recursion with shared owner). -/
def FxTb : SessionType :=
  SessionType.externalChoice "r" [("y", "sy", FxT)]
/-- Internal choice: `(p, a, sa)` continuing as `FxTa`; `(q, b, sb)` continuing as `FxTb`
   (`intC` recursion with shared owner). -/
def FxS : SessionType :=
  SessionType.internalChoice [("p", "a", "sa", FxTa), ("q", "b", "sb", FxTb)]

/-- Grafting equation: substituting `(SessionType.tRec "X" FxB0)` for `X` in `FxB0` yields
   `FxS`. -/
theorem FxS_subst : substSessionType FxB0 "X" (SessionType.tRec "X" FxB0) = FxS := rfl

/-- The prune `Has` check for (`r`, `x`, `sx`) on `FxTb` is `false` (absent from the type). -/
theorem Fx_has_Tb_rx_false :
    pruneFirstInputDeepHas "r" "x" "sx" FxTb = false := by decide
/-- The prune `Has` check for (`r`, `y`, `sy`) on `FxTa` is `false` (absent from the type). -/
theorem Fx_has_Ta_ry_false :
    pruneFirstInputDeepHas "r" "y" "sy" FxTa = false := by decide

/-- One-message prunability of `FxTa` for (`r`, `x`, `sx`). -/
theorem FxFA_Ta_X : PrunableOneMsg "r" "x" "sx" FxTa :=
  prunable_one_msg_extC_owner "r" _ "x" "sx"
/-- One-message prunability of `FxS` for (`r`, `x`, `sx`). -/
theorem FxFA_S_X : PrunableOneMsg "r" "x" "sx" FxS := by
  apply prunable_one_msg_intC_of_step _ "r" "x" "sx"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact FxFA_Ta_X
    · rw [Fx_has_Tb_rx_false] at hHas
      cases hHas
/-- One-message prunability of `FxT` for (`r`, `x`, `sx`). -/
theorem FxFA_T_X : PrunableOneMsg "r" "x" "sx" FxT :=
  prunable_one_msg_trec_of_succ "r" "x" "sx" FxFA_S_X

/-- One-message prunability of `FxTb` for (`r`, `y`, `sy`). -/
theorem FxFA_Tb_Y : PrunableOneMsg "r" "y" "sy" FxTb :=
  prunable_one_msg_extC_owner "r" _ "y" "sy"
/-- One-message prunability of `FxS` for (`r`, `y`, `sy`). -/
theorem FxFA_S_Y : PrunableOneMsg "r" "y" "sy" FxS := by
  apply prunable_one_msg_intC_of_step _ "r" "y" "sy"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [Fx_has_Ta_ry_false] at hHas
      cases hHas
    · exact FxFA_Tb_Y
/-- One-message prunability of `FxT` for (`r`, `y`, `sy`). -/
theorem FxFA_T_Y : PrunableOneMsg "r" "y" "sy" FxT :=
  prunable_one_msg_trec_of_succ "r" "y" "sy" FxFA_S_Y

/-- One-message prunability fact. -/
theorem Fx_hfaT : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FxT pm lab0 S0 → PrunableOneMsg pm lab0 S0 FxT := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | intC_step hmem hne hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact FxFA_T_X
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact FxFA_T_Y
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3

/-- One-message prunability fact. -/
theorem Fx_hfaTa : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FxTa pm lab0 S0 → PrunableOneMsg pm lab0 S0 FxTa := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact FxFA_Ta_X
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "r" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact Fx_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem Fx_hfaTb : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FxTb pm lab0 S0 → PrunableOneMsg pm lab0 S0 FxTb := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact FxFA_Tb_Y
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "r" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' _ =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact Fx_hfaT _ _ _ hsub

/-- One-message prunability fact. -/
theorem Fx_hfaS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom FxS pm lab0 S0 → PrunableOneMsg pm lab0 S0 FxS := by
  intro pm lab0 S0 hexp
  cases hexp with
  | intC_step hmem hne hsub2 =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact FxFA_S_X
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        cases hsub3 with
        | trec hsub4 =>
          cases hsub4 with
          | intC_step hmem4 hne4 hsub5 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
            rcases hmem4 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · cases hsub5 with
              | extC_here hmem6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                exact FxFA_S_X
              | extC_step hne6 hmem6 hsub7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                cases hsub7
            · cases hsub5 with
              | extC_here hmem6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                exact FxFA_S_Y
              | extC_step hne6 hmem6 hsub7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                cases hsub7
    · cases hsub2 with
      | extC_here hmem2 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        exact FxFA_S_Y
      | extC_step hne2 hmem2 hsub3 =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        cases hsub3 with
        | trec hsub4 =>
          cases hsub4 with
          | intC_step hmem4 hne4 hsub5 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
            rcases hmem4 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
            · cases hsub5 with
              | extC_here hmem6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                exact FxFA_S_X
              | extC_step hne6 hmem6 hsub7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                cases hsub7
            · cases hsub5 with
              | extC_here hmem6 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                exact FxFA_S_Y
              | extC_step hne6 hmem6 hsub7 =>
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem6
                obtain ⟨rfl, rfl, rfl⟩ := hmem6
                cases hsub7

/-- Deep adequacy of `FxT` with empty seen set. -/
theorem Fx_deep : Prunable [] FxT := by
  apply Prunable.trec_new [] "X" FxB0 _ _ Fx_hfaT
  · simp
  · rw [FxS_subst]
    apply Prunable.intC [FxT] _ _ Fx_hfaS
    intro x hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl
    · apply Prunable.extC [FxT] "r" _ _ Fx_hfaTa
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain rfl := hmemY
      exact Prunable.trec_seen [FxT] "X" FxB0
        (List.mem_cons.mpr (Or.inl rfl)) Fx_hfaT
    · apply Prunable.extC [FxT] "r" _ _ Fx_hfaTb
      intro y hmemY
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
      obtain rfl := hmemY
      exact Prunable.trec_seen [FxT] "X" FxB0
        (List.mem_cons.mpr (Or.inl rfl)) Fx_hfaT

-- `KxT` rejection: certified `forced_step` cycle `T → S → T`, plus exposure, so no `Deep`.
/-- External offer by `q`: `(x, sx)` ending in `tEnd` (rejection witness (`Has`-inherited
   loop)). -/
def KxD : SessionType :=
  SessionType.externalChoice "q" [("x", "sx", SessionType.tEnd)]
/-- External offer by `r`: `(a, sa)` continuing as `KxD`; `(b, sb)` looping on `X` (rejection
   witness (`Has`-inherited loop)). -/
def KxB : SessionType :=
  SessionType.externalChoice "r"
    [("a", "sa", KxD), ("b", "sb", SessionType.tVar "X")]
/-- Recursive type: loop on `X` with body `KxB` (rejection witness (`Has`-inherited loop)). -/
def KxT : SessionType := SessionType.tRec "X" KxB
/-- The prune `Has` check for (`q`, `x`, `sx`) on `KxT` is `true` (offered by the type). -/
def KxS : SessionType :=
  SessionType.externalChoice "r" [("a", "sa", KxD), ("b", "sb", KxT)]

/-- The prune `Has` check for (`q`, `x`, `sx`) on `KxT` is `true` (offered by the type). -/
theorem Kx_has_T : pruneFirstInputDeepHas "q" "x" "sx" KxT = true := by
  decide

/-- One-message prunability of `KxT` for (`q`, `x`, `sx`). -/
theorem Kx_not_prunable_one_msg : ¬ PrunableOneMsg "q" "x" "sx" KxT := by
  intro hOneMsg
  have hmemB : ("b", "sb", KxT) ∈
      ([("a", "sa", KxD), ("b", "sb", KxT)] : List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hT : forced_step "q" "x" "sx" KxT KxS := forced_step.trec
  have hB : forced_step "q" "x" "sx" KxS KxT :=
    forced_step.extCQ (by decide) hmemB Kx_has_T
  have hRTC : Relation.ReflTransGen (forced_step "q" "x" "sx") KxT KxS :=
    Relation.ReflTransGen.single hT
  exact hOneMsg KxS KxT hRTC hB hRTC

/-- Exposure: `KxT` offers `("q", "x", "sx")`. -/
theorem KxT_exposed : ExposedFrom KxT "q" "x" "sx" := by
  have hX : ("x", "sx", SessionType.tEnd) ∈
      ([("x", "sx", SessionType.tEnd)] : List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  have hD : ExposedFrom KxD "q" "x" "sx" := ExposedFrom.extC_here hX
  have hA : ("a", "sa", KxD) ∈
      ([("a", "sa", KxD), ("b", "sb", SessionType.tVar "X")] :
        List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  have hB : ExposedFrom KxB "q" "x" "sx" :=
    ExposedFrom.extC_step (by decide) hA hD
  exact ExposedFrom.trec hB

/-- Deep adequacy of `KxT` with empty seen set. -/
theorem KxT_not_deep : ¬ Prunable [] KxT := by
  intro hPrunable
  exact Kx_not_prunable_one_msg (deep_has_acyclic hPrunable "q" "x" "sx" KxT_exposed)

-- `GxT` rejection (split owners; genuine cross-fire cycle).
/-- Internal choice: `(p, a, sa)` continuing into `externalChoice`; `(q, b, sb)` continuing into
   `externalChoice` (rejection witness (split owners; cross-fire cycle)). -/
def GxB0 : SessionType :=
  SessionType.internalChoice
    [("p", "a", "sa",
      SessionType.externalChoice "r1" [("x", "sx", SessionType.tVar "X")]),
     ("q", "b", "sb",
      SessionType.externalChoice "r2" [("y", "sy", SessionType.tVar "X")])]
/-- Recursive type: loop on `X` with body `GxB0` (rejection witness (split owners; cross-fire
   cycle)). -/
def GxT : SessionType := SessionType.tRec "X" GxB0
/-- External offer by `r1`: `(x, sx)` continuing as `GxT` (rejection witness (split owners;
   cross-fire cycle)). -/
def GxTa : SessionType :=
  SessionType.externalChoice "r1" [("x", "sx", GxT)]
/-- External offer by `r2`: `(y, sy)` continuing as `GxT` (rejection witness (split owners;
   cross-fire cycle)). -/
def GxTb : SessionType :=
  SessionType.externalChoice "r2" [("y", "sy", GxT)]
/-- Internal choice: `(p, a, sa)` continuing as `GxTa`; `(q, b, sb)` continuing as `GxTb`
   (rejection witness (split owners; cross-fire cycle)). -/
def GxS : SessionType :=
  SessionType.internalChoice [("p", "a", "sa", GxTa), ("q", "b", "sb", GxTb)]

/-- One-message prunability of `GxT` for (`r1`, `x`, `sx`). -/
theorem Gx_not_prunable_one_msg_rx : ¬ PrunableOneMsg "r1" "x" "sx" GxT := by
  intro hOneMsg
  have hmemB : ("q", "b", "sb", GxTb) ∈
      ([("p", "a", "sa", GxTa), ("q", "b", "sb", GxTb)] :
        List (Role × Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  have hmemY : ("y", "sy", GxT) ∈
      ([("y", "sy", GxT)] : List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  have hHasTb : pruneFirstInputDeepHas "r1" "x" "sx" GxTb = true := by
    decide
  have hHasT : pruneFirstInputDeepHas "r1" "x" "sx" GxT = true := by
    decide
  have hT : forced_step "r1" "x" "sx" GxT GxS := forced_step.trec
  have hB : forced_step "r1" "x" "sx" GxS GxTb := forced_step.intC hmemB hHasTb
  have hTb : forced_step "r1" "x" "sx" GxTb GxT :=
    forced_step.extCQ (by decide) hmemY hHasT
  have hRTC : Relation.ReflTransGen (forced_step "r1" "x" "sx") GxT GxTb :=
    (Relation.ReflTransGen.single hT).trans
      (Relation.ReflTransGen.single hB)
  exact hOneMsg GxTb GxT hRTC hTb hRTC

/-- Exposure: `GxT` offers `("r1", "x", "sx")`. -/
theorem GxT_exposed_rx : ExposedFrom GxT "r1" "x" "sx" := by
  have hX : ("x", "sx", SessionType.tVar "X") ∈
      ([("x", "sx", SessionType.tVar "X")] : List (Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  have hOpen : ExposedFrom
      (SessionType.externalChoice "r1" [("x", "sx", SessionType.tVar "X")])
      "r1" "x" "sx" := ExposedFrom.extC_here hX
  have hB : ("p", "a", "sa",
      SessionType.externalChoice "r1" [("x", "sx", SessionType.tVar "X")]) ∈
      ([("p", "a", "sa",
        SessionType.externalChoice "r1" [("x", "sx", SessionType.tVar "X")]),
       ("q", "b", "sb",
        SessionType.externalChoice "r2" [("y", "sy", SessionType.tVar "X")])] :
        List (Role × Lab × DataSort × SessionType)) :=
    List.mem_cons.mpr (Or.inl rfl)
  have hnePR1 : ("p" : Role) ≠ "r1" := by decide
  have hStep : ExposedFrom GxB0 "r1" "x" "sx" :=
    ExposedFrom.intC_step hB hnePR1 hOpen
  exact ExposedFrom.trec hStep
mutual
/-- Boolean recursion check: `true` exactly for `tRec`-free types. -/
def no_rec_bool : SessionType → Bool
  | .tEnd => true
  | .tVar _ => true
  | .tRec _ _ => false
  | .internalChoice bs => no_rec_bool_int bs
  | .externalChoice _ bs => no_rec_bool_ext bs
/-- Boolean recursion check over internal-choice branch lists. -/
def no_rec_bool_int : List (Role × Lab × DataSort × SessionType) → Bool
  | [] => true
  | (_, _, _, T') :: rest => no_rec_bool T' && no_rec_bool_int rest
/-- Boolean recursion check over external-choice branch lists. -/
def no_rec_bool_ext : List (Lab × DataSort × SessionType) → Bool
  | [] => true
  | (_, _, T') :: rest => no_rec_bool T' && no_rec_bool_ext rest
end

/-- A `true` boolean check on an internal branch list gives `true` on every member target. -/
theorem no_rec_bool_int_mem : ∀ (bs : List (Role × Lab × DataSort × SessionType)),
    no_rec_bool_int bs = true →
    ∀ x ∈ bs, no_rec_bool x.2.2.2 = true := by
  intro bs
  induction bs with
  | nil => intro h x hx; simp at hx
  | cons hd tl ih =>
    obtain ⟨r, l, s, U0⟩ := hd
    intro h x hx
    simp only [no_rec_bool_int, Bool.and_eq_true] at h
    obtain ⟨hHd, hTl⟩ := h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · simpa using hHd
    · exact ih hTl x hmem

/-- A `true` boolean check on an external branch list gives `true` on every member target. -/
theorem no_rec_bool_ext_mem : ∀ (bs : List (Lab × DataSort × SessionType)),
    no_rec_bool_ext bs = true →
    ∀ x ∈ bs, no_rec_bool x.2.2 = true := by
  intro bs
  induction bs with
  | nil => intro h x hx; simp at hx
  | cons hd tl ih =>
    obtain ⟨l, s, U0⟩ := hd
    intro h x hx
    simp only [no_rec_bool_ext, Bool.and_eq_true] at h
    obtain ⟨hHd, hTl⟩ := h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · simpa using hHd
    · exact ih hTl x hmem

/-- Boolean check soundness, by strong size induction: `no_rec_bool T = true` implies `T.NoRec`. -/
theorem no_rec_bool_true_aux (n : Nat) :
    ∀ (T : SessionType), sizeOf T < n → no_rec_bool T = true → T.NoRec := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hSize hB
    cases T with
    | tEnd => exact SessionType.NoRec.end
    | tVar X => exact SessionType.NoRec.tVar X
    | tRec X B =>
      simp only [no_rec_bool] at hB
      cases hB
    | internalChoice branches =>
      simp only [no_rec_bool] at hB
      apply SessionType.NoRec.internalChoice
      intro x hx
      obtain ⟨r, l, s, U0⟩ := x
      have hmem : (r, l, s, U0) ∈ branches := hx
      have h1 : sizeOf U0 < sizeOf (SessionType.internalChoice branches) :=
        sizeOf_SessionType_lt_sizeOf_internalChoice hmem
      have hT : no_rec_bool U0 = true := no_rec_bool_int_mem branches hB _ hmem
      exact ih _ hSize _ h1 hT
    | externalChoice p branches =>
      simp only [no_rec_bool] at hB
      apply SessionType.NoRec.externalChoice
      intro x hx
      obtain ⟨l, s, U0⟩ := x
      have hmem : (l, s, U0) ∈ branches := hx
      have h1 : sizeOf U0 < sizeOf (SessionType.externalChoice p branches) :=
        sizeOf_SessionType_lt_sizeOf_externalChoice (p := p) hmem
      have hT : no_rec_bool U0 = true := no_rec_bool_ext_mem branches hB _ hmem
      exact ih _ hSize _ h1 hT

/-- Boolean check soundness: `no_rec_bool T = true` implies `T.NoRec`. -/
theorem no_rec_bool_true {T : SessionType} (h : no_rec_bool T = true) : T.NoRec :=
  no_rec_bool_true_aux (sizeOf T + 1) T (Nat.lt_succ_self _) h

-- `forced_step` preserves `NoRec` (`trec` cannot fire: no `trec` head under `NoRec`).
/-- `The witness` is recursion-free. -/
theorem forced_step_norec_target {T U : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (h : forced_step p lab S T U) (hNR : T.NoRec) : U.NoRec := by
  cases h with
  | trec => cases hNR
  | extCQ hne hmem hHas => exact noRec_of_mem_extBranches hNR hmem
  | intC hmem hHas => exact noRec_of_mem_intBranches hNR hmem

/-- `The witness` is recursion-free. -/
theorem forced_step_norec_rtc {T U : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (h : Relation.ReflTransGen (forced_step p lab S) T U) (hNR : T.NoRec) : U.NoRec := by
  induction h with
  | refl => exact hNR
  | tail h' hs ih => exact forced_step_norec_target hs ih

-- `forced_step`s strictly shrink size under `NoRec`.
/-- Forced steps strictly shrink `sizeOf` for recursion-free types. -/
theorem forced_step_size_lt_of_norec {T U : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (h : forced_step p lab S T U) (hNR : T.NoRec) : sizeOf U < sizeOf T := by
  cases h with
  | trec => cases hNR
  | @extCQ q branches x hne hmem hHas =>
    obtain ⟨l, s, T0⟩ := x
    exact sizeOf_SessionType_lt_sizeOf_externalChoice hmem
  | @intC branches x hmem hHas =>
    obtain ⟨r, l, s, T0⟩ := x
    exact sizeOf_SessionType_lt_sizeOf_internalChoice hmem

/-- Forced-step reachability never grows `sizeOf` for recursion-free types. -/
theorem rtc_norec_size_le {T U : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (h : Relation.ReflTransGen (forced_step p lab S) T U) (hNR : T.NoRec) :
    sizeOf U ≤ sizeOf T := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail h' hs ih =>
    have hNR' := forced_step_norec_rtc h' hNR
    exact Nat.le_trans (Nat.le_of_lt (forced_step_size_lt_of_norec hs hNR')) ih

/-- One-message prunability from `NoRec`, by strong size induction: a cycle
    at `U` contradicts prunability at the strictly smaller step-target `V`. -/
theorem norec_prunable_one_msg_aux (n : Nat) :
    ∀ (T : SessionType), sizeOf T < n → T.NoRec →
    ∀ (p : Role) (lab : Lab) (S : DataSort), PrunableOneMsg p lab S T := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hSize hNR p lab S U V hRTC hStep hBack
    have hNRU : U.NoRec := forced_step_norec_rtc hRTC hNR
    have hleU : sizeOf U ≤ sizeOf T := rtc_norec_size_le hRTC hNR
    have hUlt : sizeOf U < n := lt_of_le_of_lt hleU hSize
    have hltV : sizeOf V < sizeOf U := forced_step_size_lt_of_norec hStep hNRU
    have hNRV : V.NoRec :=
      forced_step_norec_rtc (Relation.ReflTransGen.single hStep) hNRU
    exact (ih _ hUlt _ hltV hNRV _ _ _ _ _ hBack hStep) hBack

/-- Every recursion-free type is one-message prunable for every target message. -/
theorem norec_prunable_one_msg {T : SessionType} (hNR : T.NoRec)
    (p : Role) (lab : Lab) (S : DataSort) : PrunableOneMsg p lab S T :=
  norec_prunable_one_msg_aux (sizeOf T + 1) T (Nat.lt_succ_self _) hNR p lab S

/-- Every recursion-free type is deeply adequate under any seen set. -/
theorem norec_deep {T : SessionType} (hNR : T.NoRec)
    (seen : List SessionType) : Prunable seen T := by
  induction hNR
  next => exact Prunable.tEnd seen
  next X => exact Prunable.tvar seen X
  next hall ih =>
    exact Prunable.intC seen _
      (fun x hx => ih x hx)
      (fun p lab S _ => norec_prunable_one_msg
        (SessionType.NoRec.internalChoice hall) p lab S)
  next hall ih =>
    exact Prunable.extC seen _ _
      (fun x hx => ih x hx)
      (fun p lab S _ => norec_prunable_one_msg
        (SessionType.NoRec.externalChoice hall) p lab S)

-- `Monitorable` toolkit (mirrors `Nest.SessionAdequacy`; `private` to
-- avoid clashes since this module joins the build root).
/-- No prune steps leave `tEnd`. -/
private theorem norec_PruneStep_not_from_tEnd {U : SessionType} :
    ¬ Drainability.PruneStep SessionType.tEnd U := by
  intro h
  cases h

/-- No prune steps leave an open variable. -/
private theorem norec_PruneStep_not_from_tVar (X : String) {U : SessionType} :
    ¬ Drainability.PruneStep (SessionType.tVar X) U := by
  intro h
  cases h

/-- Prune reachability from a stuck type is trivial (reflexivity only). -/
private theorem norec_PruneStep_eq_of_rtc_stuck {T : SessionType}
    (hstuck : ∀ U, ¬ Drainability.PruneStep T U) {V : SessionType}
    (h : Relation.ReflTransGen Drainability.PruneStep T V) : V = T := by
  induction h with
  | refl => rfl
  | @tail a b hRTC hStep ih =>
    subst ih
    exact absurd hStep (hstuck _)

/-- `tEnd` is monitorable (empty prune closure). -/
private theorem norec_Monitorable_tEnd :
    Drainability.Monitorable SessionType.tEnd := by
  have heq : {U : SessionType |
      Relation.ReflTransGen Drainability.PruneStep SessionType.tEnd U}
      = {SessionType.tEnd} := by
    apply Set.Subset.antisymm
    · intro U hU
      exact Set.mem_singleton_iff.mpr
        (norec_PruneStep_eq_of_rtc_stuck (fun _ => norec_PruneStep_not_from_tEnd) hU)
    · intro U hU
      rw [Set.mem_singleton_iff] at hU
      subst hU
      exact Relation.ReflTransGen.refl
  unfold Drainability.Monitorable
  rw [heq]
  exact Set.finite_singleton _

/-- Open variables are monitorable (singleton prune closure). -/
private theorem norec_Monitorable_tvar (X : String) :
    Drainability.Monitorable (SessionType.tVar X) := by
  have heq : {U : SessionType |
      Relation.ReflTransGen Drainability.PruneStep (SessionType.tVar X) U}
      = {SessionType.tVar X} := by
    apply Set.Subset.antisymm
    · intro U hU
      exact Set.mem_singleton_iff.mpr
        (norec_PruneStep_eq_of_rtc_stuck (fun _ => norec_PruneStep_not_from_tVar X) hU)
    · intro U hU
      rw [Set.mem_singleton_iff] at hU
      subst hU
      exact Relation.ReflTransGen.refl
  unfold Drainability.Monitorable
  rw [heq]
  exact Set.finite_singleton _

/-- Branch membership fact for the witness list. -/
private theorem norec_Monitorable_intC_of_branches
    {branches : List (Role × Lab × DataSort × SessionType)}
    (hall : ∀ x ∈ branches, Drainability.Monitorable x.2.2.2) :
    Drainability.Monitorable (SessionType.internalChoice branches) := by
  have hsub : {U : SessionType | Relation.ReflTransGen Drainability.PruneStep
      (SessionType.internalChoice branches) U} ⊆
      {SessionType.internalChoice branches} ∪
        ⋃ x ∈ (↑branches.toFinset : Set (Role × Lab × DataSort × SessionType)),
          {U : SessionType | Relation.ReflTransGen Drainability.PruneStep x.2.2.2 U} := by
    intro U hU
    rcases Drainability.PruneStep.head_intC_inv hU with rfl | ⟨x, hmem, hRTC⟩
    · exact Set.mem_union_left _ rfl
    · apply Set.mem_union_right
      apply Set.mem_biUnion (List.mem_toFinset.mpr hmem) hRTC
  apply Set.Finite.subset _ hsub
  refine Set.Finite.union (Set.finite_singleton _) ?_
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun x hx => ?_)
  exact hall x (List.mem_toFinset.mp hx)

/-- Branch membership fact for the witness list. -/
private theorem norec_Monitorable_extC_of_branches {p : Role}
    {branches : List (Lab × DataSort × SessionType)}
    (hall : ∀ x ∈ branches, Drainability.Monitorable x.2.2) :
    Drainability.Monitorable (SessionType.externalChoice p branches) := by
  have hsub : {U : SessionType | Relation.ReflTransGen Drainability.PruneStep
      (SessionType.externalChoice p branches) U} ⊆
      {SessionType.externalChoice p branches} ∪
        ⋃ x ∈ (↑branches.toFinset : Set (Lab × DataSort × SessionType)),
          {U : SessionType | Relation.ReflTransGen Drainability.PruneStep x.2.2 U} := by
    intro U hU
    rcases Drainability.PruneStep.head_extC_inv hU with rfl | ⟨x, hmem, hRTC⟩
    · exact Set.mem_union_left _ rfl
    · apply Set.mem_union_right
      apply Set.mem_biUnion (List.mem_toFinset.mpr hmem) hRTC
  apply Set.Finite.subset _ hsub
  refine Set.Finite.union (Set.finite_singleton _) ?_
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun x hx => ?_)
  exact hall x (List.mem_toFinset.mp hx)

/-- Every recursion-free type is monitorable (finite prune closure). -/
theorem norec_monitorable {T : SessionType} (hNR : T.NoRec) :
    Drainability.Monitorable T := by
  induction hNR
  next => exact norec_Monitorable_tEnd
  next X => exact norec_Monitorable_tvar X
  next hall ih => exact norec_Monitorable_intC_of_branches (fun x hx => ih x hx)
  next hall ih => exact norec_Monitorable_extC_of_branches (fun x hx => ih x hx)

-- Generic bespoke-closure driver: a prune-closed finite set containing `T`
-- makes `T` monitorable. Per-type work is just the state list plus one
-- step-case per state below.
/-- A prune-closed finite set containing `T` makes `T` monitorable. -/
theorem Monitorable_of_closed_set (T : SessionType) (S : Finset SessionType) :
    T ∈ S → (∀ U ∈ S, ∀ V, Drainability.PruneStep U V → V ∈ S) →
    Drainability.Monitorable T := by
  intro hmem hclosed
  have key : ∀ {U : SessionType},
      Relation.ReflTransGen Drainability.PruneStep T U → U ∈ S := by
    intro U hU
    induction hU with
    | refl => exact hmem
    | tail hRTC hStep ih => exact hclosed _ ih _ hStep
  have hsub : {U : SessionType | Relation.ReflTransGen Drainability.PruneStep T U} ⊆ ↑S := by
    intro U hU
    exact Finset.mem_coe.mpr (key hU)
  exact Set.Finite.subset (Finset.finite_toSet S) hsub
