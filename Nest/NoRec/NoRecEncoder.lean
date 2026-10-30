import Nest.NoRec.VacuousRec
import Nest.NoRec.NoRecUtils

/-!
# NoRecEncoder: NoRec balancedness, adequacy, and encoder lemmas.

IsBalancedW, the fuelled `pruneFirstInputDeep` fold, `PruneAdequate` adequacy under
vacuous recursion, and the NoRec encoder lemmas (`monitor_fold_aux_out_aux_norec`).
-/

/-!
# NoRec bridge + adequacy + encoder cluster.

Only `Nest.NoRec` uses these.
-/

/-!
# Weak balancedness.

Only `Nest.NoRec` uses these; `NoRec` implies
`IsBalancedW` via `SessionType.IsBalancedW_of_NoRec` below.
-/

/-- Weakened balancedness (recursion-variable uniformity): every recursive
    subterm `tRec X B` has uniform `X`-paths — all `LeadsTo X B` paths involve
    the same participants. It constrains only paths ending at the
    recursion variable itself, so `X`-free branches (`tEnd`, other variables)
    never break it. Since substitution for `X` eliminates free `X`-leaves,
    `X`-paths do not graft: under closedness this is preserved by substitution
    and hence by unfolding (see `SessionType.IsBalancedW_subst`). -/
inductive SessionType.IsBalancedW : SessionType → Prop where
  | end : IsBalancedW SessionType.tEnd
  | tvar (X : String) : IsBalancedW (SessionType.tVar X)
  | internalChoice {branches : List (Role × Lab × DataSort × SessionType)}
      (h_branches : ∀ (x : Role × Lab × DataSort × SessionType),
        x ∈ branches → IsBalancedW x.2.2.2) :
    IsBalancedW (SessionType.internalChoice branches)
  | externalChoice {r : Role} {branches : List (Lab × DataSort × SessionType)}
      (h_branches : ∀ (x : Lab × DataSort × SessionType),
        x ∈ branches → IsBalancedW x.2.2) :
    IsBalancedW (SessionType.externalChoice r branches)
  | trec {X : String} {B : SessionType} (hB : IsBalancedW B)
      (hbal : ∀ (S1 S2 : List Role), SessionType.LeadsTo X B S1 →
        SessionType.LeadsTo X B S2 → SessionType.SameParticipants S1 S2) :
    IsBalancedW (SessionType.tRec X B)

/-- Weakened balancedness is preserved by substitution with closed `R`
    (LeadsTo-paths to the bound variable never graft, via `inv_of_closed`). -/
theorem SessionType.IsBalancedW_subst {B R : SessionType} {X0 : String}
    (hB : B.IsBalancedW) (hR : R.IsBalancedW) (hRCl : R.IsClosed) :
    (substSessionType B X0 R).IsBalancedW := by
  induction hB
  · simp [substSessionType]
    exact SessionType.IsBalancedW.end
  · rename_i Y
    by_cases hXY : X0 = Y
    · subst hXY
      simp [substSessionType]
      exact hR
    · simp [substSessionType, hXY]
      exact SessionType.IsBalancedW.tvar _
  · rename_i branches h_branches ih
    simp only [substSessionType]
    apply SessionType.IsBalancedW.internalChoice
    intro x hx
    rw [go_int_eq_map] at hx
    obtain ⟨y, hy, hEq⟩ := List.mem_map.mp hx
    rcases y with ⟨p0, lab0, S0, T0⟩
    simp at hEq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq
    exact ih _ hy
  · rename_i r branches h_branches ih
    simp only [substSessionType]
    apply SessionType.IsBalancedW.externalChoice
    intro x hx
    rw [go_ext_eq_map] at hx
    obtain ⟨y, hy, hEq⟩ := List.mem_map.mp hx
    rcases y with ⟨lab0, S0, T0⟩
    simp at hEq
    obtain ⟨rfl, rfl, rfl⟩ := hEq
    exact ih _ hy
  · rename_i Y0 B0 hB0 hbal ih
    by_cases hXY : X0 = Y0
    · simp [substSessionType, hXY]
      exact SessionType.IsBalancedW.trec hB0 hbal
    · simp [substSessionType, hXY]
      apply SessionType.IsBalancedW.trec ih
      intro S1 S2 h1 h2
      have hneY : Y0 ≠ X0 := Ne.symm hXY
      have h1' := SessionType.LeadsTo_subst_inv_of_closed B0 hRCl hneY h1
      have h2' := SessionType.LeadsTo_subst_inv_of_closed B0 hRCl hneY h2
      exact hbal S1 S2 h1' h2'

/-- Deep prune of the first input `msg = (p, lab, S)` from a well-formed
    session type `T`: defined (as `some T'`) iff some `externalChoice p`
    offering the `(lab, S)` branch is reachable while every traversed
    `internalChoice` avoids `p`-senders; in that case every such reachable
    `externalChoice p` is replaced by its `(lab, S)` continuation, and
    branches that reach no such `externalChoice p` are removed. `fuel` bounds
    recursion unfoldings (see `pruneFirstInputDeepGo`). -/
def pruneFirstInputDeep (T : SessionType) (msg : QueueMessage) (fuel : Nat) :
    Option SessionType :=
  match msg with
  | QueueMessage.msg p lab S =>
    if pruneFirstInputDeepHas p lab S T then
      some (pruneFirstInputDeepGo p lab S fuel T)
    else none

/-- A network is balanced when every entry's session type is weakly balanced
    (`SessionType.IsBalancedW`): recursion-variable uniformity per binder,
    preserved by substitution and unfolding on closed types. Replaces
    `Network.NoRec` as the threading hypothesis for the monitor/prune
    correspondence (`mon_yes_iff_prune_deep` needs no `NoRec`). -/
def Network.IsBalancedW (N : Network) : Prop :=
  ∀ (x : Role × SessionTypeWithQueue), x ∈ N → x.2.1.IsBalancedW

/-- Balancedness of an internal-choice branch target. -/
lemma SessionType.IsBalancedW.of_internalChoice
    {branches : List (Role × Lab × DataSort × SessionType)}
    (h : IsBalancedW (SessionType.internalChoice branches))
    {x : Role × Lab × DataSort × SessionType} (hmem : x ∈ branches) :
    IsBalancedW x.2.2.2 := by
  cases h with
  | internalChoice h_branches => exact h_branches x hmem

/-- Balancedness of an external-choice branch target. -/
lemma SessionType.IsBalancedW.of_externalChoice
    {p : Role} {branches : List (Lab × DataSort × SessionType)}
    (h : IsBalancedW (SessionType.externalChoice p branches))
    {x : Lab × DataSort × SessionType} (hmem : x ∈ branches) :
    IsBalancedW x.2.2 := by
  cases h with
  | externalChoice h_branches => exact h_branches x hmem

/-- Balancedness of a `tRec` body. -/
lemma SessionType.IsBalancedW.of_tRecBody {X : String} {B : SessionType}
    (h : IsBalancedW (SessionType.tRec X B)) : IsBalancedW B := by
  cases h with
  | trec hB hbal => exact hB

/-- Recursion-free types are weakly balanced (no `tRec` subterm ever needs the
    uniformity condition). -/
lemma SessionType.IsBalancedW_of_NoRec {T : SessionType} (hNR : T.NoRec) :
    T.IsBalancedW := by
  induction hNR
  · exact SessionType.IsBalancedW.end
  · exact SessionType.IsBalancedW.tvar _
  · rename_i h_branches ih
    exact SessionType.IsBalancedW.internalChoice (fun x hx => ih x hx)
  · rename_i h_branches ih
    exact SessionType.IsBalancedW.externalChoice (fun x hx => ih x hx)

/-- Vacuous-recursion types are weakly balanced (a vacuous binder admits no
    `LeadsTo` path to its variable, so uniformity holds vacuously). Used to
    discharge balancedness at `VacuousRec` call sites from `hVac` alone. -/
lemma SessionType.IsBalancedW.of_vacuous {T : SessionType} (hVac : T.VacuousRec) :
    T.IsBalancedW := by
  induction hVac
  · exact SessionType.IsBalancedW.end
  · exact SessionType.IsBalancedW.tvar _
  · rename_i h_branches ih
    exact SessionType.IsBalancedW.internalChoice (fun x hx => ih x hx)
  · rename_i h_branches ih
    exact SessionType.IsBalancedW.externalChoice (fun x hx => ih x hx)
  · rename_i hfree _ ih
    exact SessionType.IsBalancedW.trec ih
      (fun S1 S2 h1 _ => absurd (SessionType.LeadsTo_fv h1) hfree)

/-- Unfolding is impossible at `NoRec` heads (unfolds start at `tRec`,
    which `NoRec` excludes). Closes `Unfold1` cases in `NoRec`-scoped
    proofs in one line. -/
theorem Unfold1.absurd_of_NoRec {T U : SessionType} (hNR : T.NoRec)
    (h : Unfold1 T U) : False := by
  cases h with
  | tRec => cases hNR






/-- Branch-target counts fit in the choice sum. -/
private theorem count_mem_le_go_int
    {l : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType} (hmem : x ∈ l) :
    x.2.2.2.tRecCount ≤ SessionType.tRecCount.goInt l := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨q0, l0, s0, T0⟩
    simp only [SessionType.tRecCount.goInt] at ⊢
    simp at hmem
    rcases hmem with rfl | hmem
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)

/-- Branch-target counts fit in the choice sum. -/
private theorem count_mem_le_go_ext
    {l : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType} (hmem : x ∈ l) :
    x.2.2.tRecCount ≤ SessionType.tRecCount.goExt l := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨l0, s0, T0⟩
    simp only [SessionType.tRecCount.goExt] at ⊢
    simp at hmem
    rcases hmem with rfl | hmem
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_add_left _ _)

/-- Vacuous-everywhere + `Has`-everywhere types admit static-fuel adequacy:
    each unfolding deletes its binder (`subst_noop`), so `tRec`-count fuel
    suffices; branch targets use monotonicity. By size induction. -/
theorem PruneAdequate.of_vacuous_everywhere (p : Role) (lab : Lab)
    (S : DataSort) {T : SessionType} (hWF : T.WellFormed)
    (hVac : T.VacuousRec) :
    PruneAdequate p lab S (SessionType.tRecCount T) T := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop := fun U => U.WellFormed →
    U.VacuousRec →
    PruneAdequate p lab S (SessionType.tRecCount U) U
  have hC : ∀ U, C U := by
    intro U
    refine hwf.induction (α := SessionType) (C := C) (a := U) ?step
    intro U ih hWF hVac
    cases U with
    | tEnd => exact PruneAdequate.tEnd _
    | tVar X => exact PruneAdequate.tvar _ X
    | internalChoice branches =>
      apply PruneAdequate.intC
      intro x hx
      rcases x with ⟨q0, l0, s0, T0⟩
      have hlt : sizeOf T0 < sizeOf (SessionType.internalChoice branches) :=
        sizeOf_SessionType_lt_sizeOf_internalChoice hx
      obtain ⟨hND, hCl, hCo⟩ := hWF
      have hWFT0 : T0.WellFormed :=
        ⟨noDupl_of_mem_intBranches hND hx,
          isClosed_of_mem_intBranches hCl hx,
          isContractive_of_mem_intBranches hCo hx⟩
      have hVacT0 : T0.VacuousRec := by
        cases hVac with
        | internalChoice hall => exact hall _ hx
      have h1 := ih T0 hlt hWFT0 hVacT0
      have hcount : T0.tRecCount ≤
          (SessionType.internalChoice branches).tRecCount := by
        simp only [SessionType.tRecCount]
        exact count_mem_le_go_int hx
      exact PruneAdequate.mono hcount h1
    | externalChoice q branches =>
      apply PruneAdequate.extC
      intro x hx
      rcases x with ⟨l0, s0, T0⟩
      have hlt : sizeOf T0 < sizeOf (SessionType.externalChoice q branches) :=
        sizeOf_SessionType_lt_sizeOf_externalChoice (p := q) hx
      obtain ⟨hND, hCl, hCo⟩ := hWF
      have hWFT0 : T0.WellFormed :=
        ⟨noDupl_of_mem_extBranches hND hx,
          isClosed_of_mem_extBranches hCl hx,
          isContractive_of_mem_extBranches hCo hx⟩
      have hVacT0 : T0.VacuousRec := by
        cases hVac with
        | externalChoice hall => exact hall _ hx
      have h1 := ih T0 hlt hWFT0 hVacT0
      have hcount : T0.tRecCount ≤
          (SessionType.externalChoice q branches).tRecCount := by
        simp only [SessionType.tRecCount]
        exact count_mem_le_go_ext hx
      exact PruneAdequate.mono hcount h1
    | tRec Y B =>
      cases hVac with
      | trec hfree hVacB =>
        have hNDB : B.NoDupl := by cases hWF.1 with | tRec h => exact h
        have hCoB : B.Contractive := by
          cases hWF.2.2 with | tRec hCo0 hG0 => exact hCo0
        have hClB : B.IsClosed :=
          closed_of_trec_closed_vacuous hfree hWF.2.1
        have hltB : sizeOf B < sizeOf (SessionType.tRec Y B) := by simp
        have hB := ih B hltB ⟨hNDB, hClB, hCoB⟩ hVacB
        exact PruneAdequate.trec_vac hfree hB
  exact hC T hWF hVac

/-- Maximal determinism for recursion-free types (NoRec-side corollary of
    `mon_tr_yes_target_unique` above, kept for the NoRec workstream):
    without `tRec`, unfold cases prune and every
    branch target is strictly smaller, so well-founded size induction closes
    using keys-half (`nodup_sublist_eq_of_mem_iff`) + branch determinism. -/
lemma mon_tr_yes_target_unique_norec {M T1 T2 : SessionType} {γ : ext_tag}
    (hNR : M.NoRec) (hND : M.NoDupl)
    (h1 : mon_tr_yes M γ T1) (h2 : mon_tr_yes M γ T2) : T1 = T2 := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop := fun M => ∀ (T1 T2 : SessionType) (γ : ext_tag),
    M.NoRec → M.NoDupl → mon_tr_yes M γ T1 → mon_tr_yes M γ T2 → T1 = T2
  have hC : ∀ M, C M := by
    intro M
    refine hwf.induction (α := SessionType) (C := C) (a := M) ?step
    intro M ih T1 T2 γ hNR hND h1 h2
    rcases h1 with ⟨hE1, hM1⟩
    rcases h2 with ⟨hE2, hM2⟩
    cases M with
    | tEnd =>
      cases hM1 with
      | @base _ _ _ hb => cases hb
    | tVar X =>
      cases hM1 with
      | @base _ _ _ hb => cases hb
    | tRec X B =>
      cases hNR
    | internalChoice branches =>
      cases hM1 with
      | @base _ _ _ hb =>
        cases hb with
        | intC huniq hmemB1 =>
          cases hM2 with
          | @base _ _ _ hb2 =>
            cases hb2 with
            | intC huniq2 hmemB2 =>
              exact unique_target_of_nodup_int huniq hmemB1 hmemB2
      | @pfxInt branches kept1 q labq Sq X hne1 hno1 hkept1 hall1 hNK1 hkey1 hallMax1 hcover1 horder1 =>
        cases hM2 with
        | @base _ _ _ hb2 => cases hb2
        | @pfxInt branches kept2 q labq Sq X hne2 hno2 hkept2 hall2 hNK2 hkey2 hallMax2 hcover2 horder2 =>
          have hNDt : List.Nodup (branches.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) :=
            SessionType.NoDupl.triple_nodup_of_internalChoice hND
          have hNRb : ∀ (x : Role × Lab × DataSort × SessionType),
              x ∈ branches → x.2.2.2.NoRec := by
            cases hNR with
            | internalChoice h => exact h
          have hNKt1 : List.Nodup (kept1.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) :=
            nodup_triple_of_nodup_pair hNK1
          have hNKt2 : List.Nodup (kept2.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) :=
            nodup_triple_of_nodup_pair hNK2
          have hsetEq : ∀ k, k ∈ kept1.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) ↔
              k ∈ kept2.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) := by
            intro k
            rcases k with ⟨r, l, s⟩
            constructor
            · intro hmemK1
              rcases List.mem_map.mp hmemK1 with ⟨x, hxK1, hkeyEq1⟩
              rcases x with ⟨r', l', s', T1'⟩
              have hkk : (r', l', s') = (r, l, s) := hkeyEq1
              obtain ⟨rfl, rfl, rfl⟩ := hkk
              obtain ⟨T0a, hmemB⟩ := hkey1 r l s T1' hxK1
              have hsubE1 := hall1 T0a T1' r l s hmemB hxK1
              rcases hcover2 r l s T0a hmemB ⟨T1', hsubE1⟩ with ⟨T2', hmemK2⟩
              exact List.mem_map.mpr ⟨(r, l, s, T2'), hmemK2, rfl⟩
            · intro hmemK2
              rcases List.mem_map.mp hmemK2 with ⟨x, hxK2, hkeyEq2⟩
              rcases x with ⟨r', l', s', T2'⟩
              have hkk : (r', l', s') = (r, l, s) := hkeyEq2
              obtain ⟨rfl, rfl, rfl⟩ := hkk
              obtain ⟨T0a, hmemB⟩ := hkey2 r l s T2' hxK2
              have hsubE2 := hall2 T0a T2' r l s hmemB hxK2
              rcases hcover1 r l s T0a hmemB ⟨T2', hsubE2⟩ with ⟨T1', hmemK1⟩
              exact List.mem_map.mpr ⟨(r, l, s, T1'), hmemK1, rfl⟩
          have hKeyEq : kept1.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) =
              kept2.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) :=
            nodup_sublist_eq_of_mem_iff hNDt horder1 horder2 hNKt1 hNKt2 hsetEq
          have hlen : kept1.length = kept2.length := by
            have h := congrArg List.length hKeyEq
            simpa [List.length_map] using h
          have hkeptEq : kept1 = kept2 := by
            apply List.ext_getElem hlen
            intro i h1 h2
            match hqe1 : kept1[i]'h1, hqe2 : kept2[i]'h2 with
            | (r, l, s, T1i), (r2, l2, s2, T2i) =>
              have hki1 : i < (kept1.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))).length := by
                rw [List.length_map]; exact h1
              have hki2 : i < (kept2.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))).length := by
                rw [List.length_map]; exact h2
              have hmap : (kept1.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))[i]'hki1 =
                  (kept2.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))[i]'hki2 := by
                simp [hKeyEq]
              have e1 : (kept1.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))[i]'hki1 = (r, l, s) := by
                simp [List.getElem_map, hqe1]
              have e2 : (kept2.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))[i]'hki2 = (r2, l2, s2) := by
                simp [List.getElem_map, hqe2]
              have hkk : (r, l, s) = (r2, l2, s2) := by
                rw [← e1, ← e2]; exact hmap
              obtain ⟨rfl, rfl, rfl⟩ := hkk
              have hmemK1 : (r, l, s, T1i) ∈ kept1 := hqe1 ▸ List.getElem_mem h1
              have hmemK2 : (r, l, s, T2i) ∈ kept2 := hqe2 ▸ List.getElem_mem h2
              obtain ⟨T0a, hmemB⟩ := hkey1 r l s T1i hmemK1
              have hsubE1 := hall1 T0a T1i r l s hmemB hmemK1
              have hsubM1 := hallMax1 T0a T1i r l s hmemB hmemK1 hsubE1
              have hsubE2 := hall2 T0a T2i r l s hmemB hmemK2
              have hsubM2 := hallMax2 T0a T2i r l s hmemB hmemK2 hsubE2
              have hlt : sizeOf T0a < sizeOf (SessionType.internalChoice branches) :=
                sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
              have hNR0 : T0a.NoRec := hNRb _ hmemB
              have hND0 : T0a.NoDupl := noDupl_of_mem_intBranches hND hmemB
              have hTgt : T1i = T2i :=
                ih T0a hlt T1i T2i (ext_tag.recv q labq Sq) hNR0 hND0 ⟨hsubE1, hsubM1⟩ ⟨hsubE2, hsubM2⟩
              -- Goal was already substituted to tuples by `match`; close by congruence.
              exact congrArg (fun T => (r, l, s, T)) hTgt
          rw [hkept1, hkept2, hkeptEq]
    | externalChoice p branches =>
      cases hM1 with
      | @base _ _ _ hb =>
        cases hb with
        | extC huniq hmemB1 =>
          cases hM2 with
          | @base _ _ _ hb2 =>
            cases hb2 with
            | extC huniq2 hmemB2 =>
              have hNDc := hND
              cases hNDc with
              | externalChoice hnl _ _ =>
                exact unique_target_of_nodup_ext (nodup_of_nodup_labels hnl) hmemB1 hmemB2
          | @pfxExt _ _ _ _ _ _ _ _ hneq2 _ _ _ _ _ _ _ =>
            exact absurd rfl hneq2
      | @pfxExt p branches kept1 q lab S X hne1 hneq1 hkept1 hall1 hNK1 hkey1 hallMax1 hcover1 horder1 =>
        cases hM2 with
        | @base _ _ _ hb2 =>
          cases hb2 with
          | extC huniq hmem =>
            exact absurd rfl hneq1
        | @pfxExt p branches kept2 q lab S X hne2 hneq2 hkept2 hall2 hNK2 hkey2 hallMax2 hcover2 horder2 =>
          have hNDc := hND
          have hNDpair : List.Nodup (branches.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) := by
            cases hNDc with
            | externalChoice hnl _ _ => exact nodup_of_nodup_labels hnl
          have hNRb : ∀ (x : Lab × DataSort × SessionType),
              x ∈ branches → x.2.2.NoRec := by
            cases hNR with
            | externalChoice h => exact h
          have hNKp1 : List.Nodup (kept1.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) :=
            nodup_of_nodup_labels hNK1
          have hNKp2 : List.Nodup (kept2.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) :=
            nodup_of_nodup_labels hNK2
          have hsetEq : ∀ k, k ∈ kept1.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) ↔
              k ∈ kept2.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) := by
            intro k
            rcases k with ⟨l, s⟩
            constructor
            · intro hmemK1
              rcases List.mem_map.mp hmemK1 with ⟨x, hxK1, hkeyEq1⟩
              rcases x with ⟨l', s', T1'⟩
              have hkk : (l', s') = (l, s) := hkeyEq1
              obtain ⟨rfl, rfl⟩ := hkk
              obtain ⟨T0a, hmemB⟩ := hkey1 l s T1' hxK1
              have hsubE1 := hall1 T0a T1' l s hmemB hxK1
              rcases hcover2 l s T0a hmemB ⟨T1', hsubE1⟩ with ⟨T2', hmemK2⟩
              exact List.mem_map.mpr ⟨(l, s, T2'), hmemK2, rfl⟩
            · intro hmemK2
              rcases List.mem_map.mp hmemK2 with ⟨x, hxK2, hkeyEq2⟩
              rcases x with ⟨l', s', T2'⟩
              have hkk : (l', s') = (l, s) := hkeyEq2
              obtain ⟨rfl, rfl⟩ := hkk
              obtain ⟨T0a, hmemB⟩ := hkey2 l s T2' hxK2
              have hsubE2 := hall2 T0a T2' l s hmemB hxK2
              rcases hcover1 l s T0a hmemB ⟨T2', hsubE2⟩ with ⟨T1', hmemK1⟩
              exact List.mem_map.mpr ⟨(l, s, T1'), hmemK1, rfl⟩
          have hKeyEq : kept1.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) =
              kept2.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) :=
            nodup_sublist_eq_of_mem_iff hNDpair horder1 horder2 hNKp1 hNKp2 hsetEq
          have hlen : kept1.length = kept2.length := by
            have h := congrArg List.length hKeyEq
            simpa [List.length_map] using h
          have hkeptEq : kept1 = kept2 := by
            apply List.ext_getElem hlen
            intro i h1 h2
            match hqe1 : kept1[i]'h1, hqe2 : kept2[i]'h2 with
            | (l, s, T1i), (l2, s2, T2i) =>
              have hki1 : i < (kept1.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))).length := by
                rw [List.length_map]; exact h1
              have hki2 : i < (kept2.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))).length := by
                rw [List.length_map]; exact h2
              have hmap : (kept1.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))[i]'hki1 =
                  (kept2.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))[i]'hki2 := by
                simp [hKeyEq]
              have e1 : (kept1.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))[i]'hki1 = (l, s) := by
                simp [List.getElem_map, hqe1]
              have e2 : (kept2.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))[i]'hki2 = (l2, s2) := by
                simp [List.getElem_map, hqe2]
              have hkk : (l, s) = (l2, s2) := by
                rw [← e1, ← e2]; exact hmap
              obtain ⟨rfl, rfl⟩ := hkk
              have hmemK1 : (l, s, T1i) ∈ kept1 := hqe1 ▸ List.getElem_mem h1
              have hmemK2 : (l, s, T2i) ∈ kept2 := hqe2 ▸ List.getElem_mem h2
              obtain ⟨T0a, hmemB⟩ := hkey1 l s T1i hmemK1
              have hsubE1 := hall1 T0a T1i l s hmemB hmemK1
              have hsubE2 := hall2 T0a T2i l s hmemB hmemK2
              have hsubM1 := hallMax1 T0a T1i l s hmemB hmemK1 hsubE1
              have hsubM2 := hallMax2 T0a T2i l s hmemB hmemK2 hsubE2
              have hlt : sizeOf T0a < sizeOf (SessionType.externalChoice p branches) :=
                sizeOf_SessionType_lt_sizeOf_externalChoice hmemB
              have hNR0 : T0a.NoRec := hNRb _ hmemB
              have hND0 : T0a.NoDupl := noDupl_of_mem_extBranches hND hmemB
              have hTgt : T1i = T2i :=
                ih T0a hlt T1i T2i (ext_tag.recv q lab S) hNR0 hND0 ⟨hsubE1, hsubM1⟩ ⟨hsubE2, hsubM2⟩
              exact congrArg (fun T => (l, s, T)) hTgt
          rw [hkept1, hkept2, hkeptEq]
  exact hC _ _ _ _ hNR hND h1 h2

/-- Maximal yes-derivations preserve `NoRec` and `NoDupl`: targets of recursion-free, duplicate-free
   sources stay recursion-free and duplicate-free. -/
lemma mon_tr_yes_preserves_norec_no_dupl {M T1 : SessionType} {γ : ext_tag}
    (hNR : M.NoRec) (hND : M.NoDupl) (h1 : mon_tr_yes M γ T1) :
    T1.NoRec ∧ T1.NoDupl := by
  have hwf : WellFounded (fun x y : SessionType => sizeOf x < sizeOf y) :=
    (measure fun x : SessionType => sizeOf x).wf
  let C : SessionType → Prop := fun M => M.NoRec → M.NoDupl →
    ∀ (T1 : SessionType) (γ : ext_tag) (hE1 : mon_tr_yes_exist M γ T1)
    (hM1 : mon_tr_yes_max_deriv hE1), T1.NoRec ∧ T1.NoDupl
  have hC : ∀ M, C M := by
    intro M
    refine hwf.induction (α := SessionType) (C := C) (a := M) ?step
    intro M ih hNR hND T1 γ hE1 hM1
    cases M with
    | tEnd =>
      cases hM1 with
      | @base _ _ _ hb => cases hb
    | tVar X =>
      cases hM1 with
      | @base _ _ _ hb => cases hb
    | tRec X B => cases hNR
    | internalChoice branches =>
      cases hM1 with
      | @base _ _ _ hb =>
        cases hb with
        | intC huniq hmem =>
          exact ⟨noRec_of_mem_intBranches hNR hmem,
            noDupl_of_mem_intBranches hND hmem⟩
      | @pfxInt branches kept q lab S X hne hno hkept hall hNK hkey hallMax hcover horder =>
        rw [hkept]
        constructor
        · apply SessionType.NoRec.internalChoice
          intro x hx
          rcases x with ⟨r, l, s, T1'⟩
          obtain ⟨T0a, hmemB⟩ := hkey r l s T1' hx
          have hsubE := hall T0a T1' r l s hmemB hx
          have hsubM := hallMax T0a T1' r l s hmemB hx hsubE
          have hlt : sizeOf T0a < sizeOf (SessionType.internalChoice branches) :=
            sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
          have hNR0 : T0a.NoRec := noRec_of_mem_intBranches hNR hmemB
          have hND0 : T0a.NoDupl := noDupl_of_mem_intBranches hND hmemB
          exact (ih T0a hlt hNR0 hND0 T1' (ext_tag.recv q lab S) hsubE hsubM).1
        · apply SessionType.NoDupl.internalChoice hNK hne.2
          intro x hx
          rcases x with ⟨r, l, s, T1'⟩
          obtain ⟨T0a, hmemB⟩ := hkey r l s T1' hx
          have hsubE := hall T0a T1' r l s hmemB hx
          have hsubM := hallMax T0a T1' r l s hmemB hx hsubE
          have hlt : sizeOf T0a < sizeOf (SessionType.internalChoice branches) :=
            sizeOf_SessionType_lt_sizeOf_internalChoice hmemB
          have hNR0 : T0a.NoRec := noRec_of_mem_intBranches hNR hmemB
          have hND0 : T0a.NoDupl := noDupl_of_mem_intBranches hND hmemB
          exact (ih T0a hlt hNR0 hND0 T1' (ext_tag.recv q lab S) hsubE hsubM).2
    | externalChoice p branches =>
      cases hM1 with
      | @base _ _ _ hb =>
        cases hb with
        | extC huniq hmem =>
          exact ⟨noRec_of_mem_extBranches hNR hmem,
            noDupl_of_mem_extBranches hND hmem⟩
      | @pfxExt p branches kept q lab S X hne hneq hkept hall hNK hkey hallMax hcover horder =>
        rw [hkept]
        constructor
        · apply SessionType.NoRec.externalChoice
          intro x hx
          rcases x with ⟨l, s, T1'⟩
          obtain ⟨T0a, hmemB⟩ := hkey l s T1' hx
          have hsubE := hall T0a T1' l s hmemB hx
          have hsubM := hallMax T0a T1' l s hmemB hx hsubE
          have hlt : sizeOf T0a < sizeOf (SessionType.externalChoice p branches) :=
            sizeOf_SessionType_lt_sizeOf_externalChoice hmemB
          have hNR0 : T0a.NoRec := noRec_of_mem_extBranches hNR hmemB
          have hND0 : T0a.NoDupl := noDupl_of_mem_extBranches hND hmemB
          exact (ih T0a hlt hNR0 hND0 T1' (ext_tag.recv q lab S) hsubE hsubM).1
        · apply SessionType.NoDupl.externalChoice hNK hne.2
          intro x hx
          rcases x with ⟨l, s, T1'⟩
          obtain ⟨T0a, hmemB⟩ := hkey l s T1' hx
          have hsubE := hall T0a T1' l s hmemB hx
          have hsubM := hallMax T0a T1' l s hmemB hx hsubE
          have hlt : sizeOf T0a < sizeOf (SessionType.externalChoice p branches) :=
            sizeOf_SessionType_lt_sizeOf_externalChoice hmemB
          have hNR0 : T0a.NoRec := noRec_of_mem_extBranches hNR hmemB
          have hND0 : T0a.NoDupl := noDupl_of_mem_extBranches hND hmemB
          exact (ih T0a hlt hNR0 hND0 T1' (ext_tag.recv q lab S) hsubE hsubM).2
  rcases h1 with ⟨hE1, hM1⟩
  exact hC M hNR hND T1 γ hE1 hM1

/-- Output-liveness for a send step (type-level, `NoRec` version): the
    queue `Q` remains fully absorbable from the send-target `T'`. Without
    this, the send can prune the branches that absorb `Q`; with it (the
    analogue of `intPfx_diamond`'s `h_acc`), the send commutes past the
    absorption. Stated with an explicit acceptor (`∃ M', ...`) like `h_acc`. -/
lemma monitor_fold_aux_out_aux_norec {Q : Queue} {T T' M : SessionType}
    {p : Role} {lab : Lab} {S : DataSort}
    (hTNR : T.NoRec) (hTND : T.NoDupl)
    (hST : st_trans T (st_label.out p lab S) T')
    (hEnc : monitor_fold (T, Q) M)
    (hAcc : ∃ M', monitor_fold (T', Q) M') :
    ∃ M', monitor_fold (T', Q) M' ∧ mon_tr_yes M (ext_tag.send p lab S) M' := by
  revert T T' M hTNR hTND hST hEnc hAcc
  induction Q with
  | nil =>
    intro T T' M hTNR hTND hST hEnc hAcc
    -- Invert the send: `T = internalChoice branches`, `(p,lab,S,T') ∈ branches`.
    cases hST with
    | intC hmem =>
      rename_i branches
      simp only [monitor_fold, monitor_fold_aux] at hEnc
      subst hEnc
      obtain ⟨Macc, hAccWit⟩ := hAcc
      -- Base send from membership + triple nodup.
      have htriple : List.Nodup (List.map
          (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) branches) := by
        cases hTND with
        | internalChoice hnp _ _ => exact nodup_triple_of_nodup_pair hnp
      have hb : mon_tr_yes_base (SessionType.internalChoice branches)
          (ext_tag.send p lab S) T' := mon_tr_yes_base.intC htriple hmem
      have hMEq : Macc = T' := by simpa only [monitor_fold, monitor_fold_aux] using hAccWit
      refine ⟨Macc, hAccWit, ?_⟩
      rw [hMEq]
      exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩
    | tRec hsub =>
      cases hTNR
  | cons msg rest ih =>
    intro T T' M hTNR hTND hST hEnc hAcc
    rcases msg with ⟨q0, lab0, S0⟩
    simp only [monitor_fold, monitor_fold_aux] at hEnc
    obtain ⟨Tmid, hRecv, hRest⟩ := hEnc
    obtain ⟨Macc, hAccWit⟩ := hAcc
    simp only [monitor_fold, monitor_fold_aux] at hAccWit
    obtain ⟨TmidAcc, hRecvAcc, hRestAcc⟩ := hAccWit
    cases hST with
    | intC hmem =>
      rename_i branches
      -- Commute the send past the head receive (`intPfx_diamond` + Det).
      obtain ⟨X', hSTmid, hRecv'⟩ :=
        intPfx_diamond (st_trans.intC hmem) hRecv ⟨_, hRecvAcc.1⟩
      have hT'NR : T'.NoRec := noRec_of_mem_intBranches hTNR hmem
      have hT'ND : T'.NoDupl := noDupl_of_mem_intBranches hTND hmem
      have hXeq : X' = TmidAcc :=
        mon_tr_yes_target_unique_norec hT'NR hT'ND hRecv' hRecvAcc
      rw [hXeq] at hSTmid hRecv'
      have hpair := mon_tr_yes_preserves_norec_no_dupl hTNR hTND hRecv
      obtain ⟨M', hEnc', hSend⟩ :=
        ih hpair.1 hpair.2 hSTmid hRest ⟨_, hRestAcc⟩
      exact ⟨M', ⟨TmidAcc, hRecvAcc, hEnc'⟩, hSend⟩
    | tRec hsub =>
      cases hTNR
