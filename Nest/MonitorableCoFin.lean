import Nest.MonitorCo
import Nest.MonitorCoFun
import Nest.MonitorCoRel
import Nest.SemFoldCo
import Nest.FoldExistsCo

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-- Peel a computed-transition membership into an `observe` equation:
    `(g, W) ∈ mon_tr_yes_co_fun V` yields `observe V hW g = some W`.
    Fully general (no case analysis on `V`); per-monitor proofs use this
    once and then invert the resulting `fmon` derivation
    (`observe_sound`). -/
theorem mem_fun_observe {V : SessionType} (hW : V.WellFormed)
    {p : ext_tag × SessionType} (hp : p ∈ mon_tr_yes_co_fun V) :
    ∃ g W, FmonCompute.observe V hW g = some W ∧ p = (g, W) := by
  have hw : V.wfCheck [] = true := SessionType.wfCheck_complete hW
  rw [mon_tr_yes_co_fun, dite_eq_left hw] at hp
  rw [FmonCompute.outgoing, List.mem_filterMap] at hp
  obtain ⟨g, hgmem, hp⟩ := hp
  cases h : FmonCompute.observe V hW g with
  | none => simp [h] at hp
  | some W =>
    have hpW : (g, W) = p := by simpa [h] using hp
    exact ⟨g, W, h, hpW.symm⟩

/-- Mapped-nodup + all-mapped-equal forces length ≤ 1 (for pinning
    kept-lists to singletons). -/
theorem nodup_map_all_eq_length_le_one {α β : Type} {l : List α} {f : α → β} {k : β}
    (hnd : (l.map f).Nodup) (hall : ∀ y ∈ l.map f, y = k) : l.length ≤ 1 := by
  match l with
  | [] => simp
  | [x] => simp
  | x :: y :: rest =>
    have hx : f x = k := hall _ (by simp)
    have hy : f y = k := hall _ (by simp)
    have hnd' : f x ∉ List.map f (y :: rest) :=
      (List.nodup_cons.mp hnd).1
    have hmem : f y ∈ List.map f (y :: rest) := by simp
    rw [hx] at hnd'
    rw [hy] at hmem
    exact absurd hmem hnd'

/-- 1-branch external kept-pinning: membership + nodup + sublist forces
    `kept = [(k, T1)]`. -/
theorem kept_ext_singleton {kept : List (Lab × DataSort × SessionType)}
    {b : Lab × DataSort × SessionType} {T1 : SessionType}
    (hke : kept ≠ []) (hnd : (kept.map ext_key).Nodup)
    (hmem : (b.1, b.2.1, T1) ∈ kept)
    (hallk : ∀ x ∈ kept, (x.1, x.2.1) = (b.1, b.2.1)) :
    kept = [(b.1, b.2.1, T1)] := by
  have hkeys : ∀ y ∈ kept.map ext_key, y = b.1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hxx := hallk x hx
    have h1 := congrArg Prod.fst hxx
    show ext_key x = b.1
    exact h1
  have hlen : kept.length ≤ 1 := nodup_map_all_eq_length_le_one hnd hkeys
  match heq : kept with
  | [] => exact absurd rfl hke
  | [x] =>
    simp only [List.mem_singleton] at hmem
    obtain rfl := hmem
    rfl

/-- 1-branch internal kept-pinning. -/
theorem kept_int_singleton {kept : List (Role × Lab × DataSort × SessionType)}
    {b : Role × Lab × DataSort × SessionType} {T1 : SessionType}
    (hke : kept ≠ []) (hnd : (kept.map int_key).Nodup)
    (hmem : (b.1, b.2.1, b.2.2.1, T1) ∈ kept)
    (hallk : ∀ x ∈ kept, (x.1, x.2.1, x.2.2.1) = (b.1, b.2.1, b.2.2.1)) :
    kept = [(b.1, b.2.1, b.2.2.1, T1)] := by
  have hkeys : ∀ y ∈ kept.map int_key, y = (b.1, b.2.1) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨r, l, s, T⟩ := x
    have hxx := hallk _ hx
    simp only [] at hxx
    obtain ⟨rfl, rfl, rfl⟩ := hxx
    rfl
  have hlen : kept.length ≤ 1 := nodup_map_all_eq_length_le_one hnd hkeys
  match heq : kept with
  | [] => exact absurd rfl hke
  | [x] =>
    simp only [List.mem_singleton] at hmem
    obtain rfl := hmem
    rfl

/-- 2-branch external kept-pinning, both eligible (order-free disjunction:
    fixed-order conclusion would be false, swapped kept satisfies hyps). -/
theorem kept_ext_two_ee_disj {kept : List (Lab × DataSort × SessionType)}
    {b1 b2 : Lab × DataSort × SessionType} {T1 T2 : SessionType}
    (hke : kept ≠ []) (hnd : (kept.map ext_key).Nodup)
    (hmem1 : (b1.1, b1.2.1, T1) ∈ kept) (hmem2 : (b2.1, b2.2.1, T2) ∈ kept)
    (hallk : ∀ x ∈ kept, x.1 = b1.1 ∨ x.1 = b2.1)
    (hne12 : b1.1 ≠ b2.1) :
    kept = [(b1.1, b1.2.1, T1), (b2.1, b2.2.1, T2)] ∨
      kept = [(b2.1, b2.2.1, T2), (b1.1, b1.2.1, T1)] := by
  have hne : (b1.1, b1.2.1, T1) ≠ (b2.1, b2.2.1, T2) := by
    intro h
    apply hne12
    have := congrArg Prod.fst h
    simpa using this
  have hle : kept.length ≤ 2 := by
    match heq : kept with
    | [] => simp
    | [_] => simp
    | [_, _] => simp
    | x :: y :: z :: rest =>
      have hx := hallk x (by simp)
      have hy := hallk y (by simp)
      have hz := hallk z (by simp)
      simp only [List.map_cons] at hnd
      have hnx : ext_key x ∉ ext_key y :: ext_key z :: (rest.map ext_key) :=
        (List.nodup_cons.mp hnd).1
      have hny : ext_key y ∉ ext_key z :: (rest.map ext_key) :=
        (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        rcases hz with hz | hz
      · have e1 : ext_key x = ext_key y := by simp [ext_key, hx, hy]
        exact absurd (e1 ▸ List.mem_cons_self) hnx
      · have e1 : ext_key x = ext_key y := by simp [ext_key, hx, hy]
        exact absurd (e1 ▸ List.mem_cons_self) hnx
      · have e1 : ext_key x = ext_key z := by simp [ext_key, hx, hz]
        have m : ext_key x ∈ ext_key y :: ext_key z :: (rest.map ext_key) := by
          rw [e1]
          exact List.mem_cons_of_mem _ List.mem_cons_self
        exact absurd m hnx
      · have e1 : ext_key y = ext_key z := by simp [ext_key, hy, hz]
        exact absurd (e1 ▸ List.mem_cons_self) hny
      · have e1 : ext_key y = ext_key z := by simp [ext_key, hy, hz]
        exact absurd (e1 ▸ List.mem_cons_self) hny
      · have e1 : ext_key x = ext_key z := by simp [ext_key, hx, hz]
        have m : ext_key x ∈ ext_key y :: ext_key z :: (rest.map ext_key) := by
          rw [e1]
          exact List.mem_cons_of_mem _ List.mem_cons_self
        exact absurd m hnx
      · have e1 : ext_key x = ext_key y := by simp [ext_key, hx, hy]
        exact absurd (e1 ▸ List.mem_cons_self) hnx
      · have e1 : ext_key x = ext_key y := by simp [ext_key, hx, hy]
        exact absurd (e1 ▸ List.mem_cons_self) hnx
  have hge : 2 ≤ kept.length := by
    match hkept : kept with
    | [] =>
      simp at hmem1
    | [x] =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem1 hmem2
      exfalso
      exact hne (hmem1.trans hmem2.symm)
    | _ :: _ :: _ =>
      simp
  have hlen2 : kept.length = 2 := by omega
  obtain ⟨a, b, rfl⟩ : ∃ a b, kept = [a, b] := by
    match hkept : kept with
    | [] => simp at hlen2
    | [_] => simp at hlen2
    | [a, b] => exact ⟨a, b, rfl⟩
    | _ :: _ :: _ :: _ => simp at hlen2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem1 hmem2
  rcases hmem1 with h1a | h1b <;> rcases hmem2 with h2a | h2b
  · exfalso
    exact hne (h1a.trans h2a.symm)
  · exact Or.inl (by rw [h1a, h2b])
  · exact Or.inr (by rw [h1b, h2a])
  · exfalso
    exact hne (h1b.trans h2b.symm)

/-- 2-branch internal kept-pinning, both eligible (order-free disjunction). -/
theorem kept_int_two_ee_disj {kept : List (Role × Lab × DataSort × SessionType)}
    {b1 b2 : Role × Lab × DataSort × SessionType} {T1 T2 : SessionType}
    (hke : kept ≠ []) (hnd : (kept.map int_key).Nodup)
    (hmem1 : (b1.1, b1.2.1, b1.2.2.1, T1) ∈ kept)
    (hmem2 : (b2.1, b2.2.1, b2.2.2.1, T2) ∈ kept)
    (hallk : ∀ x ∈ kept, (x.1, x.2.1) = (b1.1, b1.2.1) ∨
      (x.1, x.2.1) = (b2.1, b2.2.1))
    (hne12 : (b1.1, b1.2.1) ≠ (b2.1, b2.2.1)) :
    kept = [(b1.1, b1.2.1, b1.2.2.1, T1), (b2.1, b2.2.1, b2.2.2.1, T2)] ∨
      kept = [(b2.1, b2.2.1, b2.2.2.1, T2),
        (b1.1, b1.2.1, b1.2.2.1, T1)] := by
  have hne : (b1.1, b1.2.1, b1.2.2.1, T1) ≠ (b2.1, b2.2.1, b2.2.2.1, T2) := by
    intro h
    apply hne12
    have := congrArg
      (fun t : Role × Lab × DataSort × SessionType => (t.1, t.2.1)) h
    simpa using this
  have hle : kept.length ≤ 2 := by
    match heq : kept with
    | [] => simp
    | [_] => simp
    | [_, _] => simp
    | x :: y :: z :: rest =>
      have hx := hallk x (by simp)
      have hy := hallk y (by simp)
      have hz := hallk z (by simp)
      simp only [List.map_cons] at hnd
      have hnx : int_key x ∉ int_key y :: int_key z :: (rest.map int_key) :=
        (List.nodup_cons.mp hnd).1
      have hny : int_key y ∉ int_key z :: (rest.map int_key) :=
        (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      rcases hx with hx | hx <;> rcases hy with hy | hy <;>
        rcases hz with hz | hz
      · have e1 : int_key x = int_key y := by simp [int_key, hx, hy]
        exact absurd (e1 ▸ List.mem_cons_self) hnx
      · have e1 : int_key x = int_key y := by simp [int_key, hx, hy]
        exact absurd (e1 ▸ List.mem_cons_self) hnx
      · have e1 : int_key x = int_key z := by simp [int_key, hx, hz]
        have m : int_key x ∈ int_key y :: int_key z :: (rest.map int_key) := by
          rw [e1]
          exact List.mem_cons_of_mem _ List.mem_cons_self
        exact absurd m hnx
      · have e1 : int_key y = int_key z := by simp [int_key, hy, hz]
        exact absurd (e1 ▸ List.mem_cons_self) hny
      · have e1 : int_key y = int_key z := by simp [int_key, hy, hz]
        exact absurd (e1 ▸ List.mem_cons_self) hny
      · have e1 : int_key x = int_key z := by simp [int_key, hx, hz]
        have m : int_key x ∈ int_key y :: int_key z :: (rest.map int_key) := by
          rw [e1]
          exact List.mem_cons_of_mem _ List.mem_cons_self
        exact absurd m hnx
      · have e1 : int_key x = int_key y := by simp [int_key, hx, hy]
        exact absurd (e1 ▸ List.mem_cons_self) hnx
      · have e1 : int_key x = int_key y := by simp [int_key, hx, hy]
        exact absurd (e1 ▸ List.mem_cons_self) hnx
  have hge : 2 ≤ kept.length := by
    match hkept : kept with
    | [] =>
      simp at hmem1
    | [x] =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem1 hmem2
      exfalso
      exact hne (hmem1.trans hmem2.symm)
    | _ :: _ :: _ =>
      simp
  have hlen2 : kept.length = 2 := by omega
  obtain ⟨a, b, rfl⟩ : ∃ a b, kept = [a, b] := by
    match hkept : kept with
    | [] => simp at hlen2
    | [_] => simp at hlen2
    | [a, b] => exact ⟨a, b, rfl⟩
    | _ :: _ :: _ :: _ => simp at hlen2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem1 hmem2
  rcases hmem1 with h1a | h1b <;> rcases hmem2 with h2a | h2b
  · exfalso
    exact hne (h1a.trans h2a.symm)
  · exact Or.inl (by rw [h1a, h2b])
  · exact Or.inr (by rw [h1b, h2a])
  · exfalso
    exact hne (h1b.trans h2b.symm)

/-- Constructor for `MonitorableCo` via a finite `mon_tr_yes_co_fun`-closed
    representative list. Every coinductive step target is `Eqv` to a computed
    output (`mon_tr_yes_co_fun_complete_eqv`), and steps transport along `Eqv`
    (`Prune_eqv_l_co`), so `Eqv`-coverage by `F` follows by `ReflTransGen`
    induction; `eqv_implies_unfoldEquiv` turns it into `UnfoldEquiv`-coverage. -/
theorem MonitorableCo.of_fun_closed {T : SessionType} (hT : T.WellFormed)
    (F : List SessionType) (hMem : T ∈ F)
    (hWF : ∀ V ∈ F, V.WellFormed)
    (hClosed : ∀ V ∈ F, ∀ p ∈ mon_tr_yes_co_fun V, p.2 ∈ F) :
    MonitorableCo T := by
  have hEqvCov : ∀ U : SessionType, Relation.ReflTransGen CoStep T U →
      ∃ V ∈ F, Eqv U V := by
    intro U hU
    induction hU with
    | refl => exact ⟨T, hMem, Eqv_refl hT⟩
    | tail hRT hStep ih =>
      obtain ⟨V, hVF, hEqvUV⟩ := ih
      unfold CoStep at hStep
      obtain ⟨γ, hU, hU', hco⟩ := hStep
      have hPrune := co_implies_Prune hU hU' hco
      have hPruneV := Prune_eqv_l_co hEqvUV hU (hWF V hVF) hPrune
      have hExV : Ex V γ := Ex_of_Prune (hWF V hVF) hPruneV
      obtain ⟨V3, hfmon⟩ := fmon_exists (hWF V hVF) hExV
      have hV3 : V3.WellFormed := fmon_preserves_wf (hWF V hVF) hfmon
      have hcoV : mon_tr_yes_co V γ V3 (hWF V hVF) hV3 :=
        fmon_implies_mon_tr_yes_co (hWF V hVF) hV3 hfmon
      have hPruneV3 := fmon_spec (hWF V hVF) hfmon
      have hEqvUV3 := Prune_unique (hWF V hVF) hPruneV hPruneV3
      obtain ⟨T2, hmem, hEqvV3T2⟩ :=
        mon_tr_yes_co_fun_complete_eqv (hWF V hVF) hV3 hcoV
      exact ⟨T2, hClosed V hVF (γ, T2) hmem, Eqv_trans hEqvUV3 hEqvV3T2⟩
  refine ⟨hT, F.toFinset, fun U hU => ?_⟩
  obtain ⟨V, hVF, hEqv⟩ := hEqvCov U hU
  refine ⟨V, List.mem_toFinset.mpr hVF, ?_⟩
  exact eqv_implies_unfoldEquiv (coStep_reachable_wf hT hU) (hWF V hVF) hEqv

-- ================================================================
-- Kernel-reducible fuel-bounded checker for `MonitorableCo`.
-- ================================================================

mutual
/-- Syntactic observation tags occurring anywhere in a session type. -/
def syntaxTags : SessionType → List ext_tag
  | .tEnd | .tVar _ => []
  | .tRec _ B => syntaxTags B
  | .internalChoice bs =>
      (bs.map fun b => .send b.1 b.2.1 b.2.2.1) ++ syntaxTagsInt bs
  | .externalChoice p bs =>
      (bs.map fun b => .recv p b.1 b.2.1) ++ syntaxTagsExt bs

/-- Internal-branch traversal for `syntaxTags`. -/
def syntaxTagsInt : List (Role × Lab × DataSort × SessionType) → List ext_tag
  | [] => []
  | (_, _, _, T) :: bs => syntaxTags T ++ syntaxTagsInt bs

/-- External-branch traversal for `syntaxTags`. -/
def syntaxTagsExt : List (Lab × DataSort × SessionType) → List ext_tag
  | [] => []
  | (_, _, T) :: bs => syntaxTags T ++ syntaxTagsExt bs
end

/-- Membership characterization for `syntaxTagsInt`. -/
theorem mem_syntaxTagsInt_iff
    {bs : List (Role × Lab × DataSort × SessionType)} {g : ext_tag} :
    g ∈ syntaxTagsInt bs ↔ ∃ b ∈ bs, g ∈ syntaxTags b.2.2.2 := by
  induction bs with
  | nil => simp [syntaxTagsInt]
  | cons hd tl ih =>
    rcases hd with ⟨r, l, s, T⟩
    simp [syntaxTagsInt, ih]

/-- Membership characterization for `syntaxTagsExt`. -/
theorem mem_syntaxTagsExt_iff
    {bs : List (Lab × DataSort × SessionType)} {g : ext_tag} :
    g ∈ syntaxTagsExt bs ↔ ∃ b ∈ bs, g ∈ syntaxTags b.2.2 := by
  induction bs with
  | nil => simp [syntaxTagsExt]
  | cons hd tl ih =>
    rcases hd with ⟨l, s, T⟩
    simp [syntaxTagsExt, ih]

/-- Substitution does not manufacture new syntactic tags. -/
theorem syntaxTags_subst (B : SessionType) (X : String) (U : SessionType)
    {g : ext_tag} (hg : g ∈ syntaxTags (substSessionType B X U)) :
    g ∈ syntaxTags B ∨ g ∈ syntaxTags U := by
  induction B using session_induction with
  | done => simp [substSessionType, syntaxTags] at hg
  | var Y =>
    simp only [substSessionType] at hg
    split at hg
    · exact Or.inr hg
    · simp [syntaxTags] at hg
  | rec Y C ih =>
    simp only [substSessionType] at hg
    split at hg
    · exact Or.inl hg
    · simp only [syntaxTags] at hg ⊢
      exact ih hg
  | intC bs ih =>
    simp only [substSessionType, go_int_eq_map, syntaxTags, List.map_map,
      List.mem_append, mem_syntaxTagsInt_iff] at hg ⊢
    rcases hg with hhead | ⟨b', hb', hgb'⟩
    · left; left
      rcases List.mem_map.mp hhead with ⟨b, hb, rfl⟩
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    · rcases List.mem_map.mp hb' with ⟨b, hb, rfl⟩
      rcases ih b hb hgb' with h1 | h2
      · left; right; exact ⟨b, hb, h1⟩
      · exact Or.inr h2
  | extC p bs ih =>
    simp only [substSessionType, go_ext_eq_map, syntaxTags, List.map_map,
      List.mem_append, mem_syntaxTagsExt_iff] at hg ⊢
    rcases hg with hhead | ⟨b', hb', hgb'⟩
    · left; left
      rcases List.mem_map.mp hhead with ⟨b, hb, rfl⟩
      exact List.mem_map.mpr ⟨b, hb, rfl⟩
    · rcases List.mem_map.mp hb' with ⟨b, hb, rfl⟩
      rcases ih b hb hgb' with h1 | h2
      · left; right; exact ⟨b, hb, h1⟩
      · exact Or.inr h2

/-- Every base transition tag occurs in `syntaxTags`. -/
theorem base_mem_syntaxTags {T U : SessionType} {g : ext_tag}
    (step : mon_tr_yes_base T g U) : g ∈ syntaxTags T := by
  induction step with
  | intC _ member =>
    simp only [syntaxTags, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨_, member, rfl⟩)
  | extC _ member =>
    simp only [syntaxTags, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨_, member, rfl⟩)
  | tRec _ ih =>
    rcases syntaxTags_subst _ _ _ ih with h1 | h2
    · exact h1
    · exact h2

/-- Every finite existential transition tag occurs in `syntaxTags`. -/
theorem exist_mem_syntaxTags {T U : SessionType} {g : ext_tag}
    (step : mon_tr_yes_exist T g U) : g ∈ syntaxTags T := by
  induction step with
  | base step => exact base_mem_syntaxTags step
  | @pfxInt branches kept q l s V nonempty off eq all unique keys ih =>
    obtain ⟨⟨r, a, b, W⟩, retained⟩ :=
      List.exists_mem_of_ne_nil kept nonempty.2
    obtain ⟨U0, member⟩ := keys r a b W retained
    simp only [syntaxTags, List.mem_append, mem_syntaxTagsInt_iff]
    exact Or.inr ⟨(r, a, b, U0), member, ih U0 W r a b member retained⟩
  | @pfxExt p branches kept q l s V nonempty off eq all unique keys ih =>
    obtain ⟨⟨a, b, W⟩, retained⟩ :=
      List.exists_mem_of_ne_nil kept nonempty.2
    obtain ⟨U0, member⟩ := keys a b W retained
    simp only [syntaxTags, List.mem_append, mem_syntaxTagsExt_iff]
    exact Or.inr ⟨(a, b, U0), member, ih U0 W a b member retained⟩
  | unfold _ ih =>
    rcases syntaxTags_subst _ _ _ ih with h1 | h2
    · exact h1
    · exact h2

/-- Pure value-level base step lookup at a head-normal type. -/
def baseAtHeadVal (H : SessionType) (g : ext_tag) : Option SessionType :=
  match H, g with
  | .internalChoice bs, .send p l s =>
      match bs.find? (fun b => b.1 == p && b.2.1 == l && b.2.2.1 == s) with
      | some b => some b.2.2.2
      | none => none
  | .externalChoice p bs, .recv q l s =>
      if p == q then
        match bs.find? (fun b => b.1 == l && b.2.1 == s) with
        | some b => some b.2.2
        | none => none
      else none
  | _, _ => none

/-- Soundness of `baseAtHeadVal`: a found target yields a `mon_tr_yes_base`
    step. -/
theorem baseAtHeadVal_sound {H : SessionType} (hW : H.WellFormed)
    {g : ext_tag} {V : SessionType} (h : baseAtHeadVal H g = some V) :
    mon_tr_yes_base H g V := by
  cases H with
  | internalChoice bs =>
    cases g with
    | recv q l s => simp [baseAtHeadVal] at h
    | send p l s =>
      simp only [baseAtHeadVal] at h
      cases hf : bs.find? (fun b => b.1 == p && b.2.1 == l && b.2.2.1 == s) with
      | none => simp [hf] at h
      | some b =>
        simp only [hf, Option.some.injEq] at h
        subst h
        rcases b with ⟨p', l', s', V0⟩
        have hmem := List.mem_of_find?_eq_some hf
        have hpred := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hpred
        rcases hpred with ⟨⟨rfl, rfl⟩, rfl⟩
        exact .intC hW.1.triple_nodup_of_internalChoice hmem
  | externalChoice p bs =>
    cases g with
    | send q l s => simp [baseAtHeadVal] at h
    | recv q l s =>
      simp only [baseAtHeadVal] at h
      split at h
      · rename_i hpq
        have rfl_pq : p = q := beq_iff_eq.mp hpq
        subst rfl_pq
        cases hf : bs.find? (fun b => b.1 == l && b.2.1 == s) with
        | none => simp [hf] at h
        | some b =>
          simp only [hf, Option.some.injEq] at h
          subst h
          rcases b with ⟨l', s', V0⟩
          have hmem := List.mem_of_find?_eq_some hf
          have hpred := List.find?_some hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hpred
          rcases hpred with ⟨rfl, rfl⟩
          exact .extC (nodup_ext_key2_of_wf hW) hmem
      · simp at h
  | tEnd => simp [baseAtHeadVal] at h
  | tVar _ => simp [baseAtHeadVal] at h
  | tRec _ _ => simp [baseAtHeadVal] at h

/-- Pure lookup of a session type in a fold context `G` via `SessionType.beq`. -/
def lookupFCtx (G : FCtx) (T : SessionType) : Option String :=
  match G.find? (fun p => SessionType.beq p.1 T) with
  | some (_, u) => some u
  | none => none

/-- Soundness of `lookupFCtx` on `some`: `(T, u) ∈ G`. -/
theorem lookupFCtx_some {G : FCtx} {T : SessionType} {u : String}
    (h : lookupFCtx G T = some u) : (T, u) ∈ G := by
  unfold lookupFCtx at h
  cases hf : G.find? (fun p => SessionType.beq p.1 T) with
  | none => simp [hf] at h
  | some p =>
    rcases p with ⟨T', u'⟩
    simp only [hf, Option.some.injEq] at h
    subst h
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    have heq : T' = T := SessionType.beq_sound T' T hpred
    subst heq
    exact hmem

/-- Soundness of `lookupFCtx` on `none`: `T ∉ G.map Prod.fst`. -/
theorem lookupFCtx_none {G : FCtx} {T : SessionType}
    (h : lookupFCtx G T = none) : T ∉ G.map Prod.fst := by
  unfold lookupFCtx at h
  cases hf : G.find? (fun p => SessionType.beq p.1 T) with
  | some p => simp [hf] at h
  | none =>
    intro hmem
    rcases List.mem_map.mp hmem with ⟨⟨T', u⟩, hmemG, heq⟩
    simp only at heq
    subst heq
    have hnone := List.find?_eq_none.mp hf (T', u) hmemG
    exact hnone (SessionType.beq_refl T')

/-- Pure branch filter/mapper for internal choices using `eligibility`. -/
def retainIntVal (childFn : SessionType → Option SessionType) (g : ext_tag) :
    List (Role × Lab × DataSort × SessionType) →
    Option (List (Role × Lab × DataSort × SessionType))
  | [] => some []
  | (r, l, s, T0) :: bs =>
      match retainIntVal childFn g bs with
      | none => none
      | some rest =>
          if eligibility T0 g then
            match childFn T0 with
            | some U => some ((r, l, s, U) :: rest)
            | none => none
          else some rest

/-- Pure branch filter/mapper for external choices using `eligibility`. -/
def retainExtVal (childFn : SessionType → Option SessionType) (g : ext_tag) :
    List (Lab × DataSort × SessionType) →
    Option (List (Lab × DataSort × SessionType))
  | [] => some []
  | (l, s, T0) :: bs =>
      match retainExtVal childFn g bs with
      | none => none
      | some rest =>
          if eligibility T0 g then
            match childFn T0 with
            | some U => some ((l, s, U) :: rest)
            | none => none
          else some rest

/-- Soundness of `retainIntVal`: produces a `KRint` retention witness. -/
theorem retainIntVal_sound {childFn : SessionType → Option SessionType}
    {G : FCtx} {g : ext_tag}
    {bs kept : List (Role × Lab × DataSort × SessionType)}
    (hW : ∀ b ∈ bs, b.2.2.2.WellFormed)
    (hChild : ∀ b ∈ bs, ∀ U, childFn b.2.2.2 = some U → fchild G b.2.2.2 g U)
    (h : retainIntVal childFn g bs = some kept) :
    KRint (fun T0 => Ex T0 g) (fun T0 U => fchild G T0 g U) bs kept := by
  induction bs generalizing kept with
  | nil =>
    simp [retainIntVal] at h
    subst h
    exact .nil
  | cons b bs ih =>
    rcases b with ⟨r, l, s, T0⟩
    simp only [retainIntVal] at h
    cases hr : retainIntVal childFn g bs with
    | none => simp [hr] at h
    | some rest =>
      simp only [hr] at h
      have hkr := ih (fun b hb => hW b (List.mem_cons_of_mem _ hb))
        (fun b hb => hChild b (List.mem_cons_of_mem _ hb)) hr
      have hWT0 : T0.WellFormed := hW (r, l, s, T0) List.mem_cons_self
      split at h
      · rename_i helig
        have hEx : Ex T0 g := (eligibility_correct hWT0).mp helig
        cases hc : childFn T0 with
        | none => simp [hc] at h
        | some U =>
          simp only [hc, Option.some.injEq] at h
          subst h
          exact .keep hEx (hChild (r, l, s, T0) List.mem_cons_self U hc) hkr
      · rename_i hnelig
        simp only [Option.some.injEq] at h
        subst h
        have hnEx : ¬ Ex T0 g :=
          fun hEx => hnelig ((eligibility_correct hWT0).mpr hEx)
        exact .drop hnEx hkr

/-- Soundness of `retainExtVal`: produces a `KRext` retention witness. -/
theorem retainExtVal_sound {childFn : SessionType → Option SessionType}
    {G : FCtx} {g : ext_tag}
    {bs kept : List (Lab × DataSort × SessionType)}
    (hW : ∀ b ∈ bs, b.2.2.WellFormed)
    (hChild : ∀ b ∈ bs, ∀ U, childFn b.2.2 = some U → fchild G b.2.2 g U)
    (h : retainExtVal childFn g bs = some kept) :
    KRext (fun T0 => Ex T0 g) (fun T0 U => fchild G T0 g U) bs kept := by
  induction bs generalizing kept with
  | nil =>
    simp [retainExtVal] at h
    subst h
    exact .nil
  | cons b bs ih =>
    rcases b with ⟨l, s, T0⟩
    simp only [retainExtVal] at h
    cases hr : retainExtVal childFn g bs with
    | none => simp [hr] at h
    | some rest =>
      simp only [hr] at h
      have hkr := ih (fun b hb => hW b (List.mem_cons_of_mem _ hb))
        (fun b hb => hChild b (List.mem_cons_of_mem _ hb)) hr
      have hWT0 : T0.WellFormed := hW (l, s, T0) List.mem_cons_self
      split at h
      · rename_i helig
        have hEx : Ex T0 g := (eligibility_correct hWT0).mp helig
        cases hc : childFn T0 with
        | none => simp [hc] at h
        | some U =>
          simp only [hc, Option.some.injEq] at h
          subst h
          exact .keep hEx (hChild (l, s, T0) List.mem_cons_self U hc) hkr
      · rename_i hnelig
        simp only [Option.some.injEq] at h
        subst h
        have hnEx : ¬ Ex T0 g :=
          fun hEx => hnelig ((eligibility_correct hWT0).mpr hEx)
        exact .drop hnEx hkr

/-- Structurally fuel-bounded computable fold transition (`fmon` value
    computation without well-founded recursion or proof arguments). -/
def fmonFuel : Nat → FCtx → SessionType → ext_tag → Option SessionType
  | 0, _, _, _ => none
  | n + 1, G, .internalChoice bs, g =>
      match baseAtHeadVal (.internalChoice bs) g with
      | some V => some V
      | none =>
          match g with
          | .send _ _ _ => none
          | .recv q lab S =>
              if bs.isEmpty || !(bs.all fun b => q != b.1) then none
              else
                let childFn (T0 : SessionType) : Option SessionType :=
                  match lookupFCtx G T0 with
                  | some u => some (.tVar u)
                  | none => fmonFuel n G T0 (.recv q lab S)
                match retainIntVal childFn (.recv q lab S) bs with
                | some kept =>
                    if kept.isEmpty then none else some (.internalChoice kept)
                | none => none
  | n + 1, G, .externalChoice p bs, g =>
      match baseAtHeadVal (.externalChoice p bs) g with
      | some V => some V
      | none =>
          match g with
          | .send _ _ _ => none
          | .recv q lab S =>
              if bs.isEmpty || q == p then none
              else
                let childFn (T0 : SessionType) : Option SessionType :=
                  match lookupFCtx G T0 with
                  | some u => some (.tVar u)
                  | none => fmonFuel n G T0 (.recv q lab S)
                match retainExtVal childFn (.recv q lab S) bs with
                | some kept =>
                    if kept.isEmpty then none
                    else some (.externalChoice p kept)
                | none => none
  | n + 1, G, .tRec X B, g =>
      let H := head (.tRec X B)
      match baseAtHeadVal H g with
      | some V => some V
      | none =>
          let u := fvar G.length
          let G' : FCtx := ((.tRec X B, u) :: G)
          match fmonFuel n G' H g with
          | some V => some (mkRec u V)
          | none => none
  | _ + 1, _, _, _ => none

/-- Soundness of `fmonFuel`: every returned target is a valid `fmon`
    derivation. -/
theorem fmonFuel_sound (fuel : Nat) :
    ∀ {G : FCtx} {T : SessionType} {g : ext_tag} {W : SessionType},
      T.WellFormed → fmonFuel fuel G T g = some W → fmon G T g W := by
  induction fuel with
  | zero => intro G T g W _ h; simp [fmonFuel] at h
  | succ n ih =>
    intro G T g W hW h
    cases T with
    | tEnd => simp [fmonFuel] at h
    | tVar _ => simp [fmonFuel] at h
    | internalChoice bs =>
      simp only [fmonFuel] at h
      cases hb : baseAtHeadVal (.internalChoice bs) g with
      | some V =>
        simp only [hb, Option.some.injEq] at h
        subst h
        exact .fm_base (baseAtHeadVal_sound hW hb)
      | none =>
        simp only [hb] at h
        cases g with
        | send _ _ _ => simp at h
        | recv q lab S =>
          simp only at h
          split at h
          · simp at h
          · rename_i hcond
            simp only [Bool.or_eq_true, Bool.not_eq_true', not_or,
              Bool.not_eq_false] at hcond
            rcases hcond with ⟨hbs_ne, hall_ne⟩
            have hne : bs ≠ [] := by
              intro heq; subst heq; simp at hbs_ne
            have hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ bs → q ≠ p' := by
              intro p' lab' S' T0 hmem
              have hq := List.all_eq_true.mp hall_ne (p', lab', S', T0) hmem
              simpa [bne_iff_ne] using hq
            let childFn (T0 : SessionType) : Option SessionType :=
              match lookupFCtx G T0 with
              | some u => some (.tVar u)
              | none => fmonFuel n G T0 (.recv q lab S)
            have hChild : ∀ b ∈ bs, ∀ U, childFn b.2.2.2 = some U →
                fchild G b.2.2.2 (.recv q lab S) U := by
              intro b hbmem U hc
              dsimp only [childFn] at hc
              cases hl : lookupFCtx G b.2.2.2 with
              | some u =>
                simp only [hl, Option.some.injEq] at hc
                subst hc
                exact .fc_fold (lookupFCtx_some hl)
              | none =>
                simp only [hl] at hc
                exact .fc_go (lookupFCtx_none hl)
                  (ih (wf_of_mem_int hW hbmem) hc)
            cases hr : retainIntVal childFn (.recv q lab S) bs with
            | none =>
              dsimp only [childFn] at hr
              rw [hr] at h
              simp at h
            | some kept =>
              have hr' := hr
              dsimp only [childFn] at hr'
              rw [hr'] at h
              simp only at h
              split at h
              · simp at h
              · rename_i hke_b
                simp only [Option.some.injEq] at h
                subst h
                have hke : kept ≠ [] := by
                  intro heq; subst heq; simp at hke_b
                have hk := retainIntVal_sound
                  (fun b hb => wf_of_mem_int hW hb) hChild hr
                have hnd3 := hW.1.triple_nodup_of_internalChoice
                refine .fm_pfxInt hne hke hno ?_ ?_ ?_ ?_ (KRint_sublist3 hk)
                · intro T0 T1 r l s h0 h1
                  obtain ⟨T0', h0', _, hp⟩ := KRint_kept_mem hk h1
                  have heq := unique_target_of_nodup_int hnd3 h0 h0'
                  subst T0'
                  exact hp
                · exact (KRint_sublist2 hk).nodup (nodup_int_key_of_wf hW)
                · intro r l s T1 h1
                  obtain ⟨T0, h0, hE, _⟩ := KRint_kept_mem hk h1
                  exact ⟨T0, h0, hE⟩
                · intro r l s T0 h0 hE
                  obtain ⟨T1, h1, _⟩ := KRint_cover hk h0 hE
                  exact ⟨T1, h1⟩
    | externalChoice p bs =>
      simp only [fmonFuel] at h
      cases hb : baseAtHeadVal (.externalChoice p bs) g with
      | some V =>
        simp only [hb, Option.some.injEq] at h
        subst h
        exact .fm_base (baseAtHeadVal_sound hW hb)
      | none =>
        simp only [hb] at h
        cases g with
        | send _ _ _ => simp at h
        | recv q lab S =>
          simp only at h
          split at h
          · simp at h
          · rename_i hcond
            simp only [Bool.or_eq_true, not_or, beq_iff_eq] at hcond
            rcases hcond with ⟨hbs_ne, hneq⟩
            have hne : bs ≠ [] := by
              intro heq; subst heq; simp at hbs_ne
            let childFn (T0 : SessionType) : Option SessionType :=
              match lookupFCtx G T0 with
              | some u => some (.tVar u)
              | none => fmonFuel n G T0 (.recv q lab S)
            have hChild : ∀ b ∈ bs, ∀ U, childFn b.2.2 = some U →
                fchild G b.2.2 (.recv q lab S) U := by
              intro b hbmem U hc
              dsimp only [childFn] at hc
              cases hl : lookupFCtx G b.2.2 with
              | some u =>
                simp only [hl, Option.some.injEq] at hc
                subst hc
                exact .fc_fold (lookupFCtx_some hl)
              | none =>
                simp only [hl] at hc
                exact .fc_go (lookupFCtx_none hl)
                  (ih (wf_of_mem_ext hW hbmem) hc)
            cases hr : retainExtVal childFn (.recv q lab S) bs with
            | none =>
              dsimp only [childFn] at hr
              rw [hr] at h
              simp at h
            | some kept =>
              have hr' := hr
              dsimp only [childFn] at hr'
              rw [hr'] at h
              simp only at h
              split at h
              · simp at h
              · rename_i hke_b
                simp only [Option.some.injEq] at h
                subst h
                have hke : kept ≠ [] := by
                  intro heq; subst heq; simp at hke_b
                have hk := retainExtVal_sound
                  (fun b hb => wf_of_mem_ext hW hb) hChild hr
                have hnd2 := nodup_ext_key2_of_wf hW
                refine .fm_pfxExt hne hke hneq ?_ ?_ ?_ ?_ (KRext_sublist2 hk)
                · intro T0 T1 l s h0 h1
                  obtain ⟨T0', h0', _, hp⟩ := KRext_kept_mem hk h1
                  have heq := unique_target_of_nodup_ext hnd2 h0 h0'
                  subst T0'
                  exact hp
                · exact (KRext_sublist1 hk).nodup (nodup_ext_key_of_wf hW)
                · intro l s T1 h1
                  obtain ⟨T0, h0, hE, _⟩ := KRext_kept_mem hk h1
                  exact ⟨T0, h0, hE⟩
                · intro l s T0 h0 hE
                  obtain ⟨T1, h1, _⟩ := KRext_cover hk h0 hE
                  exact ⟨T1, h1⟩
    | tRec X B =>
      simp only [fmonFuel] at h
      have hH : hnf (.tRec X B) (head (.tRec X B)) := head_correct hW
      have hWH : (head (.tRec X B)).WellFormed :=
        SessionType.wellFormedUnfold hW hH.1
      cases hb : baseAtHeadVal (head (.tRec X B)) g with
      | some V =>
        simp only [hb, Option.some.injEq] at h
        subst h
        exact .fm_base
          (base_unfoldstar_lift hH.1 (baseAtHeadVal_sound hWH hb))
      | none =>
        simp only [hb] at h
        cases hf :
            fmonFuel n ((.tRec X B, fvar G.length) :: G)
              (head (.tRec X B)) g with
        | none => simp [hf] at h
        | some V =>
          simp only [hf, Option.some.injEq] at h
          subst h
          exact .fm_rec hH.1 hH.2 (ih hWH hf)

/-- One-step successors of `V` computed by `fmonFuel` over `syntaxTags V`. -/
def nextStates (stepFuel : Nat) (V : SessionType) : List SessionType :=
  (syntaxTags V).filterMap fun g =>
    if eligibility V g then fmonFuel stepFuel [] V g else none

/-- Append elements of `ws` not yet in `seen` (up to `SessionType.beq`). -/
def addUnique :
    List SessionType → List SessionType →
      List SessionType × List SessionType
  | [], seen => ([], seen)
  | W :: ws, seen =>
      if seen.any (fun U => SessionType.beq W U) then
        addUnique ws seen
      else
        let (added, seen') := addUnique ws (W :: seen)
        (W :: added, seen')

/-- Fuel-bounded BFS computing a candidate finite cover list starting from
    `work` and `seen`. -/
def bfsClosure :
    Nat → Nat → List SessionType → List SessionType → List SessionType
  | 0, _, _, seen => seen
  | _ + 1, _, [], seen => seen
  | n + 1, stepFuel, V :: work, seen =>
      let succs := nextStates stepFuel V
      let (newWork, seen') := addUnique succs seen
      bfsClosure n stepFuel (work ++ newWork) seen'

/-- Executable check that `F` is closed under `fmonFuel` on all eligible
    syntactic tags of every member. -/
def stepClosedCheck (fuel : Nat) (F : List SessionType) : Bool :=
  F.all fun V =>
    (syntaxTags V).all fun g =>
      if eligibility V g then
        match fmonFuel fuel [] V g with
        | some W => F.any (fun U => SessionType.beq W U)
        | none => false
      else true

/-- Executable check that a candidate cover list `F` witnesses
    `MonitorableCo T`. -/
def coverClosedCheck (stepFuel : Nat) (T : SessionType)
    (F : List SessionType) : Bool :=
  T.wfCheck [] && F.any (fun U => SessionType.beq T U) &&
    F.all (fun V => V.wfCheck []) && stepClosedCheck stepFuel F

/-- Executable check for `MonitorableCo T`: computes the BFS closure `F`
    and verifies `coverClosedCheck`. Discharged on concrete types by
    `by decide`. -/
def monitorableCoCheck (bfsFuel stepFuel : Nat) (T : SessionType) : Bool :=
  coverClosedCheck stepFuel T (bfsClosure bfsFuel stepFuel [T] [T])

/-- Constructor for `MonitorableCo T` from a verified cover list `F`. -/
theorem MonitorableCo.of_cover_check {T : SessionType}
    {F : List SessionType} {stepFuel : Nat}
    (h : coverClosedCheck stepFuel T F = true) : MonitorableCo T := by
  unfold coverClosedCheck at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hTwf, hTmem⟩, hFwf⟩, hClosed⟩
  have hT : T.WellFormed := SessionType.wfCheck_sound hTwf
  obtain ⟨T0, hT0F, hT0eq⟩ := List.any_eq_true.mp hTmem
  have hTeq : T = T0 := SessionType.beq_sound T T0 hT0eq
  subst hTeq
  have hWF : ∀ V ∈ F, V.WellFormed := by
    intro V hVF
    exact SessionType.wfCheck_sound (List.all_eq_true.mp hFwf V hVF)
  have hEqvCov : ∀ U : SessionType, Relation.ReflTransGen CoStep T U →
      ∃ V ∈ F, Eqv U V := by
    intro U hU
    induction hU with
    | refl => exact ⟨T, hT0F, Eqv_refl hT⟩
    | tail hRT hStep ih =>
      obtain ⟨V, hVF, hEqvUV⟩ := ih
      unfold CoStep at hStep
      obtain ⟨γ, hU, hU', hco⟩ := hStep
      have hPrune := co_implies_Prune hU hU' hco
      have hPruneV := Prune_eqv_l_co hEqvUV hU (hWF V hVF) hPrune
      have hExV : Ex V γ := Ex_of_Prune (hWF V hVF) hPruneV
      have hElig : eligibility V γ = true :=
        (eligibility_correct (hWF V hVF)).mpr hExV
      obtain ⟨_, hexStep⟩ := hExV
      have hTag : γ ∈ syntaxTags V := exist_mem_syntaxTags hexStep
      have hVclosed := List.all_eq_true.mp hClosed V hVF
      have hGclosed := List.all_eq_true.mp hVclosed γ hTag
      simp only [hElig, ite_true] at hGclosed
      cases hf : fmonFuel stepFuel [] V γ with
      | none => simp [hf] at hGclosed
      | some W =>
        simp only [hf] at hGclosed
        obtain ⟨W0, hW0F, hW0eq⟩ := List.any_eq_true.mp hGclosed
        have hWeq : W = W0 := SessionType.beq_sound W W0 hW0eq
        subst hWeq
        have hfmon : fmon [] V γ W :=
          fmonFuel_sound stepFuel (hWF V hVF) hf
        have hPruneW := fmon_spec (hWF V hVF) hfmon
        have hEqvU'W := Prune_unique (hWF V hVF) hPruneV hPruneW
        exact ⟨W, hW0F, hEqvU'W⟩
  refine ⟨hT, F.toFinset, fun U hU => ?_⟩
  obtain ⟨V, hVF, hEqv⟩ := hEqvCov U hU
  exact ⟨V, List.mem_toFinset.mpr hVF,
    eqv_implies_unfoldEquiv (coStep_reachable_wf hT hU) (hWF V hVF) hEqv⟩

/-- Constructor for `MonitorableCo T` via `monitorableCoCheck` (`by decide`). -/
theorem MonitorableCo.of_check {T : SessionType} {bfsFuel stepFuel : Nat}
    (h : monitorableCoCheck bfsFuel stepFuel T = true) : MonitorableCo T :=
  MonitorableCo.of_cover_check h

/-- Evaluating `monitor_fold_val_partial_co` on an empty queue returns the
    session type itself. -/
theorem monitor_fold_val_partial_co_nil (T : SessionType) :
    monitor_fold_val_partial_co (T, []) = some T := by
  have hex : ∃ T', monitor_fold_co (T, []) T' := ⟨T, rfl⟩
  unfold monitor_fold_val_partial_co
  rw [dite_eq_left hex]
  exact congrArg some hex.choose_spec

/-- Every empty-queue network whose member session types are `MonitorableCo`
    satisfies `Network.MonitorableCo`. -/
theorem Network.MonitorableCo_of_all_nil (N : Network)
    (hNil : ∀ x ∈ N, x.2.2 = [])
    (hMon : ∀ x ∈ N, _root_.MonitorableCo x.2.1) :
    Network.MonitorableCo N := by
  induction N with
  | nil => exact ⟨[], rfl, by intro x hx; cases hx⟩
  | cons hd tl ih =>
    obtain ⟨r, T, Q⟩ := hd
    have hQ : Q = [] := hNil _ (List.mem_cons.mpr (Or.inl rfl))
    subst hQ
    have hM := monitor_fold_val_partial_co_nil T
    obtain ⟨MN, hMN, hall⟩ := ih
      (fun x hx => hNil x (List.mem_cons.mpr (Or.inr hx)))
      (fun x hx => hMon x (List.mem_cons.mpr (Or.inr hx)))
    refine ⟨(r, ((T, []), T)) :: MN,
      by rw [consistentInstrumentation_co, hM, hMN], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxtl
    · exact hMon (r, (T, [])) (List.mem_cons.mpr (Or.inl rfl))
    · exact hall x hxtl

/-- Executable check for `Network.MonitorableCo` on an empty-queue network. -/
def networkMonitorableCoCheck (bfsFuel stepFuel : Nat) (N : Network) : Bool :=
  N.all (fun x => x.2.2.isEmpty) &&
    N.all (fun x => monitorableCoCheck bfsFuel stepFuel x.2.1)

/-- Constructor for `Network.MonitorableCo` via `networkMonitorableCoCheck`. -/
theorem Network.MonitorableCo_of_check {N : Network} {bfsFuel stepFuel : Nat}
    (h : networkMonitorableCoCheck bfsFuel stepFuel N = true) :
    Network.MonitorableCo N := by
  unfold networkMonitorableCoCheck at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hNil, hMon⟩
  apply Network.MonitorableCo_of_all_nil N
  · intro x hx
    exact List.isEmpty_iff.mp (List.all_eq_true.mp hNil x hx)
  · intro x hx
    exact MonitorableCo.of_check (List.all_eq_true.mp hMon x hx)

