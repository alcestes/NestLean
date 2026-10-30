import Cslib
import Nest.SessionUtils
import Nest.MonitorToolkit
import Nest.MonitorLTS

set_option linter.unusedVariables false

open Cslib
open Cslib.LTS

/-!
# Counterexamples ProofUtils: shared NoRec helper lemmas.

NoRec helper lemmas shared by the counterexamples in this directory.
All declarations keep their root-level names.
-/

/-- List infrastructure for the maximality rebuild: sublists through `map`
    and `filterMap` (names not in core/Batteries under these forms). -/
private lemma Sublist.map' {α β : Type} (f : α → β) {l₁ l₂ : List α}
    (h : List.Sublist l₁ l₂) : List.Sublist (l₁.map f) (l₂.map f) := by
  induction h with
  | slnil => exact List.Sublist.slnil
  | cons _ _ ih => exact List.Sublist.cons _ ih
  | cons_cons _ _ ih => exact List.Sublist.cons_cons _ ih

/-- Same-key entries of a nodup-keyed list coincide (for aligning kept keys
    with source branches on both internal `(role, label)` pairs and
    external `label`s). -/
lemma nodup_key_unique {α κ : Type} {f : α → κ} {l : List α} {a b : α}
    (hnd : (l.map f).Nodup) (ha : a ∈ l) (hb : b ∈ l) (hfab : f a = f b) :
    a = b := by
  induction l with
  | nil => simp at ha
  | cons hd tl ih =>
    simp at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · simp at hnd
        obtain ⟨hnotin, _⟩ := hnd
        exact ((hnotin _ hb) hfab.symm).elim
    · rcases hb with rfl | hb
      · simp at hnd
        obtain ⟨hnotin, _⟩ := hnd
        exact ((hnotin _ ha) hfab).elim
      · have htl : (tl.map f).Nodup := by
          simp at hnd
          exact hnd.2
        exact ih htl ha hb

/-- Branches for the `internalChoice` prefix rule that have an `mon_tr_yes` transition for the given role,
    label, and data sort. Drops entries that have no `mon_tr_yes` transition. -/
noncomputable def intBranchesWithmon_tr_yes (branches : List (Role × Lab × DataSort × SessionType))
    (q : Role) (lab : Lab) (S : DataSort)
    (ih : (T0 : SessionType) → sizeOf T0 < sizeOf (SessionType.internalChoice branches) → ext_tag → SessionType → Prop) :
    List (Role × Lab × DataSort × SessionType) :=
  branches.attach.filterMap (λ ⟨(r, lab', S', T0), hmem⟩ =>
    by
      by_cases h : ∃ (T'' : SessionType),
        ih T0 (sizeOf_SessionType_lt_sizeOf_internalChoice hmem) (ext_tag.recv q lab S) T''
      · exact some (r, lab', S', h.choose)
      · exact none
  )

/-- Branches for the `externalChoice` prefix rule that have an `mon_tr_yes` transition for the given role,
    label, and data sort. Drops entries that have no `mon_tr_yes` transition. -/
noncomputable def extBranchesWithmon_tr_yes (p : Role) (branches : List (Lab × DataSort × SessionType))
    (q : Role) (lab : Lab) (S : DataSort)
    (ih : (T0 : SessionType) → sizeOf T0 < sizeOf (SessionType.externalChoice p branches) → ext_tag → SessionType → Prop) :
    List (Lab × DataSort × SessionType) :=
  branches.attach.filterMap (λ ⟨(lab', S', T0), hmem⟩ =>
    by
      by_cases h : ∃ (T'' : SessionType),
        ih T0 (sizeOf_SessionType_lt_sizeOf_externalChoice hmem) (ext_tag.recv q lab S) T''
      · exact some (lab', S', h.choose)
      · exact none
  )


/-- Pair-key nodup projection for internal choices (avoids casing `NoDupl`
    at use sites, where the index may carry inaccessible implicits). -/
private lemma noDupl_intBranches_pair_nodup
    {branches : List (Role × Lab × DataSort × SessionType)}
    (h : (SessionType.internalChoice branches).NoDupl) :
    ((branches.map fun x : Role × Lab × DataSort × SessionType =>
      (x.1, x.2.1))).Nodup := by
  cases h with
  | internalChoice hnp _ _ => exact hnp


/-- NoRec receive-firing forces an `extC` head (`intC` prunes by tag mismatch,
    `tRec` by `NoRec`). Mirror of `st_trans_out_int_c_of_norec`. -/
lemma st_trans_inp_ext_c_of_norec {T T' : SessionType} {r : Role} {lab : Lab} {S : DataSort}
    (hNR : T.NoRec) (hST : st_trans T (st_label.inp r lab S) T') :
    ∃ branches, T = SessionType.externalChoice r branches ∧ (lab, S, T') ∈ branches := by
  cases hST with
  | extC hmem => exact ⟨_, rfl, hmem⟩
  | tRec h => cases hNR


/-- Fully-kept `filterMap` key-sublist (public port). -/
theorem sd_filterMap_keys_sublist {α : Type*} {β : Type*} {γ : Type*}
    {l : List α} {f : α → Option β} {g : β → γ} {h : α → γ}
    (hkey : ∀ a ∈ l, ∀ b, f a = some b → g b = h a) :
    (List.map g (List.filterMap f l)).Sublist (List.map h l) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filterMap_cons]
    match e : f a with
    | some b =>
      have hkb : g b = h a := hkey a (List.mem_cons.mpr (Or.inl rfl)) b e
      have iht := ih (fun a ha b hb => hkey a (List.mem_cons.mpr (Or.inr ha)) b hb)
      simp only [List.map_cons]
      rw [← hkb]
      exact List.Sublist.cons_cons _ iht
    | none =>
      have iht := ih (fun a ha b hb => hkey a (List.mem_cons.mpr (Or.inr ha)) b hb)
      simp only [List.map_cons]
      exact List.Sublist.cons _ iht


/-- Acceptable-to-maximal for recursion-free types: an existential
    yes-derivation upgrades to a maximal one. By size induction (`NoRec`
    prunes `tRec`/`unfold`, so branch targets are strictly smaller):
    `base` is maximal directly; `pfxInt`/`pfxExt` rebuild maximality by
    filter-collecting ALL accepting branches (classical decidability),
    with kept targets defined as the IH-maximal targets (so `hall` uses
    choose-specs and `hallMax` transports along proof irrelevance).
    This discharges the maximality-existence bottom for the NoRec fragment —
    no determinism needed. -/
lemma acceptable_to_maximal_norec_aux : ∀ (n : Nat) (T0 : SessionType) (γ : ext_tag),
    T0.NoRec → T0.NoDupl → sizeOf T0 ≤ n →
    (∃ T1, mon_tr_yes_exist T0 γ T1) → ∃ T1, mon_tr_yes T0 γ T1 := by
  intro n
  induction n with
  | zero =>
    intro T0 γ hNR hND hle hacc
    cases T0 <;> simp at hle
  | succ n ih =>
    intro T0 γ hNR hND hle hacc
    obtain ⟨T1, hE⟩ := hacc
    have hbase : ∀ {T : SessionType} {γ : ext_tag} {V : SessionType}
        (hb : mon_tr_yes_base T γ V),
        T.NoRec → T.NoDupl → sizeOf T ≤ n + 1 →
        ∃ T1, mon_tr_yes T γ T1 := by
      intro T γ V hb hNR hND hle
      exact ⟨_, mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩
    have hpfxInt : ∀ {branches kept : List (Role × Lab × DataSort × SessionType)}
        {q : Role} {lab : Lab} {S : DataSort} {T : SessionType}
        (hne : branches ≠ [] ∧ kept ≠ [])
        (hno : ∀ p' lab' S' T0, (p', lab', S', T0) ∈ branches → q ≠ p')
        (hkept : T = SessionType.internalChoice kept)
        (hall : ∀ T0 T1 r l s, (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1)
        (hNodupKept : (kept.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)).Nodup)
        (hkey : ∀ r l s T1, (r, l, s, T1) ∈ kept → ∃ T0, (r, l, s, T0) ∈ branches)
        (_ihHall : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
          (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
          T0.NoRec → T0.NoDupl → sizeOf T0 ≤ n + 1 → ∃ T1, mon_tr_yes T0 (ext_tag.recv q lab S) T1)
        (hNR : (SessionType.internalChoice branches).NoRec)
        (hND : (SessionType.internalChoice branches).NoDupl)
        (hle : sizeOf (SessionType.internalChoice branches) ≤ n + 1),
        ∃ T1, mon_tr_yes (SessionType.internalChoice branches) (ext_tag.recv q lab S) T1 := by
      intro branches kept q lab S T hne hno hkept hall hNodupKept hkey _ihHall hNR hND hle
      classical
      have hNRb : ∀ (x : Role × Lab × DataSort × SessionType),
          x ∈ branches → x.2.2.2.NoRec := by
        intro x hx
        cases hNR with
        | internalChoice hbr => exact hbr x hx
      have hNDb : ∀ (x : Role × Lab × DataSort × SessionType),
          x ∈ branches → x.2.2.2.NoDupl := by
        intro x hx
        exact noDupl_of_mem_intBranches hND hx
      have hlt : ∀ (x : Role × Lab × DataSort × SessionType),
          x ∈ branches → sizeOf x.2.2.2 ≤ n := by
        intro x hx
        rcases x with ⟨r, l, s, T0b⟩
        show sizeOf T0b ≤ n
        have h := sizeOf_SessionType_lt_sizeOf_internalChoice hx
        omega
      -- IH-maximal per accepting branch.
      have ihMax : ∀ (x : Role × Lab × DataSort × SessionType),
          x ∈ branches → (∃ T1, mon_tr_yes_exist x.2.2.2 (ext_tag.recv q lab S) T1) →
          ∃ T1, mon_tr_yes x.2.2.2 (ext_tag.recv q lab S) T1 := by
        intro x hx hax
        rcases x with ⟨r, l, s, T0b⟩
        exact ih T0b (ext_tag.recv q lab S) (hNRb _ hx) (hNDb _ hx) (hlt _ hx) hax
      -- Acceptors (Bool filter) + kept with IH-chosen targets.
      set acceptors := branches.filter
        (fun x : Role × Lab × DataSort × SessionType =>
          decide (∃ T1, mon_tr_yes_exist x.2.2.2 (ext_tag.recv q lab S) T1)) with haccDef
      have accOf : ∀ (x : Role × Lab × DataSort × SessionType),
          x ∈ acceptors → ∃ T1, mon_tr_yes_exist x.2.2.2 (ext_tag.recv q lab S) T1 := by
        intro x hmem
        exact of_decide_eq_true (List.mem_filter.mp hmem).2
      have memBrOf : ∀ (x : Role × Lab × DataSort × SessionType),
          x ∈ acceptors → x ∈ branches := by
        intro x hmem
        exact (List.mem_filter.mp hmem).1
      set keptF := acceptors.attach.map (fun a => match a with
        | ⟨(r, l, s, T0b), hmem⟩ =>
          (r, l, s, (ihMax _ (memBrOf _ hmem) (accOf _ hmem)).choose)) with hkeptDef
      have hkeptEq : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
          (r, l, s, T1) ∈ keptF →
          ∃ (T0b : SessionType) (hmemB : (r, l, s, T0b) ∈ branches)
            (hmemA : (r, l, s, T0b) ∈ acceptors),
            T1 = (ihMax _ (memBrOf _ hmemA) (accOf _ hmemA)).choose := by
        intro r l s T1 hmemK
        rw [hkeptDef] at hmemK
        have hmap : ∃ a, a ∈ acceptors.attach ∧
            (match a with
              | ⟨(r', l', s', T0b), hmem⟩ =>
                (r', l', s', (ihMax _ (memBrOf _ hmem) (accOf _ hmem)).choose)) =
            (r, l, s, T1) := List.mem_map.mp hmemK
        obtain ⟨⟨⟨r', l', s', T0b⟩, hmemA⟩, _, hF⟩ := hmap
        simp only [Prod.mk.injEq] at hF
        obtain ⟨e1, e2, e3, e4⟩ := hF
        rw [e1, e2, e3] at hmemA
        have hmemB : (r, l, s, T0b) ∈ branches := memBrOf _ hmemA
        exact ⟨T0b, hmemB, hmemA, e4.symm⟩
      have hmemKept : ∀ (b : Role × Lab × DataSort × SessionType)
          (hmemA : b ∈ acceptors),
          ((b.1, b.2.1, b.2.2.1,
            (ihMax _ (memBrOf _ hmemA) (accOf _ hmemA)).choose)) ∈ keptF := by
        intro b hmemA
        rw [hkeptDef]
        apply List.mem_map.mpr
        refine ⟨⟨b, hmemA⟩, ?_, ?_⟩
        · exact List.mem_attach _ _
        · rcases b with ⟨r, l, s, T0b⟩
          rfl
      -- Kept pair-keys nodup via sublist.
      have hsubKeys : List.Sublist
          ((keptF.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)))
          ((branches.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) := by
        have h1 : ((keptF.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) =
            ((acceptors.attach.map fun a : {x // x ∈ acceptors} =>
              ((a.val.1, a.val.2.1) : Role × Lab))) := by
          simp only [hkeptDef, List.map_map]
          apply List.map_congr_left
          intro a _
          rcases a with ⟨⟨r, l, s, T0b⟩, hmem⟩
          rfl
        have h2 : ((acceptors.attach.map fun a : {x // x ∈ acceptors} =>
            ((a.val.1, a.val.2.1) : Role × Lab))) =
            (acceptors.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) := by
          have := List.attach_map_val (f := fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) (l := acceptors)
          simpa using this
        have h3 : List.Sublist
            ((acceptors.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)))
            ((branches.map fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) :=
          Sublist.map' _ List.filter_sublist
        rw [h1, h2]
        exact h3
      have hnodupK : ((keptF.map fun x : Role × Lab × DataSort × SessionType =>
          (x.1, x.2.1))).Nodup := by
        have hndp : ((branches.map fun x : Role × Lab × DataSort × SessionType =>
            (x.1, x.2.1))).Nodup :=
          noDupl_intBranches_pair_nodup hND
        exact hndp.sublist hsubKeys
      -- nonempty kept for both constructions.
      have hkeptFne : keptF ≠ [] := by
        rcases hne with ⟨-, hkeptne⟩
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hkeptne
        obtain ⟨r, l, s, T0e⟩ := e
        obtain ⟨T0eB, hmemB⟩ := hkey _ _ _ _ he
        have hEe := hall _ _ _ _ _ hmemB he
        have hacc : ∃ T1, mon_tr_yes_exist T0eB _ T1 := ⟨_, hEe⟩
        have hmemA : (r, l, s, T0eB) ∈ acceptors := by
          apply List.mem_filter.mpr
          exact ⟨hmemB, decide_eq_true hacc⟩
        exact List.ne_nil_of_mem (hmemKept _ hmemA)
      have hneF : branches ≠ [] ∧ keptF ≠ [] :=
        ⟨SessionType.NoDupl.ne_of_internalChoice hND, hkeptFne⟩
      have hall' : ∀ (T0 T1 : SessionType) (r : Role) (l : Lab) (s : DataSort),
          (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ keptF →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1 := by
        intro T0 T1 r l s hmemB hmemK
        obtain ⟨T0b, hmemB', hmemA, hT⟩ := hkeptEq _ _ _ _ hmemK
        have hTeq : T0 = T0b := by
          have hndp : ((branches.map fun x : Role × Lab × DataSort × SessionType =>
              (x.1, x.2.1))).Nodup :=
            noDupl_intBranches_pair_nodup hND
          have heq := nodup_key_unique hndp hmemB hmemB' (by simpa using rfl)
          simpa using congrArg
            (fun x : Role × Lab × DataSort × SessionType => x.2.2.2) heq
        subst hTeq
        subst hT
        exact ((ihMax _ (memBrOf _ hmemA) (accOf _ hmemA)).choose_spec).1
      have hkey' : ∀ (r : Role) (l : Lab) (s : DataSort) (T1 : SessionType),
          (r, l, s, T1) ∈ keptF → ∃ T0, (r, l, s, T0) ∈ branches := by
        intro r l s T1 hmemK
        obtain ⟨T0b, hmemB, _, _⟩ := hkeptEq _ _ _ _ hmemK
        exact ⟨T0b, hmemB⟩
      refine ⟨SessionType.internalChoice keptF, ?_, ?_⟩
      · exact mon_tr_yes_exist.pfxInt hneF hno rfl hall' hnodupK hkey'
      · refine @mon_tr_yes_max_deriv.pfxInt branches keptF q lab S _
          hneF hno rfl hall' hnodupK hkey' ?hallMax' ?hcover' ?horder'
        · intro T0 T1 r l s hmemB hmemK hsub
          obtain ⟨T0b, hmemB', hmemA, hT⟩ := hkeptEq _ _ _ _ hmemK
          have hTeq : T0 = T0b := by
            have hndp : ((branches.map fun x : Role × Lab × DataSort × SessionType =>
                (x.1, x.2.1))).Nodup :=
              noDupl_intBranches_pair_nodup hND
            have heq := nodup_key_unique hndp hmemB hmemB' (by simpa using rfl)
            simpa using congrArg
              (fun x : Role × Lab × DataSort × SessionType => x.2.2.2) heq
          subst hTeq
          subst hT
          have hMstar := (ihMax _ (memBrOf _ hmemA)
            (accOf _ hmemA)).choose_spec
          obtain ⟨hEs, hMs⟩ := hMstar
          have heqP : hsub = hEs := proof_irrel _ _
          rw [heqP]
          exact hMs
        · intro r l s T0 hmemB hacc
          obtain ⟨T1acc, hEacc⟩ := hacc
          have hmemAcc : (r, l, s, T0) ∈ acceptors :=
            List.mem_filter.mpr ⟨hmemB, decide_eq_true ⟨T1acc, hEacc⟩⟩
          exact ⟨(ihMax _ (memBrOf _ hmemAcc)
            (accOf _ hmemAcc)).choose,
            hmemKept _ hmemAcc⟩
        · -- keptF triple-keys sublist (same chain, triple key).
          have h1 : ((keptF.map fun x : Role × Lab × DataSort × SessionType =>
              (x.1, x.2.1, x.2.2.1))) =
              ((acceptors.attach.map fun a : {x // x ∈ acceptors} =>
                ((a.val.1, a.val.2.1, a.val.2.2.1) : Role × Lab × DataSort))) := by
            simp only [hkeptDef, List.map_map]
            apply List.map_congr_left
            intro a _
            rcases a with ⟨⟨r, l, s, T0b⟩, hmem⟩
            rfl
          have h2 : ((acceptors.attach.map fun a : {x // x ∈ acceptors} =>
              ((a.val.1, a.val.2.1, a.val.2.2.1) : Role × Lab × DataSort))) =
              (acceptors.map fun x : Role × Lab × DataSort × SessionType =>
                (x.1, x.2.1, x.2.2.1)) := by
            have := List.attach_map_val (f := fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)) (l := acceptors)
            simpa using this
          have h3 : List.Sublist
              ((acceptors.map fun x : Role × Lab × DataSort × SessionType =>
                (x.1, x.2.1, x.2.2.1)))
              ((branches.map fun x : Role × Lab × DataSort × SessionType =>
                (x.1, x.2.1, x.2.2.1))) :=
            Sublist.map' _ List.filter_sublist
          rw [h1, h2]
          exact h3
    have hpfxExt : ∀ {pp : Role} {branches keptF : List (Lab × DataSort × SessionType)}
        {q : Role} {lab : Lab} {S : DataSort} {T : SessionType}
        (hne : branches ≠ [] ∧ keptF ≠ [])
        (hneq : q ≠ pp)
        (hkept : T = SessionType.externalChoice pp keptF)
        (hall : ∀ T0 T1 l s, (l, s, T0) ∈ branches → (l, s, T1) ∈ keptF →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1)
        (hNodupKept : (keptF.map fun x : Lab × DataSort × SessionType => x.1).Nodup)
        (hkey : ∀ l s T1, (l, s, T1) ∈ keptF → ∃ T0, (l, s, T0) ∈ branches)
        (_ihHall : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
          (l, s, T0) ∈ branches → (l, s, T1) ∈ keptF →
          T0.NoRec → T0.NoDupl → sizeOf T0 ≤ n + 1 → ∃ T1, mon_tr_yes T0 (ext_tag.recv q lab S) T1)
        (hNR : (SessionType.externalChoice pp branches).NoRec)
        (hND : (SessionType.externalChoice pp branches).NoDupl)
        (hle : sizeOf (SessionType.externalChoice pp branches) ≤ n + 1),
        ∃ T1, mon_tr_yes (SessionType.externalChoice pp branches) (ext_tag.recv q lab S) T1 := by
      intro p branches keptF q lab S T hne hneq hkept hall hnodup hkey _ihHall hNR hND hle
      classical
      have hNRb : ∀ (x : Lab × DataSort × SessionType),
          x ∈ branches → x.2.2.NoRec := by
        intro x hx
        cases hNR with
        | externalChoice hbr => exact hbr x hx
      have hNDb : ∀ (x : Lab × DataSort × SessionType),
          x ∈ branches → x.2.2.NoDupl := by
        intro x hx
        exact noDupl_of_mem_extBranches hND hx
      have hlt : ∀ (x : Lab × DataSort × SessionType),
          x ∈ branches → sizeOf x.2.2 ≤ n := by
        intro x hx
        rcases x with ⟨l, s, T0b⟩
        show sizeOf T0b ≤ n
        have h := sizeOf_SessionType_lt_sizeOf_externalChoice (p := p) hx
        omega
      have ihMax : ∀ (x : Lab × DataSort × SessionType),
          x ∈ branches → (∃ T1, mon_tr_yes_exist x.2.2 (ext_tag.recv q lab S) T1) →
          ∃ T1, mon_tr_yes x.2.2 (ext_tag.recv q lab S) T1 := by
        intro x hx hax
        rcases x with ⟨l, s, T0b⟩
        exact ih T0b (ext_tag.recv q lab S) (hNRb _ hx) (hNDb _ hx) (hlt _ hx) hax
      set acceptors := branches.filter
        (fun x : Lab × DataSort × SessionType =>
          decide (∃ T1, mon_tr_yes_exist x.2.2 (ext_tag.recv q lab S) T1)) with haccDef
      have accOf : ∀ (x : Lab × DataSort × SessionType),
          x ∈ acceptors → ∃ T1, mon_tr_yes_exist x.2.2 (ext_tag.recv q lab S) T1 := by
        intro x hmem
        exact of_decide_eq_true (List.mem_filter.mp hmem).2
      have memBrOf : ∀ (x : Lab × DataSort × SessionType),
          x ∈ acceptors → x ∈ branches := by
        intro x hmem
        exact (List.mem_filter.mp hmem).1
      set keptF := acceptors.attach.map (fun a => match a with
        | ⟨(l, s, T0b), hmem⟩ =>
          (l, s, (ihMax _ (memBrOf _ hmem) (accOf _ hmem)).choose)) with hkeptDef
      have hkeptEq : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
          (l, s, T1) ∈ keptF →
          ∃ (T0b : SessionType) (hmemB : (l, s, T0b) ∈ branches)
            (hmemA : (l, s, T0b) ∈ acceptors),
            T1 = (ihMax _ (memBrOf _ hmemA) (accOf _ hmemA)).choose := by
        intro l s T1 hmemK
        rw [hkeptDef] at hmemK
        have hmap : ∃ a, a ∈ acceptors.attach ∧
            (match a with
              | ⟨(l', s', T0b), hmem⟩ =>
                (l', s', (ihMax _ (memBrOf _ hmem) (accOf _ hmem)).choose)) =
            (l, s, T1) := List.mem_map.mp hmemK
        obtain ⟨⟨⟨l', s', T0b⟩, hmemA⟩, _, hF⟩ := hmap
        simp only [Prod.mk.injEq] at hF
        obtain ⟨e1, e2, e3⟩ := hF
        rw [e1, e2] at hmemA
        have hmemB : (l, s, T0b) ∈ branches := memBrOf _ hmemA
        exact ⟨T0b, hmemB, hmemA, e3.symm⟩
      have hmemKept : ∀ (b : Lab × DataSort × SessionType)
          (hmemA : b ∈ acceptors),
          ((b.1, b.2.1,
            (ihMax _ (memBrOf _ hmemA) (accOf _ hmemA)).choose)) ∈ keptF := by
        intro b hmemA
        rw [hkeptDef]
        apply List.mem_map.mpr
        refine ⟨⟨b, hmemA⟩, ?_, ?_⟩
        · exact List.mem_attach _ _
        · rcases b with ⟨l, s, T0b⟩
          rfl
      have hsubKeys : List.Sublist
          ((keptF.map fun x : Lab × DataSort × SessionType => x.1))
          ((branches.map fun x : Lab × DataSort × SessionType => x.1)) := by
        have h1 : ((keptF.map fun x : Lab × DataSort × SessionType => x.1)) =
            ((acceptors.attach.map fun a : {x // x ∈ acceptors} =>
              ((a.val.1) : Lab))) := by
          simp only [hkeptDef, List.map_map]
          apply List.map_congr_left
          intro a _
          rcases a with ⟨⟨l, s, T0b⟩, hmem⟩
          rfl
        have h2 : ((acceptors.attach.map fun a : {x // x ∈ acceptors} =>
            ((a.val.1) : Lab))) =
            (acceptors.map fun x : Lab × DataSort × SessionType => x.1) := by
          have := List.attach_map_val (f := fun x : Lab × DataSort × SessionType => x.1) (l := acceptors)
          simpa using this
        have h3 : List.Sublist
            ((acceptors.map fun x : Lab × DataSort × SessionType => x.1))
            ((branches.map fun x : Lab × DataSort × SessionType => x.1)) :=
          Sublist.map' _ List.filter_sublist
        rw [h1, h2]
        exact h3
      have hnodupK : ((keptF.map fun x : Lab × DataSort × SessionType =>
          x.1)).Nodup := by
        have hndp : ((branches.map fun x : Lab × DataSort × SessionType =>
            x.1)).Nodup := by
          cases hND with
          | externalChoice hnp _ _ => exact hnp
        exact hndp.sublist hsubKeys
      have hkeptFne : keptF ≠ [] := by
        rcases hne with ⟨-, hkeptne⟩
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hkeptne
        obtain ⟨l, s, T0e⟩ := e
        obtain ⟨T0eB, hmemB⟩ := hkey _ _ _ he
        have hEe := hall _ _ _ _ hmemB he
        have hacc : ∃ T1, mon_tr_yes_exist T0eB _ T1 := ⟨_, hEe⟩
        have hmemA : (l, s, T0eB) ∈ acceptors := by
          apply List.mem_filter.mpr
          exact ⟨hmemB, decide_eq_true hacc⟩
        exact List.ne_nil_of_mem (hmemKept _ hmemA)
      have hneF : branches ≠ [] ∧ keptF ≠ [] :=
        ⟨SessionType.NoDupl.ne_of_externalChoice hND, hkeptFne⟩
      have hall' : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort),
          (l, s, T0) ∈ branches → (l, s, T1) ∈ keptF →
          mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1 := by
        intro T0 T1 l s hmemB hmemK
        obtain ⟨T0b, hmemB', hmemA, hT⟩ := hkeptEq _ _ _ hmemK
        have hTeq : T0 = T0b := by
          have hndp : ((branches.map fun x : Lab × DataSort × SessionType =>
              x.1)).Nodup := by
            cases hND with
            | externalChoice hnp _ _ => exact hnp
          have heq := nodup_key_unique hndp hmemB hmemB' (by simpa using rfl)
          simpa using congrArg
            (fun x : Lab × DataSort × SessionType => x.2.2) heq
        subst hTeq
        subst hT
        exact ((ihMax _ (memBrOf _ hmemA) (accOf _ hmemA)).choose_spec).1
      have hkey' : ∀ (l : Lab) (s : DataSort) (T1 : SessionType),
          (l, s, T1) ∈ keptF → ∃ T0, (l, s, T0) ∈ branches := by
        intro l s T1 hmemK
        obtain ⟨T0b, hmemB, _, _⟩ := hkeptEq _ _ _ hmemK
        exact ⟨T0b, hmemB⟩
      have hallMaxE : ∀ (T0 T1 : SessionType) (l : Lab) (s : DataSort)
          (hmemB : (l, s, T0) ∈ branches) (hmemK : (l, s, T1) ∈ keptF)
          (hsub : mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1),
          mon_tr_yes_max_deriv hsub := by
        intro T0 T1 l s hmemB hmemK hsub
        obtain ⟨T0b, hmemB', hmemA, hT⟩ := hkeptEq _ _ _ hmemK
        have hTeq : T0 = T0b := by
          have hndp : ((branches.map fun x : Lab × DataSort × SessionType =>
              x.1)).Nodup := by
            cases hND with
            | externalChoice hnp _ _ => exact hnp
          have heq := nodup_key_unique hndp hmemB hmemB' (by simpa using rfl)
          simpa using congrArg
            (fun x : Lab × DataSort × SessionType => x.2.2) heq
        subst hTeq
        subst hT
        have hMstar := (ihMax _ (memBrOf _ hmemA)
          (accOf _ hmemA)).choose_spec
        obtain ⟨hEs, hMs⟩ := hMstar
        have heqP : hsub = hEs := proof_irrel _ _
        rw [heqP]
        exact hMs
      have hcoverE : ∀ (l : Lab) (s : DataSort) (T0 : SessionType),
          (l, s, T0) ∈ branches → (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) →
          ∃ T1, (l, s, T1) ∈ keptF := by
        intro l s T0 hmemB hacc
        obtain ⟨T1acc, hEacc⟩ := hacc
        have hmemAcc : (l, s, T0) ∈ acceptors :=
          List.mem_filter.mpr ⟨hmemB, decide_eq_true ⟨T1acc, hEacc⟩⟩
        exact ⟨(ihMax _ (memBrOf _ hmemAcc)
          (accOf _ hmemAcc)).choose,
          hmemKept _ hmemAcc⟩
      have horderE : List.Sublist
          ((keptF.map fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
          ((branches.map fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) := by
        have h1 : ((keptF.map fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) =
            ((acceptors.attach.map fun a : {x // x ∈ acceptors} =>
              ((a.val.1, a.val.2.1) : Lab × DataSort))) := by
          simp only [hkeptDef, List.map_map]
          apply List.map_congr_left
          intro a _
          rcases a with ⟨⟨l, s, T0b⟩, hmem⟩
          rfl
        have h2 : ((acceptors.attach.map fun a : {x // x ∈ acceptors} =>
            ((a.val.1, a.val.2.1) : Lab × DataSort))) =
            (acceptors.map fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) := by
          have := List.attach_map_val (f := fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) (l := acceptors)
          simpa using this
        have h3 : List.Sublist
            ((acceptors.map fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
            ((branches.map fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) :=
          Sublist.map' _ List.filter_sublist
        rw [h1, h2]
        exact h3
      have hmaxE : mon_tr_yes_max_deriv (@mon_tr_yes_exist.pfxExt p branches keptF q lab S _
        hneF hneq rfl hall' hnodupK hkey') :=
        @mon_tr_yes_max_deriv.pfxExt p branches keptF q lab S _ hneF hneq rfl hall' hnodupK hkey'
          hallMaxE hcoverE horderE
      refine ⟨SessionType.externalChoice p keptF, ?_, ?_⟩
      · exact mon_tr_yes_exist.pfxExt hneF hneq rfl hall' hnodupK hkey'
      · exact hmaxE
    have hunfold : ∀ {X : String} {B : SessionType} {γ : ext_tag} {V : SessionType}
        (h : mon_tr_yes_exist (substSessionType B X (SessionType.tRec X B)) γ V),
        ((substSessionType B X (SessionType.tRec X B)).NoRec →
          (substSessionType B X (SessionType.tRec X B)).NoDupl →
          sizeOf (substSessionType B X (SessionType.tRec X B)) ≤ n + 1 →
          ∃ T1, mon_tr_yes (substSessionType B X (SessionType.tRec X B)) γ T1) →
        (SessionType.tRec X B).NoRec → (SessionType.tRec X B).NoDupl →
        sizeOf (SessionType.tRec X B) ≤ n + 1 →
        ∃ T1, mon_tr_yes (SessionType.tRec X B) γ T1 := by
      intro X B γ V h _ hNR hND hle
      cases hNR
    exact mon_tr_yes_exist.rec (motive := fun T γ V _ => T.NoRec → T.NoDupl →
        sizeOf T ≤ n + 1 → ∃ T1, mon_tr_yes T γ T1) hbase hpfxInt hpfxExt hunfold hE hNR hND hle


/-- Public wrapper: acceptable-to-maximal for recursion-free types. -/
lemma acceptable_to_maximal_norec {T0 : SessionType} {γ : ext_tag}
    (hNR : T0.NoRec) (hND : T0.NoDupl)
    (hacc : ∃ T1, mon_tr_yes_exist T0 γ T1) : ∃ T1, mon_tr_yes T0 γ T1 :=
  acceptable_to_maximal_norec_aux _ _ _ hNR hND (Nat.le_refl _) hacc


/-- One-hop role lineage: kept int-filter entries come
    from same-key original entries, so branch-sender roles survive. -/
theorem spec_monitor_step_iff {M Mi : SessionType} {r : Role} {lab : Lab} {S : DataSort}
    {kept : List (Lab × DataSort × SessionType)}
    (hM : M = SessionType.externalChoice r kept) (hND : M.NoDupl) :
    mon_tr_yes M (ext_tag.recv r lab S) Mi ↔
    ∃ U, (lab, S, U) ∈ kept ∧ Mi = U := by
  subst hM
  constructor
  · intro hYes
    rcases hYes with ⟨hE, hMax⟩
    cases hMax with
    | base =>
      rename_i hb
      cases hb with
      | extC _ hmem => exact ⟨_, hmem, rfl⟩
    | @pfxExt _ _ _ _ _ _ _ _ hneq _ _ _ _ _ _ _ =>
      exact absurd rfl hneq
  · intro h
    obtain ⟨W, hmemW, hEqW⟩ := h
    subst hEqW
    have hpair : List.Nodup (List.map
        (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) kept) := by
      cases hND with
      | externalChoice h _ _ => exact nodup_of_nodup_labels h
    have hb : mon_tr_yes_base (SessionType.externalChoice r kept)
        (ext_tag.recv r lab S) Mi :=
      mon_tr_yes_base.extC hpair hmemW
    exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩


/-- Membership in `intBranchesWithmon_tr_yes` (public version): the source entry lies in
    the original branches and the kept entry carries the yes-transition to its new
    target. -/
lemma mem_intBranchesWithmon_tr_yes_recv {branches : List (Role × Lab × DataSort × SessionType)}
    {q : Role} {lab : Lab} {S : DataSort}
    {ih : (T0 : SessionType) → sizeOf T0 < sizeOf (SessionType.internalChoice branches) → ext_tag → SessionType → Prop}
    {p' : Role} {lab' : Lab} {S' : DataSort} {T'' : SessionType}
    (h : (p', lab', S', T'') ∈ intBranchesWithmon_tr_yes branches q lab S ih) :
    ∃ (T0 : SessionType) (hmem : (p', lab', S', T0) ∈ branches),
      ih T0 (sizeOf_SessionType_lt_sizeOf_internalChoice hmem) (ext_tag.recv q lab S) T'' := by
  unfold intBranchesWithmon_tr_yes at h
  simp [List.mem_filterMap] at h
  rcases h with ⟨T0, hmem, hf⟩
  rcases hf with ⟨hc, hEq⟩
  refine ⟨T0, hmem, ?_⟩
  rw [← hEq]
  exact hc.choose_spec

/-- Membership in `extBranchesWithmon_tr_yes` (public version of the lemma in
    `Nest.Basic`): the source entry lies in the original branches and the kept
    entry carries the yes-transition to its new target. -/
lemma mem_extBranchesWithmon_tr_yes_recv {p : Role} {branches : List (Lab × DataSort × SessionType)}
    {q : Role} {lab : Lab} {S : DataSort}
    {ih : (T0 : SessionType) → sizeOf T0 < sizeOf (SessionType.externalChoice p branches) → ext_tag → SessionType → Prop}
    {lab' : Lab} {S' : DataSort} {T'' : SessionType}
    (h : (lab', S', T'') ∈ extBranchesWithmon_tr_yes p branches q lab S ih) :
    ∃ (T0 : SessionType) (hmem : (lab', S', T0) ∈ branches),
      ih T0 (sizeOf_SessionType_lt_sizeOf_externalChoice hmem) (ext_tag.recv q lab S) T'' := by
  unfold extBranchesWithmon_tr_yes at h
  simp [List.mem_filterMap] at h
  rcases h with ⟨T0, hmem, hf⟩
  rcases hf with ⟨hc, hEq⟩
  refine ⟨T0, hmem, ?_⟩
  rw [← hEq]
  exact hc.choose_spec

/-- Auxiliary version of `st_trans_out_imp_mon_tr_yes_base` that is general in the transition
    label, so that the `st_trans` induction can run (the index `out p lab S` is not
    a variable). -/
lemma st_trans_out_imp_mon_tr_yes_base_aux : ∀ {T T' : SessionType} {α : st_label},
    st_trans T α T' →
    (∀ (p : Role) (lab : Lab) (S : DataSort),
      α = st_label.out p lab S → SessionType.WellFormed T →
        mon_tr_yes_base T (ext_tag.send p lab S) T') := by
  intro T T' α hST
  induction hST
  case extC =>
    intro p' lab' S' hEq hwf
    cases hEq
  case intC =>
    rename_i branches p lab S T h_mem
    intro p' lab' S' hEq hwf
    cases hEq
    apply mon_tr_yes_base.intC
    · rcases hwf with ⟨h_nd, _, _⟩
      cases h_nd with
      | internalChoice h_nl h_ne h_br =>
          exact nodup_triple_of_nodup_pair h_nl
    · exact h_mem
  case tRec =>
    rename_i X T T' α h' ih
    intro p' lab' S' hEq hwf
    apply mon_tr_yes_base.tRec
    exact ih p' lab' S' hEq (by
      rcases hwf with ⟨h_nd, h_cl, h_cv⟩
      cases h_nd with
      | tRec h_nd_body =>
          have h_nd_subst : SessionType.NoDupl (substSessionType T X (SessionType.tRec X T)) :=
            NoDupl_subst h_nd_body (SessionType.NoDupl.tRec h_nd_body)
          have h_cl_subst : (substSessionType T X (SessionType.tRec X T)).IsClosed := by
            unfold SessionType.IsClosed
            rw [fv_subst_aux T X (SessionType.tRec X T) h_cl]
            simpa [SessionType.IsClosed, SessionType.fv] using h_cl
          have h_cv_subst : (substSessionType T X (SessionType.tRec X T)).Contractive := by
            cases h_cv with
            | tRec h_cv_body h_cv_guard =>
                exact IsContractive_subst h_cv_body
                  (SessionType.Contractive.tRec h_cv_body h_cv_guard) h_cl
          exact ⟨h_nd_subst, h_cl_subst, h_cv_subst⟩)

/-- A `st_trans` output transition of a well-formed session type lifts to a base "yes"
    encoder transition with the same target (S-IntC + S-Rec). -/
lemma st_trans_out_imp_mon_tr_yes_base {T T' : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (hST : st_trans T (st_label.out p lab S) T') (h_wf : SessionType.WellFormed T) :
    mon_tr_yes_base T (ext_tag.send p lab S) T' := by
  exact st_trans_out_imp_mon_tr_yes_base_aux hST p lab S rfl h_wf

/-- A `st_trans` output transition of a well-formed session type lifts to a "yes" encoder
    transition with the same target (maximal via `base`). -/
lemma st_trans_out_imp_mon_tr_yes {T T' : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (hST : st_trans T (st_label.out p lab S) T') (h_wf : SessionType.WellFormed T) :
    mon_tr_yes T (ext_tag.send p lab S) T' := by
  have hb : mon_tr_yes_base T (ext_tag.send p lab S) T' :=
    st_trans_out_imp_mon_tr_yes_base hST h_wf
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩


/-- Drain labels to monitor tags: `out` (send/`sendFresh`) becomes a
    monitor `send`, `inp` (`dequeue`/`specInp`) becomes a monitor `recv`.
    `tau` (silent unfold) is unobservable: the dummy tag below is
    unreachable by construction — tag pipelines (`over_trans_lifts_to_mon_tr_yes`,
    `over_trans_trace_to_mon_yes_seq`, `sDeqOf`/`sSpecOf`) skip or exclude silent
    steps before mapping. -/
def overTagToExt : st_label → ext_tag
  | st_label.out p lab S => ext_tag.send p lab S
  | st_label.inp p lab S => ext_tag.recv p lab S
  | st_label.tau => ext_tag.recv "" "" ""

/-- Accepting branches survive the external maximal filter (public port). -/
theorem sd_kept_of_acceptable {pe : Role}
    {branches : List (Lab × DataSort × SessionType)}
    {q : Role} {lab : Lab} {S : DataSort}
    {l' : Lab} {s' : DataSort} {T0' : SessionType}
    (hmemB : (l', s', T0') ∈ branches)
    (hacc : ∃ T'', mon_tr_yes T0' (ext_tag.recv q lab S) T'') :
    ∃ T1, (l', s', T1) ∈ extBranchesWithmon_tr_yes pe branches q lab S
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') := by
  unfold extBranchesWithmon_tr_yes
  simp only [List.mem_filterMap]
  refine ⟨hacc.choose, ⟨(l', s', T0'), hmemB⟩, List.mem_attach _ _, ?_⟩
  dsimp only
  split
  · next h =>
    cases proof_irrel h hacc
    rfl
  · next hdrop =>
    exact absurd hacc hdrop


/-- Maximal prefix over the full external filter kept-list (public port). -/
theorem sd_maxPfxExt_of_kept_ne_norec
    {pe : Role} {branches : List (Lab × DataSort × SessionType)}
    {q : Role} {lab : Lab} {S : DataSort}
    (hNR : (SessionType.externalChoice pe branches).NoRec)
    (hND : SessionType.NoDupl (SessionType.externalChoice pe branches))
    (hnepq : q ≠ pe)
    (hne_kept : extBranchesWithmon_tr_yes pe branches q lab S
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') ≠ []) :
    mon_tr_yes (SessionType.externalChoice pe branches) (ext_tag.recv q lab S)
      (SessionType.externalChoice pe (extBranchesWithmon_tr_yes pe branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))) := by
  have hpair : List.Nodup
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches) := by
    cases hND with
    | externalChoice h_nodup _ _ => exact nodup_of_nodup_labels h_nodup
  have hne : branches ≠ [] ∧
      extBranchesWithmon_tr_yes pe branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') ≠ [] :=
    ⟨hND.ne_of_externalChoice, hne_kept⟩
  have hall : ∀ (T0' T1 : SessionType) (l' : Lab) (s' : DataSort),
      (l', s', T0') ∈ branches →
      (l', s', T1) ∈ extBranchesWithmon_tr_yes pe branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') →
      mon_tr_yes_exist T0' (ext_tag.recv q lab S) T1 := by
    intro T0' T1 l' s' hmemB hmemK
    obtain ⟨T0s, hmem0, hY⟩ := mem_extBranchesWithmon_tr_yes_recv hmemK
    obtain ⟨hE, _⟩ := hY
    have hT0eq : T0s = T0' := unique_target_of_nodup_ext hpair hmem0 hmemB
    subst hT0eq
    exact hE
  have hNodupKept : List.Nodup ((extBranchesWithmon_tr_yes pe branches q lab S
      (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')).map
      (fun x : Lab × DataSort × SessionType => x.1)) := by
    have hsrc : List.Nodup
        (List.map (fun x : Lab × DataSort × SessionType => x.1) branches) := by
      cases hND with
      | externalChoice h_nodup _ _ => exact h_nodup
    have hatt : List.map (fun a : {x // x ∈ branches} => a.val.1) branches.attach =
        List.map (fun x : Lab × DataSort × SessionType => x.1) branches :=
      List.attach_map_val (f := fun x : Lab × DataSort × SessionType => x.1)
    have hsub : (List.map (fun x : Lab × DataSort × SessionType => x.1)
        (extBranchesWithmon_tr_yes pe branches q lab S
          (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))).Sublist
        (List.map (fun a : {x // x ∈ branches} => a.val.1) branches.attach) :=
      sd_filterMap_keys_sublist ?hkeyLab
    rw [hatt] at hsub
    exact hsub.nodup hsrc
    · intro a ha b hb
      rcases a with ⟨⟨l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  have hkey : ∀ (l' : Lab) (s' : DataSort) (T1 : SessionType),
      (l', s', T1) ∈ extBranchesWithmon_tr_yes pe branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') →
      ∃ T0', (l', s', T0') ∈ branches := by
    intro l' s' T1 hmemK
    obtain ⟨T0s, hmem0, _⟩ := mem_extBranchesWithmon_tr_yes_recv hmemK
    exact ⟨T0s, hmem0⟩
  have hallMax : ∀ (T0' T1 : SessionType) (l' : Lab) (s' : DataSort)
      (hmemB : (l', s', T0') ∈ branches)
      (hmemK : (l', s', T1) ∈ extBranchesWithmon_tr_yes pe branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T''))
      (hsub : mon_tr_yes_exist T0' (ext_tag.recv q lab S) T1),
      mon_tr_yes_max_deriv hsub := by
    intro T0' T1 l' s' hmemB hmemK hsub
    obtain ⟨T0s, hmem0, hY⟩ := mem_extBranchesWithmon_tr_yes_recv hmemK
    obtain ⟨hE, hM⟩ := hY
    have hT0eq : T0s = T0' := unique_target_of_nodup_ext hpair hmem0 hmemB
    subst hT0eq
    cases proof_irrel hsub hE
    exact hM
  have hcover : ∀ (l' : Lab) (s' : DataSort) (T0' : SessionType),
      (l', s', T0') ∈ branches →
      (∃ T1, mon_tr_yes_exist T0' (ext_tag.recv q lab S) T1) →
      ∃ T1, (l', s', T1) ∈ extBranchesWithmon_tr_yes pe branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'') := by
    intro l' s' T0' hmemB hex
    have hNR0 : T0'.NoRec := noRec_of_mem_extBranches hNR hmemB
    have hND0 : T0'.NoDupl := by
      cases hND with
      | externalChoice _ _ hbr => exact hbr _ hmemB
    obtain ⟨T1', hMax⟩ := acceptable_to_maximal_norec hNR0 hND0 hex
    exact sd_kept_of_acceptable hmemB ⟨T1', hMax⟩
  have horder : List.Sublist
      ((extBranchesWithmon_tr_yes pe branches q lab S
        (fun T0 _hlt γ T'' => mon_tr_yes T0 γ T'')).map
        (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
      (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches) := by
    have hatt : List.map (fun a : {x // x ∈ branches} => (a.val.1, a.val.2.1))
        branches.attach =
        List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)) branches :=
      List.attach_map_val
        (f := fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
    rw [← hatt]
    refine sd_filterMap_keys_sublist ?hkeyOrd
    · intro a ha b hb
      rcases a with ⟨⟨l', s', T0'⟩, hmem⟩
      dsimp only at hb
      split at hb
      · next hkeep =>
        cases hb
        rfl
      · next hdrop =>
        cases hb
  exact ⟨mon_tr_yes_exist.pfxExt hne hnepq rfl hall hNodupKept hkey,
    mon_tr_yes_max_deriv.pfxExt (hne := hne) (hneq := hnepq) (hkept := rfl)
      (hall := hall) (hNodupKept := hNodupKept) (hkey := hkey)
      hallMax hcover horder⟩


/-- Rule kind of an approx step. -/
inductive TrKind where
  | dequeue
  | spec
  | send
  /-- Silent unfold (skipped by all tag/queue projections). -/
  | tau
  deriving DecidableEq


/-- Trace carrying per-step rule kinds. -/
inductive ClassTr : SessionTypeWithQueue → List (TrKind × st_label) →
    SessionTypeWithQueue → Prop where
  | refl (stq : SessionTypeWithQueue) : ClassTr stq [] stq
  | deq {T T' : SessionType} {Q Q' : Queue} {p : Role} {lab : Lab} {S : DataSort}
      {branches : List (Lab × DataSort × SessionType)}
      {ρ : List (TrKind × st_label)} {e : SessionTypeWithQueue}
      (hEq : T = SessionType.externalChoice p branches)
      (hmem : (lab, S, T') ∈ branches)
      (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q')
      (hT : ClassTr (T', Q') ρ e) :
      ClassTr (T, Q) ((TrKind.dequeue, st_label.inp p lab S) :: ρ) e
  | spec {T T' : SessionType} {Q : Queue} {p : Role} {lab : Lab} {S : DataSort}
      {branches : List (Lab × DataSort × SessionType)}
      {ρ : List (TrKind × st_label)} {e : SessionTypeWithQueue}
      (hEq : T = SessionType.externalChoice p branches)
      (hmem : (lab, S, T') ∈ branches)
      (hAbs : ∀ m ∈ Q, m.1 ≠ p)
      (hT : ClassTr (T', Q) ρ e) :
      ClassTr (T, Q) ((TrKind.spec, st_label.inp p lab S) :: ρ) e
  | tau {T U : SessionType} {Q : Queue}
      {ρ : List (TrKind × st_label)} {e : SessionTypeWithQueue}
      (hU : Unfold1 T U)
      (hT : ClassTr (U, Q) ρ e) :
      ClassTr (T, Q) ((TrKind.tau, st_label.tau) :: ρ) e
  | send {T T' : SessionType} {Q : Queue} {p : Role} {lab : Lab} {S : DataSort}
      {branches : List (Role × Lab × DataSort × SessionType)}
      {ρ : List (TrKind × st_label)} {e : SessionTypeWithQueue}
      (hEq : T = SessionType.internalChoice branches)
      (hST : st_trans T (st_label.out p lab S) T')
      (hFresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U : SessionType),
        (r', l', s', U) ∈ branches → ∀ m ∈ Q, m.1 ≠ r')
      (hT : ClassTr (T', Q) ρ e) :
      ClassTr (T, Q) ((TrKind.send, st_label.out p lab S) :: ρ) e
