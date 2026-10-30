import Nest.NetworkLiveness

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# SessionUtils: Session utilities: substitution, encoder uniqueness.

Substitution/no-op and closedness lemmas, branch
well-formedness descent, encoder-target uniqueness, `monitor_fold` toolkit,
overapprox traces, and the deep-drainability core.
-/

-- ================================================================
/-- Scan success pins the oldest message from the target's sender: a
    successful `dequeue.go` scan splits the scanned total around (the first
    occurrence of) the target with a sender-free prefix — it can neither
    match earlier (exact match stops) nor pass a same-sender message
    (mismatch blocks). -/
private lemma go_oldest_of_some {acc left : Queue} {tgt : QueueMessage} {Q' : Queue}
    (hFree : ∀ x ∈ acc, x.1 ≠ tgt.1)
    (hGo : Queue.dequeue.go acc left tgt = some Q') :
    ∃ s t, acc ++ left = s ++ (tgt :: t) ∧ ∀ x ∈ s, x.1 ≠ tgt.1 := by
  induction left generalizing acc Q' with
  | nil => simp [Queue.dequeue.go] at hGo
  | cons m rest ih =>
    by_cases hm : m = tgt
    · subst hm
      exact ⟨acc, rest, rfl, hFree⟩
    · have hm_ne : m ≠ tgt := hm
      by_cases hs : m.1 = tgt.1
      · exfalso
        simp [Queue.dequeue.go, hm_ne, hs] at hGo
      · have hns : m.1 ≠ tgt.1 := hs
        simp [Queue.dequeue.go, hm_ne, hns] at hGo
        have hFree' : ∀ x ∈ acc ++ [m], x.1 ≠ tgt.1 := by
          intro x hx
          rcases List.mem_append.mp hx with hL | hR
          · exact hFree x hL
          · have hxeq : x = m := by simpa using hR
            rw [hxeq]
            exact hns
        obtain ⟨s, t, hsplit, hfr⟩ := ih hFree' hGo
        refine ⟨s, t, ?_, hfr⟩
        simpa [List.append_assoc] using hsplit

/-- A successful dequeue targets the oldest message from its sender. -/
lemma dequeue_oldest_of_some {Q : Queue} {tgt : QueueMessage} {Q' : Queue}
    (h : Q.dequeue tgt = some Q') :
    ∃ s t, Q = s ++ (tgt :: t) ∧ ∀ x ∈ s, x.1 ≠ tgt.1 := by
  unfold Queue.dequeue at h
  simpa using go_oldest_of_some (acc := []) (by simp) h

mutual
/-- Substituting for a variable absent from the free variables is the identity. -/
  theorem subst_noop : (T : SessionType) → (X : String) → (U : SessionType) →
      X ∉ T.fv → substSessionType T X U = T
  | SessionType.tEnd, X, U, _ => by
      simp [substSessionType]
  | SessionType.tVar Y, X, U, h => by
      have hXY : ¬X = Y := by
        intro hXY
        subst hXY
        simp [SessionType.fv] at h
      simp [substSessionType, hXY]
  | SessionType.internalChoice branches, X, U, h => by
      change SessionType.internalChoice (substSessionType.goInt X U branches) = _
      rw [subst_goInt_noop branches X U h]
  | SessionType.externalChoice p branches, X, U, h => by
      change SessionType.externalChoice p (substSessionType.goExt X U branches) = _
      rw [subst_goExt_noop branches X U h]
  | SessionType.tRec Y T', X, U, h => by
      by_cases hXY : X = Y
      · simp [substSessionType, hXY]
      · simp only [substSessionType, hXY, ite_false]
        congr 1
        apply subst_noop T' X U
        simp [SessionType.fv] at h ⊢
        intro hm
        exact hXY (h hm)
  termination_by T X U h => sizeOf T
  decreasing_by
    all_goals simp_wf

/-- Substituting for a variable absent from all free variables of an internal-choice branch list is
   the identity. -/
  theorem subst_goInt_noop : (l : List (Role × Lab × DataSort × SessionType)) → (X : String) →
      (U : SessionType) → X ∉ SessionType.fv.goInt l → substSessionType.goInt X U l = l
  | [], X, U, _ => by simp [substSessionType.goInt]
  | h :: t, X, U, hm => by
      simp [substSessionType.goInt, SessionType.fv.goInt] at hm ⊢
      constructor
      · rw [subst_noop h.2.2.2 X U hm.1]
      · exact subst_goInt_noop t X U hm.2
  termination_by l X U _ => sizeOf l
  decreasing_by
    all_goals simp_wf <;> first | exact sizeOf_int_quad_lt h t

/-- Substituting for a variable absent from all free variables of an external-choice branch list is
   the identity. -/
  theorem subst_goExt_noop : (l : List (Lab × DataSort × SessionType)) → (X : String) →
      (U : SessionType) → X ∉ SessionType.fv.goExt l → substSessionType.goExt X U l = l
  | [], X, U, _ => by simp [substSessionType.goExt]
  | h :: t, X, U, hm => by
      simp [substSessionType.goExt, SessionType.fv.goExt] at hm ⊢
      constructor
      · rw [subst_noop h.2.2 X U hm.1]
      · exact subst_goExt_noop t X U hm.2
  termination_by l X U _ => sizeOf l
  decreasing_by
    all_goals simp_wf <;> first | exact sizeOf_ext_triple_lt h t
end


/-- Number of `tRec` nodes (static fuel bound under vacuous recursion). -/
def SessionType.tRecCount : SessionType → Nat
  | .tEnd => 0
  | .tVar _ => 0
  | .internalChoice branches => SessionType.tRecCount.goInt branches
  | .externalChoice _ branches => SessionType.tRecCount.goExt branches
  | .tRec _ B => SessionType.tRecCount B + 1
where
  goInt : List (Role × Lab × DataSort × SessionType) → Nat
    | [] => 0
    | ((_, _, _, T) :: rest) => T.tRecCount + goInt rest
  goExt : List (Lab × DataSort × SessionType) → Nat
    | [] => 0
    | ((_, _, T) :: rest) => T.tRecCount + goExt rest

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

/-- Adequacy is monotone in fuel. -/
theorem PruneAdequate.mono {p : Role} {lab : Lab} {S : DataSort}
    {T : SessionType} {f f' : Nat} (hle : f ≤ f')
    (h : PruneAdequate p lab S f T) : PruneAdequate p lab S f' T := by
  revert f' hle
  induction h with
  | tEnd fuel =>
    intro f' _
    exact PruneAdequate.tEnd f'
  | tvar fuel X =>
    intro f' _
    exact PruneAdequate.tvar f' X
  | trec_yes hHas hsub ih =>
    intro f' hle
    cases f' with
    | zero => omega
    | succ g =>
      exact PruneAdequate.trec_yes hHas (ih (by omega))
  | trec_vac hfree hsub ih =>
    intro f' hle
    cases f' with
    | zero => omega
    | succ g =>
      exact PruneAdequate.trec_vac hfree (ih (by omega))
  | intC hall ih =>
    intro f' hle
    exact PruneAdequate.intC (fun x hx => ih x hx hle)
  | extC hall ih =>
    intro f' hle
    exact PruneAdequate.extC (fun x hx => ih x hx hle)

/-- Filtering by a fresh variable is the identity. -/
private theorem filter_ne_self {Y : String} {l : List String} (h : Y ∉ l) :
    l.filter (fun x => x != Y) = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd ≠ Y := by
      intro hcon
      subst hcon
      exact h (List.mem_cons.mpr (Or.inl rfl))
    have htl : Y ∉ tl := fun hm => h (List.mem_cons.mpr (Or.inr hm))
    have hbeq : (hd != Y) = true := bne_iff_ne.mpr hhd
    simp only [List.filter_cons, hbeq, ite_true, ih htl]

/-- Head-position variables: variables reachable without crossing a
    choice. Guardedness is exactly absence from this set. -/
def SessionType.headVars : SessionType → List String
  | tEnd => []
  | SessionType.tVar Y => [Y]
  | SessionType.internalChoice _ => []
  | SessionType.externalChoice _ _ => []
  | SessionType.tRec _ B => SessionType.headVars B

/-- Head-`tRec`-spine length: one unfold step strictly decreases
    it, since substitution cannot introduce new head `tRec`s past a guarded
    head position. -/
def SessionType.spine : SessionType → Nat
  | tEnd => 0
  | SessionType.tVar _ => 0
  | SessionType.internalChoice _ => 0
  | SessionType.externalChoice _ _ => 0
  | SessionType.tRec _ B => SessionType.spine B + 1

-- Guardedness is absence at head positions (equation-style recursion:
-- `SessionType` is nested, so the `induction` tactic refuses it).
/-- A guarded variable never occurs in head position. -/
theorem guarded_not_mem_headVars : (B : SessionType) → (X : String) →
    SessionType.Guarded X B → X ∉ B.headVars
  | .tEnd, X, _ => by simp [SessionType.headVars]
  | .tVar Y, X, hG => by simpa [SessionType.headVars, SessionType.Guarded] using hG
  | .internalChoice _, X, _ => by simp [SessionType.headVars]
  | .externalChoice _ _, X, _ => by simp [SessionType.headVars]
  | .tRec Y B', X, hG => by
    simpa [SessionType.headVars, SessionType.Guarded] using
      guarded_not_mem_headVars B' X hG
  termination_by B X hG => sizeOf B
  decreasing_by all_goals simp_wf

-- Substitution past a guarded head position never grows the spine
-- (choices keep head by construction; `tRec` follows the `fv_subst_aux`
-- by-cases pattern).
/-- Substituting outside the head-variable set never grows the spine. -/
theorem spine_subst_le : (C : SessionType) → (X : String) → (T : SessionType) →
    X ∉ C.headVars → (substSessionType C X T).spine ≤ C.spine
  | .tEnd, X, T, _ => by simp [substSessionType]
  | .tVar Y, X, T, h => by
    by_cases hXY : X = Y
    · simp [SessionType.headVars] at h
      exact absurd hXY h
    · simp [substSessionType, hXY]
  | .internalChoice branches, X, T, _ => by simp [substSessionType, SessionType.spine]
  | .externalChoice p branches, X, T, _ => by simp [substSessionType, SessionType.spine]
  | .tRec Y D, X, T, h => by
    by_cases hXY : X = Y
    · simp [substSessionType, hXY]
    · simp only [substSessionType, hXY, ite_false, SessionType.spine]
      exact Nat.add_le_add_right (spine_subst_le D X T h) 1
  termination_by C X T h => sizeOf C
  decreasing_by all_goals simp_wf

-- Every closed contractive type reaches a head-normal form by finitely many
-- top-level unfolds: plain `Nat` induction on a `spine` bound
-- (`≤` form, so the weak successor IH suffices); the `tRec` step uses
-- guardedness for the strict spine drop and closedness to preserve
-- `Contractive` through the substitution (via `IsContractive_subst`).
-- Shadowing-safe: a shadowed unfold returns the body, still smaller.
/-- Every closed contractive type has a head-normal unfold normal form (by fuel-free spine
   induction). -/
lemma unfoldStar_normal_exists : ∀ (T : SessionType), T.Contractive → T.IsClosed →
    ∃ U, UnfoldStar T U ∧ IsHeadNF U := by
  intro T hCo hCl
  suffices key : ∀ (n : Nat) (T : SessionType), T.spine ≤ n → T.Contractive →
      T.IsClosed → ∃ U, UnfoldStar T U ∧ IsHeadNF U from
    key _ _ (Nat.le_refl _) hCo hCl
  intro n
  induction n with
  | zero =>
    intro T hle hCo hCl
    have hz : T.spine = 0 := Nat.le_zero.mp hle
    cases T with
    | tRec X B =>
      simp [SessionType.spine] at hz
    | _ => exact ⟨_, UnfoldStar.refl _, trivial⟩
  | succ n ih =>
    intro T hle hCo hCl
    cases T with
    | tRec X B =>
      cases hCo with
      | tRec hBco hG =>
        set T₁ := substSessionType B X (SessionType.tRec X B) with hT₁
        have hsp : T₁.spine ≤ B.spine :=
          spine_subst_le B X _ (guarded_not_mem_headVars B X hG)
        have hBn : B.spine ≤ n := by
          have hle' : (SessionType.tRec X B).spine ≤ n + 1 := hle
          simp only [SessionType.spine] at hle'
          omega
        have hle₁ : T₁.spine ≤ n := Nat.le_trans hsp hBn
        have hCl₁ : T₁.IsClosed := by
          unfold SessionType.IsClosed
          rw [fv_subst_aux B X (SessionType.tRec X B) hCl]
          simpa [SessionType.IsClosed, SessionType.fv] using hCl
        have hCo₁ : T₁.Contractive :=
          IsContractive_subst hBco (SessionType.Contractive.tRec hBco hG) hCl
        obtain ⟨U, hStar, hnfU⟩ := ih T₁ hle₁ hCo₁ hCl₁
        exact ⟨U, UnfoldStar.step Unfold1.tRec hStar, hnfU⟩
    | _ => exact ⟨_, UnfoldStar.refl _, trivial⟩

/-- Well-formedness survives unfolds (per-step via the subst
    preservations, chained by `UnfoldStar` induction). -/
lemma SessionType.wellFormedUnfold {T U : SessionType}
    (hWF : T.WellFormed) (hS : UnfoldStar T U) : U.WellFormed := by
  induction hS with
  | refl => exact hWF
  | step g _ ih =>
    cases g with
    | @tRec X B =>
      have hWF1 : (substSessionType B X (SessionType.tRec X B)).WellFormed := by
        rcases hWF with ⟨hND, hCl, hCo⟩
        refine ⟨?_, ?_, ?_⟩
        · cases hND with
          | tRec hND0 => exact NoDupl_subst hND0 (SessionType.NoDupl.tRec hND0)
        · unfold SessionType.IsClosed
          rw [fv_subst_aux B X (SessionType.tRec X B) hCl]
          simpa [SessionType.IsClosed, SessionType.fv] using hCl
        · cases hCo with
          | tRec hCo0 hG0 =>
            exact IsContractive_subst hCo0 (SessionType.Contractive.tRec hCo0 hG0) hCl
      exact ih hWF1

/-- Keys half of maximal determinism: two `Nodup` sublists of a `Nodup` source
    with the same membership set are equal as lists. Used to identify maximal
    kept-key lists (coverage + order give the same acceptable set on both
    sides; source `Nodup` kills order variants); kept targets then follow by
    branch determinism for smaller types. -/
lemma nodup_sublist_eq_of_mem_iff {α : Type*} [DecidableEq α]
    {L A B : List α}
    (hL : L.Nodup) (hA : A.Sublist L) (hB : B.Sublist L)
    (hNA : A.Nodup) (hNB : B.Nodup)
    (hset : ∀ a, a ∈ A ↔ a ∈ B) : A = B := by
  revert A B hA hB hNA hNB hset
  induction L with
  | nil =>
    intro A B hA hB hNA hNB hset
    clear hL
    have hA0 : A = [] := List.eq_nil_of_sublist_nil hA
    have hB0 : B = [] := List.eq_nil_of_sublist_nil hB
    rw [hA0, hB0]
  | cons h t ih =>
    intro A B hA hB hNA hNB hset
    have hnt : h ∉ t := (List.nodup_cons.mp hL).1
    have htN : t.Nodup := (List.nodup_cons.mp hL).2
    by_cases hhA : h ∈ A
    · have hhB : h ∈ B := (hset h).mp hhA
      obtain ⟨A', rflA, hsubA⟩ : ∃ A', A = h :: A' ∧ A'.Sublist t := by
        cases hA with
        | cons _ h' =>
          exact absurd (List.Sublist.mem hhA h') hnt
        | cons_cons a h' =>
          exact ⟨_, rfl, h'⟩
      obtain ⟨B', rflB, hsubB⟩ : ∃ B', B = h :: B' ∧ B'.Sublist t := by
        cases hB with
        | cons _ h' =>
          exact absurd (List.Sublist.mem hhB h') hnt
        | cons_cons b h' =>
          exact ⟨_, rfl, h'⟩
      subst rflA
      subst rflB
      have hNA' : A'.Nodup := (List.nodup_cons.mp hNA).2
      have hNB' : B'.Nodup := (List.nodup_cons.mp hNB).2
      have hniA : h ∉ A' := (List.nodup_cons.mp hNA).1
      have hniB : h ∉ B' := (List.nodup_cons.mp hNB).1
      have hset' : ∀ a, a ∈ A' ↔ a ∈ B' := by
        intro a
        by_cases heq : a = h
        · subst heq
          simp [hniA, hniB]
        · simpa [heq] using hset a
      have hEq : A' = B' := ih htN hsubA hsubB hNA' hNB' hset'
      rw [hEq]
    · have hhB : h ∉ B := fun hB' => hhA ((hset h).mpr hB')
      have hAt : A.Sublist t := by
        cases hA with
        | cons _ h' => exact h'
        | cons_cons a h' => exact absurd List.mem_cons_self hhA
      have hBt : B.Sublist t := by
        cases hB with
        | cons _ h' => exact h'
        | cons_cons a h' => exact absurd List.mem_cons_self hhB
      exact ih htN hAt hBt hNA hNB hset

/-- Base yes-derivations have unique targets. -/
lemma mon_tr_yes_base_target_unique {M T1 T2 : SessionType} {γ : ext_tag}
    (h1 : mon_tr_yes_base M γ T1) (h2 : mon_tr_yes_base M γ T2) : T1 = T2 := by
  induction h1 generalizing T2 with
  | intC h_unique h_mem =>
    match h2 with
    | mon_tr_yes_base.intC h_unique' h_mem' =>
      exact unique_target_of_nodup_int h_unique h_mem h_mem'
  | extC h_unique h_mem =>
    match h2 with
    | mon_tr_yes_base.extC h_unique' h_mem' =>
      exact unique_target_of_nodup_ext h_unique h_mem h_mem'
  | tRec h1' ih =>
    match h2 with
    | mon_tr_yes_base.tRec h2' => exact ih h2'

/-- Base-vs-maximal agreement: a base derivation and a maximal derivation from
    the same source agree on the target. Pure structural induction on the
    maximal derivation (no measure, no well-formedness): `base`/`base` is
    `mon_tr_yes_base_target_unique`; `pfx` prunes the base side by tag/source
    unification (`intC` sends vs `recv`, choice-kind mismatch); `unfold`
    pushes the base side through `Base.tRec` into the structural IH. -/
private lemma mon_tr_yes_base_max_unique {T : SessionType} {γ : ext_tag} {V2 : SessionType}
    (hE2 : mon_tr_yes_exist T γ V2) (hM2 : mon_tr_yes_max_deriv hE2)
    {V1 : SessionType} (hb : mon_tr_yes_base T γ V1) : V1 = V2 := by
  induction hM2 with
  | @base T γ V2 h =>
    exact mon_tr_yes_base_target_unique hb h
  | @pfxInt branches kept q lab S T' hne hno hkept hall hNK hkey hallMax hcover horder =>
    cases hb
  | @pfxExt p branches kept q lab S T' hne hneq hkept hall hNK hkey hallMax hcover horder =>
    cases hb with
    | extC _ _ => exact absurd rfl hneq
  | @unfold X B γ V h hmax ih =>
    cases hb with
    | tRec hb' => exact ih hb'

/-- Maximal determinism (full): two maximal derivations from the same
    well-formed source agree on the target. Single structural
    induction on the first maximal derivation, general over the second:
    `base` by `mon_tr_yes_base_max_unique`; `pfx`/`pfx` by keys-half (equal
    kept-lists) plus per-key target equality from the branch IHs that
    `hallMax`-below supplies; `tRec` by `Base.tRec` inversion
    (`base`-vs-`unfold`) and the subterm IH at the substituted body
    (`unfold`-vs-`unfold`, whose `NoDupl` premise closes by
    `NoDupl_subst`). Only `NoDupl` (via `WellFormed`.1) is load-bearing. -/
lemma mon_tr_yes_target_unique {M T1 T2 : SessionType} {γ : ext_tag}
    (hWF : M.WellFormed)
    (h1 : mon_tr_yes M γ T1) (h2 : mon_tr_yes M γ T2) : T1 = T2 := by
  -- Only `NoDupl` (via `WellFormed`.1) is load-bearing below.
  have hND : M.NoDupl := hWF.1
  rcases h1 with ⟨hE1, hM1⟩
  rcases h2 with ⟨hE2, hM2⟩
  -- Single structural induction on the first maximal derivation, general over
  -- the second. `pfx` branch IHs come from `hallMax`-below and `unfold` IHs
  -- from subterms, so no size induction is needed anywhere. Pure term mode
  -- (explicit `fun`s for the recursor's minor premises) keeps every binder
  -- name deterministic.
  refine mon_tr_yes_max_deriv.rec
    (motive := fun {T} {γ} {V} hE hM => T.NoDupl → ∀ (T2 : SessionType)
      (hE2 : mon_tr_yes_exist T γ T2) (hM2 : mon_tr_yes_max_deriv hE2), V = T2)
    (fun {T} {γ} {V} {hb} hND T2 hE2 hM2 => mon_tr_yes_base_max_unique hE2 hM2 hb)
    (fun {branches} {kept1} {q} {labq} {Sq} {X} {hne1} {hno1} {hkept1}
      {hall1} {hNK1} {hkey1} hallMax1 hcover1 horder1 hallMax_ih1 hND T2 hE2 hM2 => by
      cases hM2 with
      | @base _ _ _ hb2 => cases hb2
        | @pfxInt branches kept2 q labq Sq X hne2 hno2 hkept2 hall2 hNK2 hkey2 hallMax2 hcover2 horder2 =>
          have hNDt : List.Nodup (branches.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1))) :=
            SessionType.NoDupl.triple_nodup_of_internalChoice hND
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
              have hND0 : T0a.NoDupl := noDupl_of_mem_intBranches hND hmemB
              -- Branch targets closed by the structural IH from `hallMax`-below.
              have hTgt : T1i = T2i :=
                hallMax_ih1 T0a T1i r l s hmemB hmemK1 hsubE1 hND0 T2i hsubE2 hsubM2
              -- Goal was already substituted to tuples by `match`; close by congruence.
              exact congrArg (fun T => (r, l, s, T)) hTgt
          rw [hkept1, hkept2, hkeptEq])
    (fun {p} {branches} {kept1} {q} {lab} {S} {X} {hne1} {hneq1} {hkept1}
      {hall1} {hNK1} {hkey1} hallMax1 hcover1 horder1 hallMax_ih1 hND T2 hE2 hM2 => by
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
              have hsubM1 := hallMax1 T0a T1i l s hmemB hmemK1 hsubE1
              have hsubE2 := hall2 T0a T2i l s hmemB hmemK2
              have hsubM2 := hallMax2 T0a T2i l s hmemB hmemK2 hsubE2
              have hND0 : T0a.NoDupl := noDupl_of_mem_extBranches hND hmemB
              -- Branch targets closed by the structural IH from `hallMax`-below.
              have hTgt : T1i = T2i :=
                hallMax_ih1 T0a T1i l s hmemB hmemK1 hsubE1 hND0 T2i hsubE2 hsubM2
              exact congrArg (fun T => (l, s, T)) hTgt
          rw [hkept1, hkept2, hkeptEq])
    (fun {X} {B} {γ} {V} {h} hmax ih hNDu _ hE2 hM2 => by
      -- Both sides start at `tRec`: `base` inverts through `Base.tRec`
      -- (closed by `mon_tr_yes_base_max_unique`); `unfold` steps to subderivations
      -- closed by the structural IH (`NoDupl` premise via `NoDupl_subst`).
      cases hM2 with
      | @base _ _ _ hb2 =>
        cases hb2 with
        | tRec hsub2 => exact (mon_tr_yes_base_max_unique h hmax hsub2).symm
      | @unfold _ _ _ _ hsub2 hmax2 =>
        have hNDsub : (substSessionType B X (SessionType.tRec X B)).NoDupl := by
          cases hNDu with
          | tRec hND0 => exact NoDupl_subst hND0 (SessionType.NoDupl.tRec hND0)
        exact ih hNDsub _ hsub2 hmax2)
    hM1 hND T2 hE2 hM2

/-- Queue-value uniqueness (WellFormed source): fold determinism by queue
    induction, stepping with general `mon_tr_yes_target_unique` and threading
    `WellFormed` through `mon_tr_yes_preserves_wf`. -/
lemma monitor_fold_aux_value_unique : ∀ (Q : Queue) (T T1 T2 : SessionType),
    T.WellFormed → monitor_fold_aux Q T T1 → monitor_fold_aux Q T T2 → T1 = T2 := by
  intro Q
  induction Q with
  | nil =>
    intro T T1 T2 hWF h1 h2
    simp only [monitor_fold_aux] at h1 h2
    subst h1
    subst h2
    rfl
  | cons msg rest ih =>
    intro T T1 T2 hWF h1 h2
    rcases msg with ⟨p, lab, S⟩
    simp only [monitor_fold_aux] at h1 h2
    obtain ⟨mid1, hyes1, hrest1⟩ := h1
    obtain ⟨mid2, hyes2, hrest2⟩ := h2
    have hmid : mid1 = mid2 := mon_tr_yes_target_unique hWF hyes1 hyes2
    subst hmid
    have hWFm := mon_tr_yes_preserves_wf hyes1 hWF
    exact ih _ _ _ hWFm hrest1 hrest2

/-- Queue value from a well-formed entry: same proof via general
    `monitor_fold_aux_value_unique`. -/
lemma monitor_fold_val_partial_eq_of_monitor_fold {stq : SessionTypeWithQueue} {M : SessionType}
    (hWF : stq.1.WellFormed)
    (h : monitor_fold stq M) : monitor_fold_val_partial stq = some M := by
  unfold monitor_fold_val_partial
  classical
  have h_ex : ∃ T', monitor_fold stq T' := ⟨M, h⟩
  simp [h_ex]
  exact monitor_fold_aux_value_unique stq.2 stq.1 (Classical.choose h_ex) M hWF
    (Classical.choose_spec h_ex) h

/-- A successful partial queue evaluation agrees with the relational queue semantics. -/
lemma monitor_fold_val_partial_eq_of_some {stq : SessionTypeWithQueue} {M : SessionType}
    (h : monitor_fold_val_partial stq = some M) : monitor_fold stq M := by
  unfold monitor_fold_val_partial at h
  classical
  by_cases h_ex : ∃ T', monitor_fold stq T'
  · simp [h_ex] at h
    rw [← h]
    exact Classical.choose_spec h_ex
  · simp [h_ex] at h

/-- Queue folds split over concatenation: folding `A ++ B` goes through an intermediate type. -/
lemma monitor_fold_aux_append_iff {A B : Queue} {T M : SessionType} :
    monitor_fold_aux (A ++ B) T M ↔ ∃ U, monitor_fold_aux A T U ∧ monitor_fold_aux B U M := by
  constructor
  · intro h
    induction A generalizing T M with
    | nil =>
        simp at h
        refine ⟨T, by simp [monitor_fold_aux], h⟩
    | cons msg A' ih =>
        rcases msg with ⟨p, lab, S⟩
        simp only [List.cons_append] at h
        rcases h with ⟨T1, h_yes1, h_rest1⟩
        rcases ih h_rest1 with ⟨U, hA', hB⟩
        refine ⟨U, ?_, hB⟩
        exact ⟨T1, h_yes1, hA'⟩
  · rintro ⟨U, hA, hB⟩
    induction A generalizing T with
    | nil =>
        simp [monitor_fold_aux] at hA
        subst U
        simpa [monitor_fold_aux] using hB
    | cons msg A' ih =>
        rcases msg with ⟨p, lab, S⟩
        rcases hA with ⟨T1, h_yes1, hA'⟩
        have hint : monitor_fold_aux (A' ++ B) T1 M := ih hA'
        exact ⟨T1, h_yes1, hint⟩

/-- The confluence diamond at an internal choice: a receive through the choice
    prefixes an output step of the choice (STMon-IntPfx vs. S-IntC).

    RESTATED (queue-contextual): the bare version is FALSE — the maximal
    receive transition can prune the very branch that enables the output step.
    The true version carries the extra hypothesis `h_acc` that
    the out-branch target also accepts the receive; then coverage forces the
    out-branch to be kept, and the diamond goes through with no determinism
    or well-formedness needed (existence only). -/
lemma intPfx_diamond {branches : List (Role × Lab × DataSort × SessionType)}
    {T' X : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    {q : Role} {labq : Lab} {Sq : DataSort}
    (hST : st_trans (SessionType.internalChoice branches) (st_label.out p lab S) T')
    (h_rec : mon_tr_yes (SessionType.internalChoice branches) (ext_tag.recv q labq Sq) X)
    (h_acc : ∃ X', mon_tr_yes_exist T' (ext_tag.recv q labq Sq) X') :
    ∃ (X' : SessionType),
      st_trans X (st_label.out p lab S) X' ∧ mon_tr_yes T' (ext_tag.recv q labq Sq) X' := by
  cases hST with
  | intC hSrcMem =>
    rcases h_rec with ⟨hE, hM⟩
    cases hM with
    | @base _ _ _ hb => cases hb
    | @pfxInt branches kept q labq Sq X hne hno hkept hall hNodupKept hkey hallMax hcover horder =>
      rcases h_acc with ⟨_, hAccE⟩
      rcases hcover p lab S T' hSrcMem ⟨_, hAccE⟩ with ⟨T1, hKeptMem⟩
      have hsubE := hall T' T1 p lab S hSrcMem hKeptMem
      have hsubM := hallMax T' T1 p lab S hSrcMem hKeptMem hsubE
      refine ⟨T1, ?_, ⟨hsubE, hsubM⟩⟩
      rw [hkept]
      exact st_trans.intC hKeptMem

/-- Chained `mon_tr_yes` transitions over tag sequences (paper `yes(ρ̃)`). -/
inductive mon_yes_seq : SessionType → List ext_tag → SessionType → Prop where
  | refl (T) : mon_yes_seq T [] T
  | step {T Tmid T' : SessionType} {γ : ext_tag} {ρ : List ext_tag}
      (h1 : mon_tr_yes T γ Tmid) (h2 : mon_yes_seq Tmid ρ T') : mon_yes_seq T (γ :: ρ) T'

/-- Queue folds replay as yes-sequences. Induction on the queue (data)
    generalizing endpoints. -/
lemma monitor_fold_aux_to_mon_yes_seq {Q : Queue} {T M : SessionType}
    (h : monitor_fold_aux Q T M) :
    mon_yes_seq T (Q.map (fun m => match m with
      | QueueMessage.msg p lab S => ext_tag.recv p lab S)) M := by
  induction Q generalizing T M with
  | nil =>
    simp [monitor_fold_aux] at h
    subst h
    exact mon_yes_seq.refl _
  | cons msg rest ih =>
    rcases msg with ⟨p, lab, S⟩
    simp only [monitor_fold_aux] at h
    obtain ⟨Tmid, hYes, hRest⟩ := h
    simpa using mon_yes_seq.step hYes (ih hRest)

/-- Sequence splitting at a tag-list append (converse of transitivity;
    mirror of `stSeq_split` for monitor sequences; pure list induction). -/
lemma mon_yes_seq_split {T T' : SessionType} {ρ1 ρ2 : List ext_tag}
    (h : mon_yes_seq T (ρ1 ++ ρ2) T') :
    ∃ Tmid, mon_yes_seq T ρ1 Tmid ∧ mon_yes_seq Tmid ρ2 T' := by
  induction ρ1 generalizing T T' with
  | nil =>
    simpa using ⟨T, mon_yes_seq.refl _, h⟩
  | cons γ ρ1s ih =>
    cases h with
    | step h1 hTail =>
      obtain ⟨Tmid, hFirst, hSecond⟩ := ih hTail
      exact ⟨Tmid, mon_yes_seq.step h1 hFirst, hSecond⟩






/-- Deep no-`p`-sender predicate: no `internalChoice` anywhere in `T`
    offers a branch from role `p` (so no base-`intC` send from `p` can
    fire at any subterm). Structural over subterms only (no substitution,
    no measures); `extC`/`tEnd`/`tVar` need no side conditions (sends
    never fire there by tag/source mismatch). `tRec`-containing types are
    simply unclassifiable (they may unfold to sends) — no `tRec` arm. -/
inductive NoSendRole (p : Role) : SessionType → Prop where
  | tEnd : NoSendRole p SessionType.tEnd
  | tvar (X : String) : NoSendRole p (SessionType.tVar X)
  | intC {branches : List (Role × Lab × DataSort × SessionType)}
      (hno : ∀ x ∈ branches, x.1 ≠ p)
      (ih : ∀ x ∈ branches, NoSendRole p x.2.2.2) :
    NoSendRole p (SessionType.internalChoice branches)
  | extC {r : Role} {branches : List (Lab × DataSort × SessionType)}
      (ih : ∀ x ∈ branches, NoSendRole p x.2.2) :
    NoSendRole p (SessionType.externalChoice r branches)


/-- Well-formedness persists along τ-stars (via public
    `Network.wellFormedPreserved`). -/
lemma wf_star {N Ni : Network}
    (hWF : N.WellFormed) (hStar : net_trans_star N Ni) : Ni.WellFormed := by
  revert hWF
  induction hStar with
  | refl =>
    intro hWF
    exact hWF
  | step hInt hTr _ ih =>
    intro hWF
    exact ih (Network.wellFormedPreserved _ _ _ hWF hTr hInt)

/-- Sequence-to-fold: a tag-mapped queue sequence replays as a queue fold. -/
lemma mon_yes_seq_to_monitor_fold_aux {Q : Queue} {T M : SessionType}
    (h : mon_yes_seq T (Q.map fun m => match m with
      | QueueMessage.msg p lab S => ext_tag.recv p lab S) M) :
    monitor_fold_aux Q T M := by
  induction Q generalizing T M with
  | nil =>
    cases h with
    | refl => simp [monitor_fold_aux]
  | cons msg rest ih =>
    rcases msg with ⟨p, lab, S⟩
    simp only [List.map_cons] at h
    cases h with
    | step hYes hTail => exact ⟨_, hYes, ih hTail⟩

/-- Overapprox steps preserve session well-formedness (all three rules
    carry an `st_trans` step on the session component). -/
lemma over_trans_preserves_wf {stq stq' : SessionTypeWithQueue} {α : st_label}
    (h : over_trans stq α stq') (hWF : stq.1.WellFormed) : stq'.1.WellFormed := by
  induction h with
  | @dequeue T T' Q Q' p lab S branches hEq hmem hQ =>
    subst hEq
    exact SessionType.wellFormedPreserved _ _ _
      hWF (st_trans.extC (p := p) hmem)
  | @specInp T T' Q p lab S branches hEq hmem hAbs =>
    subst hEq
    exact SessionType.wellFormedPreserved _ _ _
      hWF (st_trans.extC (p := p) hmem)
  | sendFresh hEq hST hFresh => exact SessionType.wellFormedPreserved _ _ _ hWF hST
  | tauUnfold hU =>
    exact SessionType.wellFormedUnfold hWF (UnfoldStar.step hU (UnfoldStar.refl _))

/-- Labelled reflexive-transitive closure of `over_trans`: `n` transitions as
    an explicit trace `ρ` (the paper's "via n transitions"). -/
inductive over_trans_trace : SessionTypeWithQueue → List st_label → SessionTypeWithQueue → Prop where
  | refl (stq : SessionTypeWithQueue) : over_trans_trace stq [] stq
  | step {stq stq' stq'' : SessionTypeWithQueue} {α : st_label} {ρ : List st_label}
    (h : over_trans stq α stq') (hT : over_trans_trace stq' ρ stq'') :
    over_trans_trace stq (α :: ρ) stq''

/-- Head-dequeue preserves absorption with the SAME monitor: the `st_trans`
    input lifts (`st_trans_inp_imp_mon_tr_yes`) and determinism pins it to
    the absorption's first step; the tail is the post-state absorption. -/
lemma dequeue_head_preserves_absorption {T T' : SessionType} {Q' : Queue}
    {M : SessionType} {p : Role} {lab : Lab} {S : DataSort}
    (hWF : T.WellFormed)
    (hEnc : monitor_fold (T, QueueMessage.msg p lab S :: Q') M)
    (hST : st_trans T (st_label.inp p lab S) T') :
    monitor_fold (T', Q') M := by
  have hSeq : mon_yes_seq T (ext_tag.recv p lab S ::
      (Q'.map fun m => match m with
        | QueueMessage.msg p lab S => ext_tag.recv p lab S)) M := by
    simpa using monitor_fold_aux_to_mon_yes_seq hEnc
  cases hSeq with
  | step hYes hTail =>
    have hL := st_trans_inp_imp_mon_tr_yes hST hWF
    have heq : T' = _ := mon_tr_yes_target_unique hWF hL hYes
    subst heq
    exact mon_yes_seq_to_monitor_fold_aux hTail


/-!
# Deep-drainability core (shared, recursion-agnostic).

The choice-function core `CanAlwaysDrainInternalDeepCore` and its existential form
`CanAlwaysDrainInternalDeep`, the `NoDequeueFrom` guard, and the queue-scan
helpers `Queue.dequeue_head_hit` / `overTrTrace_nil_eq`. None of these
assumes `NoRec` or vacuous recursion (the `tRec` arms are handled as
ordinary cases); they are needed both by `monitor_soundness` and by the
`Nest.NoRec` soundness chain.
-/

-- ================================================================
-- Queue-scan structure (head hits, same-sender blocking).
-- ================================================================

/-- Dequeuing the head always succeeds, dropping it. -/
theorem Queue.dequeue_head_hit {d : QueueMessage} {rest : Queue} :
    Queue.dequeue (d :: rest) d = some rest := by
  simp [Queue.dequeue, Queue.dequeue.go]

-- ================================================================
-- Internal-choice-robust drainage.
-- ================================================================


/-- No dequeue step is available from `(Tᵢ, Qᵢ)`: no `st_trans` input target
    pairs with a successful queue scan for the same message. -/
def NoDequeueFrom (Ti : SessionType) (Qi : Queue) : Prop :=
  ¬ ∃ (T' : SessionType) (Q' : Queue) (r : Role) (lab : Lab) (S : DataSort),
    st_trans Ti (st_label.inp r lab S) T' ∧ Qi.dequeue (QueueMessage.msg r lab S) = some Q'

/-- Core of deep internal drainability below: same statement, except the
    per-site external-choice witness is supplied by an explicit choice
    function rather than a per-site existential, because the kernel
    rejects `∃`/`∧` wrapping the recursive occurrence when their payload
    mentions local variables. Classically equivalent to the existential
    form via `Classical.choice` (in the ambient axiom set). -/
inductive CanAlwaysDrainInternalDeepCore : SessionType → Queue → Prop where
  | mk (T0 : SessionType) (Q0 : Queue) (Tn : SessionType) (ρ : List st_label)
      (choice : SessionType → Queue → Role →
        List (Lab × DataSort × SessionType) → Lab × DataSort × SessionType) :
      over_trans_trace (T0, Q0) ρ (Tn, []) →
      (∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label),
        over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
        over_trans_trace (Ti, Qi) ρ2 (Tn, []) →
        ρ = ρ1 ++ ρ2 →
        ∀ (branches : List (Role × Lab × DataSort × SessionType)),
          Ti = SessionType.internalChoice branches → branches ≠ [] →
          ∀ (br : Role × Lab × DataSort × SessionType),
            br ∈ branches → CanAlwaysDrainInternalDeepCore br.2.2.2 Qi) →
      (∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label) (p : Role)
        (branches : List (Lab × DataSort × SessionType)),
        over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
        over_trans_trace (Ti, Qi) ρ2 (Tn, []) →
        ρ = ρ1 ++ ρ2 → Ti = SessionType.externalChoice p branches →
        branches ≠ [] → NoDequeueFrom Ti Qi →
        choice Ti Qi p branches ∈ branches) →
      (∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label)
        (p : Role) (branches : List (Lab × DataSort × SessionType)),
        over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
        over_trans_trace (Ti, Qi) ρ2 (Tn, []) →
        ρ = ρ1 ++ ρ2 → Ti = SessionType.externalChoice p branches →
        branches ≠ [] → NoDequeueFrom Ti Qi →
        CanAlwaysDrainInternalDeepCore (choice Ti Qi p branches).2.2 Qi) →
      (∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label)
        (X : String) (B : SessionType),
        over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
        over_trans_trace (Ti, Qi) ρ2 (Tn, []) →
        ρ = ρ1 ++ ρ2 → Ti = SessionType.tRec X B →
        CanAlwaysDrainInternalDeepCore B Qi) →
      CanAlwaysDrainInternalDeepCore T0 Q0

/-- Deep internal drainability: a witness `over_trans` trace (`st_label`s are
    the approx-labels) from `(T₀, Q₀)` to an empty queue, such that every
    state `(Tᵢ, Qᵢ)` lying on that trace (including the endpoints, i.e.
    `0..n` rather than `1..n`) satisfies: every `internalChoice`-branch
    target is deep for the same queue; and every `externalChoice` that
    admits no dequeue step from `Qᵢ` has some branch target deep for the
    same queue (the spec's `Qⱼ` is read as `Qᵢ`, since `j` ranges over
    branches, not trace positions). Stated over the choice-function core
    above, so only `∀`/`→` guard the recursion. -/
def CanAlwaysDrainInternalDeep (T0 : SessionType) (Q0 : Queue) : Prop :=
  ∃ (Tn : SessionType) (ρ : List st_label),
    over_trans_trace (T0, Q0) ρ (Tn, []) ∧
    ∀ (Ti : SessionType) (Qi : Queue) (ρ1 ρ2 : List st_label),
      over_trans_trace (T0, Q0) ρ1 (Ti, Qi) →
      over_trans_trace (Ti, Qi) ρ2 (Tn, []) →
      ρ = ρ1 ++ ρ2 →
      ((∀ (branches : List (Role × Lab × DataSort × SessionType)),
        Ti = SessionType.internalChoice branches → branches ≠ [] →
        ∀ (br : Role × Lab × DataSort × SessionType),
          br ∈ branches → CanAlwaysDrainInternalDeepCore br.2.2.2 Qi) ∧
      (∀ (p : Role) (branches : List (Lab × DataSort × SessionType)),
        Ti = SessionType.externalChoice p branches → branches ≠ [] →
        NoDequeueFrom Ti Qi →
        ∃ (br : Lab × DataSort × SessionType),
          br ∈ branches ∧ CanAlwaysDrainInternalDeepCore br.2.2 Qi) ∧
      (∀ (X : String) (B : SessionType),
        Ti = SessionType.tRec X B →
        CanAlwaysDrainInternalDeepCore B Qi))

/-- A nil-label overapprox trace is equality. -/
theorem overTrTrace_nil_eq {stq stq' : SessionTypeWithQueue}
    (hT : over_trans_trace stq [] stq') : stq' = stq := by
  cases hT
  case refl _ => rfl
