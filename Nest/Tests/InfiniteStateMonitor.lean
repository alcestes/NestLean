import Nest.MonitorCo
import Nest.MonitorCoFun
import Nest.SessionUtils

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# Infinite-state monitors (paper `ex:infinite-state-monitor`).

The session type `T = μX. ?Q.a ; ?P.b ; X` yields a monitor with infinitely
many states: each `?P.b` accepted while an input from `Q` is still pending
prunes the `Q`-branch but keeps the pending `?Q.a` expectation, so repeated
`?P.b` inputs pile up unboundedly many leading `?Q.a` prefixes.

This file mechanises that example with the coinductive monitor relation
(`mon_tr_yes_co` in `Nest/MonitorCo.lean`):
* `InfT` is the paper's session type (`μX. ?Q.a ; ?P.b ; X`);
* `InfU n` is the monitor state after `n` early `?P.b` inputs, i.e. `n`
  copies of `?Q.a` followed by `InfT`;
* `InfU_co_step` shows every `InfU n` accepts `?P.b` and moves to
  `InfU (n + 1)` (the paper's derivation, iterated);
* `InfU1_accept_a` shows the monitor can then accept the pending `?Q.a`
  and return to the original state;
* `InfU_fresh` shows every iterate differs from all earlier ones, and
  `InfU_reachable` shows every iterate is reachable, so the reachable
  monitor states are infinite.
-/

-- ================================================================
-- The session type from the paper and its iterates.
-- ================================================================

section InfiniteStateDef

/-- Body of the paper example: `?Q.a ; ?P.b ; X`. -/
private def InfBody : SessionType :=
  SessionType.externalChoice "Q" [("a", "S", SessionType.externalChoice "P" [("b", "S", SessionType.tVar "X")])]

/-- The paper example: `T = μX. ?Q.a ; ?P.b ; X`. -/
private def InfT : SessionType := SessionType.tRec "X" InfBody

/-- One unfolding of `InfT`: `?Q.a ; ?P.b ; T`. -/
private def InfUnfold : SessionType :=
  SessionType.externalChoice "Q" [("a", "S", SessionType.externalChoice "P" [("b", "S", InfT)])]

/-- The `?P.b ; T` continuation inside the unfolding. -/
private def InfMid : SessionType :=
  SessionType.externalChoice "P" [("b", "S", InfT)]

/-- Monitor states after `n` early `?P.b` inputs: `n` copies of `?Q.a`
    followed by `InfT`. In particular `InfU 0 = InfT`, and each further
    `?P.b` acceptance prepends one more `?Q.a` (paper derivation). -/
private def InfU : Nat → SessionType
  | 0 => InfT
  | n + 1 => SessionType.externalChoice "Q" [("a", "S", InfU n)]

/-- Monitor label for an incoming `b` from `P`. -/
private def gPb : ext_tag := ext_tag.recv "P" "b" "S"

/-- Monitor label for an incoming `a` from `Q`. -/
private def gQa : ext_tag := ext_tag.recv "Q" "a" "S"

/-- One-step unfold of the recursive type. -/
private theorem InfUnfold_eq :
    substSessionType InfBody "X" (SessionType.tRec "X" InfBody) = InfUnfold := by
  decide

end InfiniteStateDef

-- ================================================================
-- Well-formedness of the corpus.
-- ================================================================

section InfiniteStateWF

private theorem InfT_wf : InfT.WellFormed := SessionType.wfCheck_sound (by decide)

private theorem InfMid_wf : InfMid.WellFormed := SessionType.wfCheck_sound (by decide)

private theorem InfUnfold_wf : InfUnfold.WellFormed := SessionType.wfCheck_sound (by decide)

/-- Every iterate is well-formed (by induction: singleton external choices
    preserve `NoDupl`, closedness, and contractiveness). -/
private theorem InfU_wf : ∀ n, (InfU n).WellFormed := by
  intro n
  induction n with
  | zero => exact InfT_wf
  | succ n ih =>
    show (SessionType.externalChoice "Q" [("a", "S", InfU n)]).WellFormed
    rcases ih with ⟨ihND, ihCl, ihCo⟩
    refine ⟨?_, ?_, ?_⟩
    · apply SessionType.NoDupl.externalChoice
      · simp only [List.map_cons, List.map_nil]
        exact List.nodup_singleton _
      · simp
      · intro x hx
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        exact ihND
    · have hfv : (SessionType.externalChoice "Q" [("a", "S", InfU n)]).fv
          = (InfU n).fv := by
        simp only [SessionType.fv, SessionType.fv.goExt, List.append_nil]
      unfold SessionType.IsClosed
      rw [hfv]
      exact ihCl
    · apply SessionType.Contractive.externalChoice
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact ihCo

end InfiniteStateWF

-- ================================================================
-- The monitor accepts `?P.b` in every iterate (finite derivations).
-- This is the induction infrastructure for the coinductive step below.
-- ================================================================

section InfiniteStateExist

/-- Finite acceptance: `InfU n` accepts `?P.b` and moves to `InfU (n + 1)`. -/
private theorem InfU_exist_step : ∀ n, mon_tr_yes_exist (InfU n) gPb (InfU (n + 1)) := by
  intro n
  induction n with
  | zero =>
    -- `T --P.b--> ?Q.a ; T` via `unfold` then `pfxExt` (paper derivation).
    show mon_tr_yes_exist (SessionType.tRec "X" InfBody) gPb (InfU (0 + 1))
    refine mon_tr_yes_exist.unfold (X := "X") (B := InfBody) ?_
    rw [show substSessionType InfBody "X" (SessionType.tRec "X" InfBody) = InfUnfold from
      InfUnfold_eq]
    show mon_tr_yes_exist
      (SessionType.externalChoice "Q" [("a", "S", InfMid)]) gPb (InfU (0 + 1))
    refine mon_tr_yes_exist.pfxExt (branches := [("a", "S", InfMid)])
      (kept := [("a", "S", InfT)]) (q := "P") (lab := "b") (S := "S")
      (hkept := rfl) ?_ ?_ ?_ ?_ ?_
    · exact ⟨by decide, by decide⟩
    · decide
    · intro T0 T1 l s hB hK
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB hK
      obtain ⟨rfl, rfl, rfl⟩ := hB
      obtain ⟨rfl, rfl, rfl⟩ := hK
      exact mon_tr_yes_exist.base
        (mon_tr_yes_base.extC (by decide) (by simp))
    · simp
    · intro l s T1 hK
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      obtain ⟨rfl, rfl, rfl⟩ := hK
      exact ⟨InfMid, by simp⟩
  | succ n ih =>
    -- `?Q.a ; (InfU n) --P.b--> ?Q.a ; (InfU (n+1))`, reusing the IH.
    show mon_tr_yes_exist (SessionType.externalChoice "Q" [("a", "S", InfU n)]) gPb
      (SessionType.externalChoice "Q" [("a", "S", InfU (n + 1))])
    refine mon_tr_yes_exist.pfxExt (branches := [("a", "S", InfU n)])
      (kept := [("a", "S", InfU (n + 1))]) (q := "P") (lab := "b") (S := "S")
      (hkept := rfl) ?_ ?_ ?_ ?_ ?_
    · exact ⟨by simp, by simp⟩
    · decide
    · intro T0 T1 l s hB hK
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB hK
      obtain ⟨rfl, rfl, rfl⟩ := hB
      obtain ⟨rfl, rfl, rfl⟩ := hK
      exact ih
    · simp
    · intro l s T1 hK
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      obtain ⟨rfl, rfl, rfl⟩ := hK
      exact ⟨InfU n, by simp⟩

end InfiniteStateExist

-- ================================================================
-- Coinductive derivation: every iterate accepts `?P.b`.
-- The invariant covers the whole chain at once (as in `t07_sound_qx`):
-- the `n`-th point goes via `recL` for `n = 0` and via `pfxExt` otherwise,
-- and the unfolded source goes via `pfxExt` to the base step.
-- ================================================================

section InfiniteStateCo

/-- Coinduction invariant: points along the infinite `?P.b`-chain plus the
    two auxiliary points of the first step (unfolded source, base target). -/
private def InfInv : SessionType → ext_tag → SessionType → Prop :=
  fun T γ V =>
    (∃ n, T = InfU n ∧ γ = gPb ∧ V = InfU (n + 1))
      ∨ (T = InfUnfold ∧ γ = gPb ∧ V = InfU 1)
      ∨ (T = InfMid ∧ γ = gPb ∧ V = InfT)

/-- The invariant is closed under the coinductive rules. -/
private theorem InfInv_closed : ∀ a a_1 a_2, InfInv a a_1 a_2 →
    a.WellFormed ∧ mon_tr_yes_base a a_1 a_2 ∨
    (∃ branches kept q lab S, (SessionType.internalChoice branches).WellFormed ∧
      (branches ≠ [] ∧ kept ≠ [])
      ∧ (∀ p' lab' S' T0, (p', lab', S', T0) ∈ branches → q ≠ p')
        ∧ (∀ T0 T1 r l s, (r, l, s, T0) ∈ branches → (r, l, s, T1) ∈ kept →
          InfInv T0 (ext_tag.recv q lab S) T1)
        ∧ (∀ r l s T1, (r, l, s, T1) ∈ kept →
          ∃ T0, (r, l, s, T0) ∈ branches ∧
            ∃ V, mon_tr_yes_exist T0 (ext_tag.recv q lab S) V)
        ∧ (∀ r l s T0, (r, l, s, T0) ∈ branches →
          (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) → ∃ T1, (r, l, s, T1) ∈ kept)
        ∧ List.Sublist (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
          (branches.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1, x.2.2.1)))
        ∧ a = SessionType.internalChoice branches ∧ a_1 = ext_tag.recv q lab S ∧
        a_2 = SessionType.internalChoice kept) ∨
    (∃ p branches kept q lab S, (SessionType.externalChoice p branches).WellFormed ∧
      (branches ≠ [] ∧ kept ≠ []) ∧ q ≠ p ∧
        (∀ T0 T1 l s, (l, s, T0) ∈ branches → (l, s, T1) ∈ kept →
          InfInv T0 (ext_tag.recv q lab S) T1) ∧
        (∀ l s T1, (l, s, T1) ∈ kept →
          ∃ T0, (l, s, T0) ∈ branches ∧
            ∃ V, mon_tr_yes_exist T0 (ext_tag.recv q lab S) V) ∧
        (∀ l s T0, (l, s, T0) ∈ branches →
          (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv q lab S) T1) → ∃ T1, (l, s, T1) ∈ kept) ∧
        List.Sublist (kept.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1)))
          (branches.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))) ∧
        a = SessionType.externalChoice p branches ∧ a_1 = ext_tag.recv q lab S ∧
        a_2 = SessionType.externalChoice p kept) ∨
    (∃ X B, (SessionType.tRec X B).WellFormed ∧
      InfInv (substSessionType B X (SessionType.tRec X B)) a_1 a_2 ∧
      a = SessionType.tRec X B) ∨
    ∃ Y C, a.WellFormed ∧
      InfInv a a_1 (substSessionType C Y (SessionType.tRec Y C)) ∧
      a_2 = SessionType.tRec Y C := by
  intro a a_1 a_2 h
  unfold InfInv at h
  rcases h with ⟨n, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- Main chain point `(InfU n, gPb, InfU (n + 1))`.
    cases n with
    | zero =>
      -- `T --P.b--> ?Q.a ; T` via `recL` (paper derivation, outer step).
      right; right; right; left
      refine ⟨"X", InfBody, InfT_wf, ?_, rfl⟩
      have hsub : substSessionType InfBody "X" (SessionType.tRec "X" InfBody) = InfUnfold :=
        InfUnfold_eq
      rw [hsub]
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    | succ n =>
      -- `?Q.a ; (InfU n) --P.b--> ?Q.a ; (InfU (n+1))` via `pfxExt`.
      right; right; left
      have hWF' : (SessionType.externalChoice "Q" [("a", "S", InfU n)]).WellFormed :=
        InfU_wf (n + 1)
      have hhall' : ∀ T0 T1 l s, (l, s, T0) ∈ [("a", "S", InfU n)] →
          (l, s, T1) ∈ [("a", "S", InfU (n + 1))] →
          InfInv T0 (ext_tag.recv "P" "b" "S") T1 := by
        intro T0 T1 l s hB hK
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB hK
        obtain ⟨rfl, rfl, rfl⟩ := hB
        obtain ⟨rfl, rfl, rfl⟩ := hK
        exact Or.inl ⟨n, rfl, rfl, rfl⟩
      have hkey' : ∀ l s T1, (l, s, T1) ∈ [("a", "S", InfU (n + 1))] →
          ∃ T0, (l, s, T0) ∈ [("a", "S", InfU n)] ∧
            ∃ V, mon_tr_yes_exist T0 (ext_tag.recv "P" "b" "S") V := by
        intro l s T1 hK
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
        obtain ⟨rfl, rfl, rfl⟩ := hK
        exact ⟨InfU n, by simp, _, InfU_exist_step n⟩
      have hcover' : ∀ l s T0, (l, s, T0) ∈ [("a", "S", InfU n)] →
          (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "P" "b" "S") T1) →
          ∃ T1, (l, s, T1) ∈ [("a", "S", InfU (n + 1))] := by
        intro l s T0 hB _
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB ⊢
        obtain ⟨rfl, rfl, rfl⟩ := hB
        exact ⟨InfU (n + 1), by simp⟩
      have horder' : List.Sublist
          (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
            [("a", "S", InfU (n + 1))])
          (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
            [("a", "S", InfU n)]) := by
        simp only [List.map_cons, List.map_nil]
        exact List.Sublist.refl _
      exact ⟨"Q", [("a", "S", InfU n)], [("a", "S", InfU (n + 1))],
        "P", "b", "S", hWF', ⟨by simp, by simp⟩, by decide,
        hhall', hkey', hcover', horder', rfl, rfl, rfl⟩
  · -- Unfolded source: `pfxExt` keeping the single branch, base subproof.
    right; right; left
    have hhallU : ∀ T0 T1 l s, (l, s, T0) ∈ [("a", "S", InfMid)] →
        (l, s, T1) ∈ [("a", "S", InfT)] →
        InfInv T0 (ext_tag.recv "P" "b" "S") T1 := by
      intro T0 T1 l s hB hK
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB hK
      obtain ⟨rfl, rfl, rfl⟩ := hB
      obtain ⟨rfl, rfl, rfl⟩ := hK
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
    have hkeyU : ∀ l s T1, (l, s, T1) ∈ [("a", "S", InfT)] →
        ∃ T0, (l, s, T0) ∈ [("a", "S", InfMid)] ∧
          ∃ V, mon_tr_yes_exist T0 (ext_tag.recv "P" "b" "S") V := by
      intro l s T1 hK
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
      obtain ⟨rfl, rfl, rfl⟩ := hK
      have hmemB : ("a", "S", InfMid) ∈ [("a", "S", InfMid)] := by simp
      have hmemB2 : ("b", "S", InfT) ∈ [("b", "S", InfT)] := by simp
      exact ⟨InfMid, hmemB, _, mon_tr_yes_exist.base
        (mon_tr_yes_base.extC (by decide) hmemB2)⟩
    have hcoverU : ∀ l s T0, (l, s, T0) ∈ [("a", "S", InfMid)] →
        (∃ T1, mon_tr_yes_exist T0 (ext_tag.recv "P" "b" "S") T1) →
        ∃ T1, (l, s, T1) ∈ [("a", "S", InfT)] := by
      intro l s T0 hB _
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB ⊢
      obtain ⟨rfl, rfl, rfl⟩ := hB
      exact ⟨InfT, by simp⟩
    have horderU : List.Sublist
        (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
          [("a", "S", InfT)])
        (List.map (fun x : Lab × DataSort × SessionType => (x.1, x.2.1))
          [("a", "S", InfMid)]) := by
      simp only [List.map_cons, List.map_nil]
      exact List.Sublist.refl _
    exact ⟨"Q", [("a", "S", InfMid)], [("a", "S", InfT)],
      "P", "b", "S", InfUnfold_wf, ⟨by decide, by decide⟩, by decide,
      hhallU, hkeyU, hcoverU, horderU, rfl, rfl, rfl⟩
  · -- Base step: `?P.b ; T --P.b--> T`.
    left
    refine ⟨InfMid_wf, ?_⟩
    unfold InfMid gPb
    apply mon_tr_yes_base.extC
    · decide
    · simp

/-- Every iterate accepts `?P.b` and moves to the next one (paper derivation,
    iterated): receiving `?P.b` while `?Q.a` is pending prepends another
    `?Q.a` expectation. -/
theorem InfU_co_step : ∀ n, mon_tr_yes_co (InfU n) gPb (InfU (n + 1))
    (InfU_wf n) (InfU_wf (n + 1)) :=
  fun n => mon_tr_yes_max_deriv_co.coinduct InfInv InfInv_closed
    (InfU n) gPb (InfU (n + 1)) (Or.inl ⟨n, rfl, rfl, rfl⟩)

/-- The monitor can then accept the pending `?Q.a` and return to its
    original state (paper: "could then accept an incoming message `a`
    from `Q`, and return to its original state"). -/
theorem InfU1_accept_a : mon_tr_yes_co (InfU 1) gQa InfT (InfU_wf 1) InfT_wf := by
  show mon_tr_yes_max_deriv_co
    (SessionType.externalChoice "Q" [("a", "S", InfT)]) gQa InfT
  exact mon_tr_yes_max_deriv_co.base (SessionType.wfCheck_sound (by decide))
    (mon_tr_yes_base.extC (by decide) (by simp))

end InfiniteStateCo

-- ================================================================
-- Infinitely many distinct monitor states.
-- ================================================================

section InfiniteStates

/-- Number of leading `?Q.a` prefixes: the `n`-th iterate has depth `n`. -/
private def qDepth : SessionType → Nat
  | .externalChoice "Q" [("a", _, U)] => qDepth U + 1
  | _ => 0

/-- The `n`-th iterate has depth `n`. -/
private theorem qDepth_InfU : ∀ n, qDepth (InfU n) = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show qDepth (InfU n) + 1 = n + 1
    exact congrArg (· + 1) ih

/-- Distinct iterates are different monitor states. -/
theorem InfU_injective : Function.Injective InfU := by
  intro n m h
  have hq : qDepth (InfU n) = qDepth (InfU m) := congrArg qDepth h
  rw [qDepth_InfU, qDepth_InfU] at hq
  exact hq

/-- Every iterate is fresh: `InfU n` never occurred among the earlier ones,
    so the reachable monitor states are infinite. -/
theorem InfU_fresh (n : Nat) : InfU n ∉ List.map InfU (List.range n) := by
  intro hmem
  obtain ⟨m, hmemR, heq⟩ := List.mem_map.mp hmem
  have hlt : m < n := List.mem_range.mp hmemR
  have heq2 : n = m := InfU_injective heq.symm
  omega

/-- Reachability: every iterate is reachable from `InfT` by `?P.b` steps. -/
theorem InfU_reachable : ∀ n, Relation.ReflTransGen
    (fun T V => mon_tr_yes_max_deriv_co T gPb V) InfT (InfU n) := by
  intro n
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    have hstep : mon_tr_yes_max_deriv_co (InfU n) gPb (InfU (n + 1)) := InfU_co_step n
    exact Relation.ReflTransGen.tail ih hstep

/-- The monitor of `ex:infinite-state-monitor` has infinitely many states:
    beyond any finite list of session types there is a reachable iterate
    (`InfU_co_step` gives the chain, `InfU_injective` keeps them distinct). -/
theorem InfU_infinite : ∀ S : List SessionType, ∃ n, ∀ m, n ≤ m → InfU m ∉ S := by
  intro S
  induction S with
  | nil => exact ⟨0, fun m _ => by simp⟩
  | cons x xs ih =>
    obtain ⟨n, hn⟩ := ih
    rcases Classical.em (∃ k, n ≤ k ∧ InfU k = x) with ⟨k, hkn, hkx⟩ | hnone
    · -- `x` is hit at `k`; every later iterate avoids `x :: xs`.
      refine ⟨k + 1, fun m hm hmem => ?_⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hxs
      · have hmk : m = k := InfU_injective hkx.symm
        omega
      · have hnm : n ≤ m := by omega
        exact absurd hxs (hn m hnm)
    · -- `x` is never hit at/after `n`; `n` already works.
      exact ⟨n, fun m hm hmem => by
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hxs
        · exact absurd ⟨m, hm, rfl⟩ hnone
        · exact absurd hxs (hn m hm)⟩

end InfiniteStates
