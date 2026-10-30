import Nest.SessionAdequacy
import Nest.CoverDeep

/-!
# WallDemo: duality wall example (`μX. p&a(s).X`).

Separating example for drainability duality strategies: every general
strategy (size induction, spine induction, small normal-form transport) dies on the
cyclic guarded type `μX. p&a(s).X`, yet deep drainability holds by hand
(`WallDeep`). Kept as a checked example, out of the soundness critical path.
-/

section DualityWallDemo
/-- Wall-demo type: `μX. p&a(s).X` (cyclic, guarded, WF+BalW). Every
    general duality strategy dies here (see the three killer facts);
    yet the disjunction still holds by hand (`WallDeep` below) —
    truth-vs-provability gap in one example. -/
private def WallB₀ : SessionType :=
  SessionType.externalChoice "p" [("a", "s", SessionType.tVar "X")]
/-- Wall-demo loop: `μX. p&a(s).X` (single-branch offer looping on `X`). -/
private def WallT₀ : SessionType := SessionType.tRec "X" WallB₀
/-- Wall-demo queue: the matching `(p, a, s)` message. -/
private def WallQ₀ : Queue := [QueueMessage.msg "p" "a" "s"]
/-- Wall-demo unfolding: one-step graft of the loop body (`X`-free target). -/
private def WallSubst₀ : SessionType :=
  substSessionType WallB₀ "X" WallT₀

/-- Strategy killer 1 (size induction): the unfolded type is strictly
    BIGGER, so no size-IH applies at the only type related by star. -/
example : sizeOf WallT₀ < sizeOf WallSubst₀ := by decide

/-- Strategy killer 2 (spine induction): nested branch spines exceed
    their parent's, so no spine bound survives subterms. -/
private def WallNest : SessionType :=
  SessionType.internalChoice [("r", "l", "s", WallT₀)]
example : WallNest.spine < WallT₀.spine := by decide

/-- Strategy killer 3 (small normal-form transport): the small normal form is
    OPEN (free `X`), hence related to `T₀` by no `UnfoldStar`, while
    still subterm-sized. -/
example : "X" ∈ (SessionType.externalChoice "p"
    [("a", "s", SessionType.tVar "X")]).fv := by decide
example : sizeOf (SessionType.externalChoice "p"
    [("a", "s", SessionType.tVar "X")]) ≤ sizeOf WallT₀ := by decide

/-- The unfold equation at `T₀` (by computation). -/
private theorem WallSubstEq : substSessionType WallB₀ "X" WallT₀ =
    SessionType.externalChoice "p" [("a", "s", WallT₀)] := rfl

/-- `B₀` genuinely offers `(a,s)` (used to refute `NoDequeueFrom`). -/
private theorem WallHasFalse : ¬ NoDequeueFrom WallB₀ WallQ₀ := by
  intro hnd
  apply hnd
  refine ⟨SessionType.tVar "X", [], "p", "a", "s", ?_, ?_⟩
  · exact st_trans.extC (by
      show ("a", "s", SessionType.tVar "X") ∈
        [("a", "s", SessionType.tVar "X")]
      exact List.mem_cons.mpr (Or.inl rfl))
  · show Queue.dequeue [QueueMessage.msg "p" "a" "s"]
      (QueueMessage.msg "p" "a" "s") = some []
    exact Queue.dequeue_head_hit

/-- `B₀` also offers `(a,s)` after the head message is gone — same
    witness shape at `T₀` (used to refute `NoDequeueFrom` there). -/
private theorem WallHasFalseT : ¬ NoDequeueFrom WallT₀ WallQ₀ := by
  intro hnd
  apply hnd
  refine ⟨WallT₀, [], "p", "a", "s", ?_, ?_⟩
  · exact st_trans.tRec (st_trans.extC
      (List.mem_cons.mpr (Or.inl rfl)))
  · show Queue.dequeue [QueueMessage.msg "p" "a" "s"]
      (QueueMessage.msg "p" "a" "s") = some []
    exact Queue.dequeue_head_hit

/-- `Core` at a `tVar` head with empty queue (refl; all arms mismatch). -/
private theorem WallCoreTVarNil :
    CanAlwaysDrainInternalDeepCore (SessionType.tVar "X") [] := by
  refine CanAlwaysDrainInternalDeepCore.mk (SessionType.tVar "X") []
    (SessionType.tVar "X") []
    (fun _ _ _ _ => ("a", "s", SessionType.tVar "X")) ?_ ?_ ?_ ?_ ?_
  · exact over_trans_trace.refl _
  · intro Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hne br hmem
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq
  · intro Ti Qi ρ1 ρ2 X B h1 h2 heq hEq
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq

/-- `Core` at `B₀` with empty queue (refl; `extC` arms exhibit the
    single branch + `WallCoreTVarNil`). -/
private theorem WallCoreBnil :
    CanAlwaysDrainInternalDeepCore WallB₀ [] := by
  refine CanAlwaysDrainInternalDeepCore.mk WallB₀ [] WallB₀ []
    (fun _ _ _ _ => ("a", "s", SessionType.tVar "X")) ?_ ?_ ?_ ?_ ?_
  · exact over_trans_trace.refl _
  · intro Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hne br hmem
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    simp only [WallB₀] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    show ("a", "s", SessionType.tVar "X") ∈
      [("a", "s", SessionType.tVar "X")]
    exact List.mem_cons.mpr (Or.inl rfl)
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    simp only [WallB₀] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    show CanAlwaysDrainInternalDeepCore (SessionType.tVar "X") []
    exact WallCoreTVarNil
  · intro Ti Qi ρ1 ρ2 X B h1 h2 heq hEq
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq

/-- `Core` at `B₀` with the head message present: single-dequeue
    trace to `(tVar X, [])`. Nil-splits use `WallHasFalse` absurdity
    at the `extC` arms; cons-splits force `(Ti,Qi) = (tVar X, [])`
    by length + nil-trace equations (the head step itself is never
    cased) with all arms mismatch-vacuous. -/
private theorem WallCoreBmsg :
    CanAlwaysDrainInternalDeepCore WallB₀ WallQ₀ := by
  have hmemB0 : ("a", "s", SessionType.tVar "X") ∈
      [("a", "s", SessionType.tVar "X")] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hQd : Queue.dequeue WallQ₀ (QueueMessage.msg "p" "a" "s") = some [] := by
    show Queue.dequeue [QueueMessage.msg "p" "a" "s"]
      (QueueMessage.msg "p" "a" "s") = some []
    exact Queue.dequeue_head_hit
  refine CanAlwaysDrainInternalDeepCore.mk WallB₀ WallQ₀
    (SessionType.tVar "X") [st_label.inp "p" "a" "s"]
    (fun _ _ _ _ => ("a", "s", SessionType.tVar "X")) ?_ ?_ ?_ ?_ ?_
  · exact over_trans_trace.step (over_trans.dequeue rfl hmemB0 hQd) (over_trans_trace.refl _)
  · intro Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hne br hmem
    cases ρ1 with
    | nil =>
      have hST0 := overTrTrace_nil_eq h1
      cases hST0
      cases hEq
    | cons α ρ1' =>
      cases ρ2 with
      | nil =>
        cases h2
        cases hEq
      | cons β ρ2' =>
        simp at heq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    cases ρ1 with
    | nil =>
      have hST0 := overTrTrace_nil_eq h1
      cases hST0
      exact absurd hnd WallHasFalse
    | cons α ρ1' =>
      cases ρ2 with
      | nil =>
        cases h2
        cases hEq
      | cons β ρ2' =>
        simp at heq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    cases ρ1 with
    | nil =>
      have hST0 := overTrTrace_nil_eq h1
      cases hST0
      exact absurd hnd WallHasFalse
    | cons α ρ1' =>
      cases ρ2 with
      | nil =>
        cases h2
        cases hEq
      | cons β ρ2' =>
        simp at heq
  · intro Ti Qi ρ1 ρ2 X B h1 h2 heq hEq
    cases ρ1 with
    | nil =>
      have hST0 := overTrTrace_nil_eq h1
      cases hST0
      cases hEq
    | cons α ρ1' =>
      cases ρ2 with
      | nil =>
        cases h2
        cases hEq
      | cons β ρ2' =>
        simp at heq

/-- `Core` at `T₀` with empty queue (refl; `tRec` arm descends to
    `WallCoreBnil`). -/
private theorem WallCoreTNil :
    CanAlwaysDrainInternalDeepCore WallT₀ [] := by
  refine CanAlwaysDrainInternalDeepCore.mk WallT₀ [] WallT₀ []
    (fun _ _ _ _ => ("a", "s", SessionType.tVar "X")) ?_ ?_ ?_ ?_ ?_
  · exact over_trans_trace.refl _
  · intro Ti Qi ρ1 ρ2 h1 h2 heq branches hEq hne br hmem
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq
  · intro Ti Qi ρ1 ρ2 p branches h1 h2 heq hEq hne hnd
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    cases hEq
  · intro Ti Qi ρ1 ρ2 X B h1 h2 heq hEq
    obtain ⟨rfl, rfl⟩ := by simpa using heq
    cases overTrTrace_nil_eq h1
    simp only [WallT₀] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    exact WallCoreBnil

/-- Pin lemma for the wall witness: splits of the tau-dequeue drain
    land on `(T₀,[msg])`, the substituted body, or `(T₀,[])`. -/
private lemma WallPin : ∀ (ρ1 : List st_label) (Ti : SessionType) (Qi : Queue)
    (ρ2 : List st_label),
    over_trans_trace (WallT₀, WallQ₀) ρ1 (Ti, Qi) →
    over_trans_trace (Ti, Qi) ρ2 (WallT₀, []) →
    [st_label.tau, st_label.inp "p" "a" "s"] = ρ1 ++ ρ2 →
    (Ti, Qi) = (WallT₀, WallQ₀) ∨
    (Ti, Qi) = (SessionType.externalChoice "p"
      [("a", "s", WallT₀)], WallQ₀) ∨
    (Ti, Qi) = (WallT₀, []) := by
  have hNorm : substSessionType WallB₀ "X" (SessionType.tRec "X" WallB₀) =
      SessionType.externalChoice "p" [("a", "s", WallT₀)] := by
    unfold WallB₀
    rfl
  intro ρ1 Ti Qi ρ2 h1 h2 heq
  cases ρ1 with
  | nil =>
    cases overTrTrace_nil_eq h1
    exact Or.inl rfl
  | cons α' ρ1' =>
    cases h1 with
    | step hS hT =>
      cases hS with
      | tauUnfold hU =>
        unfold WallT₀ at hU
        cases hU with
        | tRec =>
          cases ρ1' with
          | nil =>
            cases overTrTrace_nil_eq hT
            exact Or.inr (Or.inl rfl)
          | cons β ρ1'' =>
            cases hT with
            | step hS2 hT2 =>
              cases hS2 with
              | dequeue hEq hmem hQd =>
                rw [hNorm] at hEq
                injection hEq with hpeq hbeq'
                subst hpeq
                subst hbeq'
                simp only [List.mem_cons, List.mem_nil_iff,
                  or_false] at hmem
                obtain ⟨rfl, rfl, rfl⟩ := hmem
                have hQd0 : Queue.dequeue WallQ₀
                    (QueueMessage.msg "p" "a" "s") = some [] := by
                  unfold WallQ₀
                  exact Queue.dequeue_head_hit
                obtain rfl := Option.some_inj.mp (hQd0.symm.trans hQd)
                cases ρ1'' with
                | nil =>
                  cases overTrTrace_nil_eq hT2
                  exact Or.inr (Or.inr rfl)
                | cons γ ρ1''' =>
                  have hlen := congrArg List.length heq
                  simp at hlen
              | specInp hEq hmem hAbs =>
                rw [hNorm] at hEq
                injection hEq with hpeq hbeq'
                subst hpeq
                subst hbeq'
                simp only [List.mem_cons, List.mem_nil_iff,
                  or_false] at hmem
                obtain ⟨rfl, rfl, rfl⟩ := hmem
                have hmem0 : QueueMessage.msg "p" "a" "s" ∈ WallQ₀ := by
                  simp [WallQ₀]
                exact (hAbs _ hmem0 rfl).elim
              | sendFresh hEq _ _ => cases hEq
              | tauUnfold hU2 => cases hU2
      | dequeue hEq _ _ =>
        unfold WallT₀ at hEq
        cases hEq
      | specInp hEq _ _ =>
        unfold WallT₀ at hEq
        cases hEq
      | sendFresh hEq _ _ =>
        unfold WallT₀ at hEq
        cases hEq

/-- THE EXAMPLE: `Deep` holds at `(μX. p&a(s).X, [msg p a s])` —
    tau-dequeue trace to `(T₀, [])`. Nil-splits pin `(T₀,[msg])`
    (`tRec` arm via `WallCoreBmsg`, `extC` via `WallHasFalseT`
    absurdity); middle splits pin the substituted body (`extC` via
    dequeue absurdity); end-splits pin `(T₀,[])` by constructor clash.
    No induction, no fuel, no adequacy — yet none of the general
    strategies (size, spine, transport, small normal-form) can produce this
    proof mechanically. -/
theorem WallDeep : CanAlwaysDrainInternalDeep WallT₀ WallQ₀ := by
  have hmemB1 : ("a", "s", WallT₀) ∈ [("a", "s", WallT₀)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hQd : Queue.dequeue WallQ₀ (QueueMessage.msg "p" "a" "s") = some [] := by
    show Queue.dequeue [QueueMessage.msg "p" "a" "s"]
      (QueueMessage.msg "p" "a" "s") = some []
    exact Queue.dequeue_head_hit
  have hU : Unfold1 WallT₀
      (SessionType.externalChoice "p" [("a", "s", WallT₀)]) := by
    unfold WallT₀
    exact Unfold1.tRec
  refine ⟨WallT₀, [st_label.tau, st_label.inp "p" "a" "s"],
    over_trans_trace.step (over_trans.tauUnfold hU)
      (over_trans_trace.step (over_trans.dequeue rfl hmemB1 hQd)
        (over_trans_trace.refl _)), ?_⟩
  · intro Ti Qi ρ1 ρ2 g1 g2 heq
    rcases WallPin ρ1 Ti Qi ρ2 g1 g2 heq with h | h | h <;> cases h
    -- At `(WallT₀,[msg])`: nil-splits by head clashes (`tRec` via
    -- `WallCoreBmsg`, `extC` via `WallHasFalseT`); cons-splits
    -- contradict (single steps cannot loop).
    · cases ρ1 with
      | nil =>
        have hST0 := overTrTrace_nil_eq g1
        cases hST0
        refine ⟨?_, ?_, ?_⟩
        · intro branches hEq hne br hmem
          cases hEq
        · intro p branches hEq hne hnd
          exact absurd hnd WallHasFalseT
        · intro X B hEq
          simp only [WallT₀] at hEq
          obtain ⟨rfl, rfl⟩ := hEq
          exact WallCoreBmsg
      | cons α ρ1' =>
        cases ρ2 with
        | nil =>
          cases g2
        | cons β ρ2' =>
          have hlen1 : ρ1'.length = 0 := by
            have h2 := congrArg List.length heq
            simp at h2
            omega
          have hρ1' : ρ1' = [] := List.length_eq_zero_iff.mp hlen1
          subst hρ1'
          cases g1 with
          | step hS hT =>
            cases hS with
            | tauUnfold hU =>
              unfold WallT₀ at hU
              cases hU with
              | tRec =>
                cases overTrTrace_nil_eq hT
            | dequeue hEqS _ _ =>
              unfold WallT₀ at hEqS
              cases hEqS
            | specInp hEqS _ _ =>
              unfold WallT₀ at hEqS
              cases hEqS
            | sendFresh hEqS _ _ =>
              unfold WallT₀ at hEqS
              cases hEqS
    · refine ⟨?_, ?_, ?_⟩
      · intro branches hEq hne br hmem
        cases hEq
      · intro p branches hEq hne hnd
        injection hEq with hpeq hbeq'
        subst hpeq
        subst hbeq'
        exact (hnd ⟨_, _, _, _, _,
          st_trans.extC (List.mem_cons.mpr (Or.inl rfl)), hQd⟩).elim
      · intro X B hEq
        cases hEq
    · refine ⟨?_, ?_, ?_⟩
      · intro branches hEq hne br hmem
        unfold WallT₀ at hEq
        cases hEq
      · intro p branches hEq hne hnd
        unfold WallT₀ at hEq
        cases hEq
      · intro X B hEq
        unfold WallT₀ at hEq
        cases hEq
        exact WallCoreBnil

end DualityWallDemo
