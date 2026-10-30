import Nest.SessionUtils
import Nest.Drainability

open Drainability

-- Certifies that branch-preserving `Cannot` without freshness
-- is FALSE: a blocked tableau coexists with an all-`Can` target family.
-- This file is evidence only (not imported by `Nest.lean`).

/-- Counterexample target: offers `("l0","s0")` from `"q"`, then ends.
    At `CE_Q` it drains (one dequeue to `[]`), i.e. it is `Can`. -/
def CE_T' : SessionType :=
  SessionType.externalChoice "q" [("l0", "s0", SessionType.tEnd)]

/-- Counterexample head: internal choice with a single `"q"`-branch. -/
def CE_T : SessionType :=
  SessionType.internalChoice [("q", "l", "s", CE_T')]

/-- Counterexample queue: the exact message the target wants. -/
def CE_Q : Queue :=
  [QueueMessage.msg "q" "l0" "s0"]

theorem CE_T'_wf : CE_T'.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.externalChoice
    · decide
    · simp
    · intro x hx
      simp at hx
      subst hx
      exact SessionType.NoDupl.end
  · show CE_T'.fv = []
    rfl
  · apply SessionType.Contractive.externalChoice
    intro x hx
    simp at hx
    subst hx
    exact SessionType.Contractive.end

theorem CE_T_wf : CE_T.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.internalChoice
    · decide
    · simp
    · intro x hx
      simp at hx
      subst hx
      exact CE_T'_wf.1
  · show CE_T.fv = []
    rfl
  · apply SessionType.Contractive.internalChoice
    intro x hx
    simp at hx
    subst hx
    exact CE_T'_wf.2.2

theorem CE_wf : CE_T'.WellFormed ∧ CE_T.WellFormed := ⟨CE_T'_wf, CE_T_wf⟩

/-- The head is `Cannot` (blocked: `"q"`-message queued, `"q"`-branch). -/
theorem CE_cannot : CannotAlwaysDrainInternalDeepRec CE_T CE_Q := by
  apply CannotAlwaysDrainInternalDeepSeen.intC_blocked _ _ _
    "q" "l" "s" CE_T' (QueueMessage.msg "q" "l0" "s0")
  · simp
  · simp [CE_Q]
  · rfl

/-- The (only) branch target is `Can` (dequeues to `[]`). -/
theorem CE_target_can : CanAlwaysDrainInternalDeepRec CE_T' CE_Q := by
  refine CanAlwaysDrainInternalDeepRec.extC_deq "q" [("l0", "s0", SessionType.tEnd)]
    CE_Q [] "l0" "s0" SessionType.tEnd ?_ ?_ ?_
  · simp
  · decide
  · exact CanAlwaysDrainInternalDeepRec.drained_nil _

/-- (3) without freshness is FALSE: the blocked tableau above coexists
    with an all-`Can` target family, so no branch preserves `Cannot`. -/
theorem cannot_adv_branch_needs_freshness :
    ¬ ∀ (branches : List (Role × Lab × DataSort × SessionType)) (Q : Queue),
      CannotAlwaysDrainInternalDeepRec (SessionType.internalChoice branches) Q →
      ∃ x ∈ branches, CannotAlwaysDrainInternalDeepRec x.2.2.2 Q := by
  intro hAll
  obtain ⟨x, hmem, hCx⟩ := hAll [("q", "l", "s", CE_T')] CE_Q CE_cannot
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  subst hmem
  exact (drainrec_not_cannot_of_can CE_wf.1 CE_target_can) hCx
