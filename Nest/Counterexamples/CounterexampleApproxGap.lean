import Nest.SessionUtils
import Nest.Drainability

open Drainability

-- `Cannot` coexists with overapprox-drainage: serving uses
-- *some* branch while `Can` needs *every* branch.
-- This file is evidence only (not imported by `Nest.lean`).

/-- Serving branch used by the refutation below. -/
def CE2_A : SessionType :=
  SessionType.externalChoice "q" [("l", "s", SessionType.tEnd)]

/-- Head with one serving branch and one stuck branch. -/
def CE2_T : SessionType :=
  SessionType.internalChoice [("r", "lr", "sr", CE2_A), ("x", "lx", "sx", SessionType.tEnd)]

/-- Queue with only the serving branch's message (hence fresh for the
    `intC` head, and nonempty). -/
def CE2_Q : Queue :=
  [QueueMessage.msg "q" "l" "s"]

/-- `Cannot` holds via the stuck `tEnd` branch (cut-free `intC_adv`). -/
theorem CE2_cannot : CannotAlwaysDrainInternalDeepRec CE2_T CE2_Q := by
  apply CannotAlwaysDrainInternalDeepSeen.intC_adv _ _ _
    ("x", "lx", "sx", SessionType.tEnd)
  · simp
  · intro r' l' s' U' hmemU m hmQ heq
    simp only [CE2_Q, List.mem_cons, List.mem_nil_iff, or_false] at hmQ
    subst hmQ
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemU
    rcases hmemU with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩ <;> simp at heq
  · apply CannotAlwaysDrainInternalDeepSeen.tEnd _ _
    simp [CE2_Q]

/-- Yet the serving branch drains `Q` in the overapprox LTS
    (`sendFresh` fires it without touching the queue, then `dequeue`
    consumes the message). So approx-drainage coexists with `Cannot`. -/
theorem CE2_over_drains : ∃ ρ T', over_trans_trace (CE2_T, CE2_Q) ρ (T', []) := by
  have hmemA : ("r", "lr", "sr", CE2_A) ∈
      [("r", "lr", "sr", CE2_A), ("x", "lx", "sx", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hST : st_trans CE2_T (st_label.out "r" "lr" "sr") CE2_A := by
    unfold CE2_T
    exact st_trans.intC (List.mem_cons.mpr (Or.inl rfl))
  have hFresh : ∀ (r' : Role) (l' : Lab) (s' : DataSort) (U' : SessionType),
      (r', l', s', U') ∈
        [("r", "lr", "sr", CE2_A), ("x", "lx", "sx", SessionType.tEnd)] →
      ∀ m ∈ CE2_Q, m.1 ≠ r' := by
    intro r' l' s' U' hmemU m hmQ heq
    simp only [CE2_Q, List.mem_cons, List.mem_nil_iff, or_false] at hmQ
    subst hmQ
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmemU
    rcases hmemU with ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩ <;> simp at heq
  have hmemD : ("l", "s", SessionType.tEnd) ∈ [("l", "s", SessionType.tEnd)] :=
    List.mem_cons.mpr (Or.inl rfl)
  have hQd : CE2_Q.dequeue (QueueMessage.msg "q" "l" "s") = some [] := by decide
  have e1 : over_trans_trace (CE2_A, CE2_Q) [st_label.inp "q" "l" "s"] (SessionType.tEnd, []) :=
    over_trans_trace.step (over_trans.dequeue rfl hmemD hQd) (over_trans_trace.refl _)
  have e0 : over_trans_trace (CE2_T, CE2_Q)
      [st_label.out "r" "lr" "sr", st_label.inp "q" "l" "s"] (SessionType.tEnd, []) :=
    over_trans_trace.step (over_trans.sendFresh rfl hST hFresh) e1
  exact ⟨_, _, e0⟩

/-- `CE2_T` is well-formed (needed for the duality step below). -/
theorem CE2_T_wf : CE2_T.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.internalChoice
    · decide
    · simp
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · exact SessionType.NoDupl.externalChoice (by decide) (by simp)
          (fun y hy => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
            subst hy
            exact SessionType.NoDupl.end)
      · exact SessionType.NoDupl.end
  · show CE2_T.fv = []
    rfl
  · apply SessionType.Contractive.internalChoice
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · apply SessionType.Contractive.externalChoice
      intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      subst hy
      exact SessionType.Contractive.end
    · exact SessionType.Contractive.end

/-- Exact `Can` fails, by duality from `CE2_cannot` (avoids casing on
    the head-normal form). This is precisely why the gap's
    all-served churn does not contradict `Cannot`: serving uses
    *some* branch, `Can` needs *every* branch. -/
theorem CE2_noCan : ¬ CanAlwaysDrainInternalDeepRec CE2_T CE2_Q :=
  fun hCan => drainrec_not_cannot_of_can CE2_T_wf hCan CE2_cannot
