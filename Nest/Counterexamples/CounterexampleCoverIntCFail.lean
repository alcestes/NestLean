import Nest.SessionUtils
import Nest.Drainability

open Drainability

-- Failing example: T = tRec X (intC [(p,a,sa, extC p [(x,sx,X)]),
--                                  (q,b,sb, extC q [(y,sy,X)])]),
-- Q = [(p,x,sx),(q,y,sy)], msg = (p,x,sx).
-- intC_drain needs Q senders disjoint from branch roles {p,q}, but Q has p and q.
def IxB0 : SessionType :=
  SessionType.internalChoice
    [("p", "a", "sa", SessionType.externalChoice "p" [("x", "sx", SessionType.tVar "X")]),
     ("q", "b", "sb", SessionType.externalChoice "q" [("y", "sy", SessionType.tVar "X")])]
def IxT : SessionType := SessionType.tRec "X" IxB0
def IxQ : Queue :=
  [QueueMessage.msg "p" "x" "sx", QueueMessage.msg "q" "y" "sy"]
def IxMsg : QueueMessage := QueueMessage.msg "p" "x" "sx"
def IxQext : Queue := IxQ ++ [IxMsg]

def IxTa : SessionType :=
  SessionType.externalChoice "p" [("x", "sx", IxT)]
def IxTb : SessionType :=
  SessionType.externalChoice "q" [("y", "sy", IxT)]
def IxS : SessionType :=
  SessionType.internalChoice
    [("p", "a", "sa", IxTa), ("q", "b", "sb", IxTb)]

theorem IxS_eq_unfold : substSessionType IxB0 "X"
    (SessionType.tRec "X" IxB0) = IxS := rfl

theorem IxQext_eq : IxQext =
    [QueueMessage.msg "p" "x" "sx", QueueMessage.msg "q" "y" "sy",
     QueueMessage.msg "p" "x" "sx"] := rfl

-- WF holds (NoDupl keys (p,a)/(q,b) distinct, closed, guarded body).
theorem IxT_nodupl_body : IxB0.NoDupl := by
  unfold IxB0
  apply SessionType.NoDupl.internalChoice (by decide) (by decide)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · apply SessionType.NoDupl.externalChoice (by decide) (by decide)
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    subst hy
    exact SessionType.NoDupl.tVar _
  · apply SessionType.NoDupl.externalChoice (by decide) (by decide)
    intro y hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    subst hy
    exact SessionType.NoDupl.tVar _

theorem IxT_wf : IxT.WellFormed := by
  unfold IxT
  refine ⟨?_, ?_, ?_⟩
  · exact SessionType.NoDupl.tRec IxT_nodupl_body
  · unfold SessionType.IsClosed
    decide
  · apply SessionType.Contractive.tRec
    · apply SessionType.Contractive.internalChoice
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · apply SessionType.Contractive.externalChoice
        intro y hy
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        subst hy
        exact SessionType.Contractive.tVar _
      · apply SessionType.Contractive.externalChoice
        intro y hy
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        subst hy
        exact SessionType.Contractive.tVar _
    · simp [IxB0, SessionType.Guarded]

-- Can premise fails for Q: trec unfolds to intC, whose drain needs p,q fresh in Q,
-- but (p,x,sx) ∈ Q hits branch role p.
theorem Ix_noCan_Q : ¬ CanAlwaysDrainInternalDeepRec IxT IxQ := by
  intro h
  unfold IxT at h
  cases h with
  | trec_step _ _ _ _ hsub =>
    rw [IxS_eq_unfold] at hsub
    cases hsub with
    | intC_drain _ _ hfresh _ =>
      have hBranch : ("p", "a", "sa", IxTa) ∈
          ([("p", "a", "sa", IxTa), ("q", "b", "sb", IxTb)] :
            List (Role × Lab × DataSort × SessionType)) :=
        List.mem_cons.mpr (Or.inl rfl)
      have hMsg : QueueMessage.msg "p" "x" "sx" ∈
          ([QueueMessage.msg "p" "x" "sx", QueueMessage.msg "q" "y" "sy"] : Queue) :=
        List.mem_cons.mpr (Or.inl rfl)
      have hcon := hfresh "p" "a" "sa" IxTa hBranch
        (QueueMessage.msg "p" "x" "sx") hMsg
      -- hcon : (msg p x sx).1 ≠ "p", i.e. "p" ≠ "p".
      exact hcon rfl

-- Same failure for Q ++ [msg]: head (p,x,sx) still hits branch role p.
theorem Ix_noCan_ext : ¬ CanAlwaysDrainInternalDeepRec IxT IxQext := by
  intro h
  unfold IxT at h
  cases h with
  | trec_step _ _ _ _ hsub =>
    rw [IxS_eq_unfold] at hsub
    cases hsub with
    | intC_drain _ _ hfresh _ =>
      have hBranch : ("p", "a", "sa", IxTa) ∈
          ([("p", "a", "sa", IxTa), ("q", "b", "sb", IxTb)] :
            List (Role × Lab × DataSort × SessionType)) :=
        List.mem_cons.mpr (Or.inl rfl)
      have hMsg : QueueMessage.msg "p" "x" "sx" ∈ IxQext := by
        rw [IxQext_eq]
        exact List.mem_cons.mpr (Or.inl rfl)
      have hcon := hfresh "p" "a" "sa" IxTa hBranch
        (QueueMessage.msg "p" "x" "sx") hMsg
      exact hcon rfl

-- Verdict: WF holds but both Can premises fail, so the example is out of scope
-- for `candrain_implies_monitor_yes` (which needs Can Q and Can (Q++[msg]));
-- neither the Q=[]-style vacuous discharge nor the length-2 Dx-style cover applies.
theorem Ix_verdict : IxT.WellFormed ∧
    ¬ CanAlwaysDrainInternalDeepRec IxT IxQ ∧
    ¬ CanAlwaysDrainInternalDeepRec IxT IxQext :=
  ⟨IxT_wf, Ix_noCan_Q, Ix_noCan_ext⟩
