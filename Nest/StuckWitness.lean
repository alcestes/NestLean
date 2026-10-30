import Nest.FairScheduler

/-!
# StuckWitness: single-role projected traces and lockstep alignment.

Role-projected queue/session traces (`role_trace`), their lockstep alignment with
`τ*` network evolution (`aligned_exec`), and the oldest-from persistence shape
(`oldest_from`). Feeds the drain-failure ⇒ non-liveness argument.
-/
/-- Actions of a role-projected trace: session-type steps or queue receives. -/
inductive role_trace_action : Type where
  | st : st_label → role_trace_action
  | recv : QueueMessage → role_trace_action
  deriving DecidableEq

/-- Single projected step at one role, mirroring `sq_trans` (sends keep the queue,
    dequeues pop it, receives extend it). -/

inductive role_trace_step : SessionTypeWithQueue → role_trace_action → SessionTypeWithQueue → Prop where
  | send {T T' Q p lab S} (h : st_trans T (st_label.out p lab S) T') :
    role_trace_step (T, Q) (role_trace_action.st (st_label.out p lab S)) (T', Q)
  | dequeue {T T' Q Q' p lab S} (hST : st_trans T (st_label.inp p lab S) T')
      (hQ : Q.dequeue (QueueMessage.msg p lab S) = some Q') :
    role_trace_step (T, Q) (role_trace_action.st (st_label.inp p lab S)) (T', Q')
  | recv {T Q} {m : QueueMessage} :
    role_trace_step (T, Q) (role_trace_action.recv m) (T, Q ++ [m])

/-- Projected trace of one role: a list of actions taking `(T, Q)` to `(T', Q')`. -/

inductive role_trace : SessionTypeWithQueue → List role_trace_action → SessionTypeWithQueue → Prop where
  | refl (stq) : role_trace stq [] stq
  | step {stq mid stq'} {a : role_trace_action} {tr : List role_trace_action}
      (h1 : role_trace_step stq a mid) (h2 : role_trace mid tr stq') :
    role_trace stq (a :: tr) stq'

/-- Lockstep alignment of a `τ*` evolution with one role's projected trace: each
    network step contributes its projected single-step trace. -/
inductive aligned_exec (q : Role) : Network → List role_trace_action → Network → Prop where
  | refl (N) : aligned_exec q N [] N
  | step {N1 N2 N3 δ} {T Q T2 Q2} {tra tr : List role_trace_action}
      (hmem1 : (q, (T, Q)) ∈ N1)
      (hTr : net_trans N1 δ N2) (hInt : is_internal_net_label δ)
      (hProj : role_trace (T, Q) tra (T2, Q2))
      (hmem2 : (q, (T2, Q2)) ∈ N2)
      (hTail : aligned_exec q N2 tr N3) : aligned_exec q N1 (tra ++ tr) N3

/-- Reflexive-transitive closure of `st_trans` over label sequences (paper `ρ̃`). -/
inductive st_seq : SessionType → List st_label → SessionType → Prop where
  | refl (T) : st_seq T [] T
  | step (α : st_label) {T Tmid T' : SessionType} {ρ : List st_label}
      (h1 : st_trans T α Tmid) (h2 : st_seq Tmid ρ T') : st_seq T (α :: ρ) T'

