import Nest.SessionLTS

open Cslib
open Cslib.LTS

set_option linter.unusedVariables false

/-!
# NetworkLTS: Queues, session queues, and networks.

Input queues and dequeue, `SessionTypeWithQueue`/`sq_trans`, networks and the
network LTS (`net_label`/`net_trans`), plus queue-scan predicates (`prune*`).
-/

-- ================================================================
-- Input queues
-- ================================================================

/-- Queue messages: a sender role `p` sending label `lab` with payload sort `S` to the queue owner. -/
inductive QueueMessage : Type where
  | msg : Role → Lab → DataSort → QueueMessage
  deriving DecidableEq

/-- An input queue is a list of queued messages. -/
abbrev Queue := List QueueMessage

/-- Dequeue a message from a queue. The message can be dequeued if it is the first message with
    the desired sender. This removes the need for a queue congruence that reorders queued
    messages with different senders.-/
def Queue.dequeue.go (seen : Queue) (left : Queue) (msg : QueueMessage) : Option Queue :=
  match left with
  | [] => none
  | m :: left' =>
    if m = msg then some (seen ++ left')
    else if m.1 = msg.1 then none
    else Queue.dequeue.go (seen ++ [m]) left' msg

/-- Dequeue the first message with the given sender (entry point; starts with an empty
   seen-accumulator). -/
def Queue.dequeue (q : Queue) (msg : QueueMessage) : Option Queue :=
  Queue.dequeue.go [] q msg

-- ================================================================
-- First-input pruning (speculative input resolution).
-- ================================================================

/-- All-`p`-absence check: every `internalChoice` branch sender differs
    from `p` (Bool `!=`, so `rfl`-probes compute). -/
def pruneAllNonP (p : Role) :
    List (Role × Lab × DataSort × SessionType) → Bool
  | [] => true
  | (q, _, _, _) :: rest => ((q != p) && pruneAllNonP p rest)

mutual
/-- Deep existence check for `pruneFirstInputDeep`: like
    `pruneFirstInputHas`, except an `internalChoice` requires *every*
    branch sender to differ from `p` (a `p`-sender branch anywhere
    poisons reachability, matching `mon_tr_yes_exist.pfxInt`'s all-fresh
    side condition) *and* some branch target to reach. -/
def pruneFirstInputDeepHas (p : Role) (lab : Lab) (S : DataSort) :
    SessionType → Bool
  | .tEnd => false
  | .tVar _ => false
  | .tRec _ B => pruneFirstInputDeepHas p lab S B
  | .internalChoice branches =>
    pruneAllNonP p branches && pruneHasDeepIntAny p lab S branches
  | .externalChoice q branches =>
    if q == p then
      branches.any (fun b => match b with
        | (l, S', _) => l == lab && S' == S)
    else pruneHasDeepExt p lab S branches

/-- Any-reachability pass over internal branch targets. -/
def pruneHasDeepIntAny (p : Role) (lab : Lab) (S : DataSort) :
    List (Role × Lab × DataSort × SessionType) → Bool
  | [] => false
  | (_, _, _, T') :: rest =>
    (pruneFirstInputDeepHas p lab S T' ||
      pruneHasDeepIntAny p lab S rest)

/-- List traversal for `pruneFirstInputDeepHas` over non-`p` external
    branch targets: some target must reach. -/
def pruneHasDeepExt (p : Role) (lab : Lab) (S : DataSort) :
    List (Lab × DataSort × SessionType) → Bool
  | [] => false
  | (_, _, T') :: rest =>
    (pruneFirstInputDeepHas p lab S T' || pruneHasDeepExt p lab S rest)
end

mutual
/-- Deep transformation for `pruneFirstInputDeep`: like `pruneFirstInputGo`,
    except branches that cannot reach an `externalChoice p` offering
    `(lab, S)` are removed (rather than kept). Resolved `(lab, S)`
    continuations are inserted as-is. Empty filtered choice lists collapse
    to `tEnd` to keep the function total.
    Recursion under `tRec` unfolds: if `pruneFirstInputDeepHas` holds for the
    recursive type, the body is unfolded
    (`substSessionType B X (tRec X B)`) and pruning iterates over the
    unfolded type; otherwise the result is `tEnd`. `fuel` bounds recursion
    unfoldings only — all other steps thread it unchanged — so a `tRec` head
    at fuel `0` folds to `tEnd`. Termination is by the lexicographic pair
    `(fuel, sizeOf ·)`: unfoldings strictly decrease `fuel`, structural steps
    strictly decrease `sizeOf` at fixed `fuel`. -/
def pruneFirstInputDeepGo (p : Role) (lab : Lab) (S : DataSort) :
    (fuel : Nat) → (T : SessionType) → SessionType
  | _, .tEnd => .tEnd
  | _, .tVar X => .tVar X
  | 0, .tRec _ _ => .tEnd
  | (f + 1), .tRec X B =>
    if pruneFirstInputDeepHas p lab S (SessionType.tRec X B) then
      pruneFirstInputDeepGo p lab S f (substSessionType B X (SessionType.tRec X B))
    else if X ∈ B.fv then .tEnd
    else pruneFirstInputDeepGo p lab S f B
  | fuel, .internalChoice branches =>
    match pruneGoDeepInt p lab S fuel branches with
    | [] => .tEnd
    | filtered => .internalChoice filtered
  | fuel, .externalChoice q branches =>
    if q == p then
      match branches.find? (fun b => match b with
          | (l, S', _) => l == lab && S' == S) with
      | some (_, _, T') => T'
      | none => .tEnd
    else
      match pruneGoDeepExt p lab S fuel branches with
      | [] => .tEnd
      | filtered => .externalChoice q filtered
termination_by fuel T => (fuel, sizeOf T)

/-- List traversal for `pruneFirstInputDeepGo` over internal branches:
    keep (mapped) iff the target reaches `(lab, S)` under `DeepHas`,
    else drop. `fuel` is threaded unchanged (only `tRec` unfolding consumes
    it). -/
def pruneGoDeepInt (p : Role) (lab : Lab) (S : DataSort) :
    (fuel : Nat) →
    List (Role × Lab × DataSort × SessionType) →
      List (Role × Lab × DataSort × SessionType)
  | _, [] => []
  | fuel, (q, l, S', T') :: rest =>
    if pruneFirstInputDeepHas p lab S T' then
      (q, l, S', pruneFirstInputDeepGo p lab S fuel T') ::
        pruneGoDeepInt p lab S fuel rest
    else pruneGoDeepInt p lab S fuel rest
termination_by fuel branches => (fuel, sizeOf branches)

/-- List traversal for `pruneFirstInputDeepGo` over non-`p` external
    branch targets: keep (mapped) iff the target reaches `(lab, S)`
    under `DeepHas`, else drop. `fuel` is threaded unchanged. -/
def pruneGoDeepExt (p : Role) (lab : Lab) (S : DataSort) :
    (fuel : Nat) →
    List (Lab × DataSort × SessionType) →
      List (Lab × DataSort × SessionType)
  | _, [] => []
  | fuel, (l, S', T') :: rest =>
    if pruneFirstInputDeepHas p lab S T' then
      (l, S', pruneFirstInputDeepGo p lab S fuel T') ::
        pruneGoDeepExt p lab S fuel rest
    else pruneGoDeepExt p lab S fuel rest
termination_by fuel branches => (fuel, sizeOf branches)
end

/-- Fuel adequacy for deep pruning: `fuel` suffices to prune `T` without
    hitting a fuel cutoff. Mirrors `pruneFirstInputDeepGo`: only the `tRec`
    arm consumes fuel, requiring `Has`-true plus adequacy of the unfolded
    type at smaller fuel (`trec_yes`); `Has`-false `tRec` heads admit no
    adequacy derivation at all, so adequacy everywhere implies `Has`-true
    along the whole `tRec` spine — joint inductions for the recursive prune
    correspondence induct on adequacy derivations (outer) and size (inner):
    `trec_yes` supplies exactly the smaller-fuel adequate-subst fact that
    `tRec`-unfolding needs. -/
inductive PruneAdequate (p : Role) (lab : Lab) (S : DataSort) :
    Nat → SessionType → Prop where
  | tEnd (fuel : Nat) : PruneAdequate p lab S fuel .tEnd
  | tvar (fuel : Nat) (X : String) : PruneAdequate p lab S fuel (.tVar X)
  | trec_yes {f : Nat} {X : String} {B : SessionType}
      (hHas : pruneFirstInputDeepHas p lab S (SessionType.tRec X B) = true)
      (hsub : PruneAdequate p lab S f
        (substSessionType B X (SessionType.tRec X B))) :
    PruneAdequate p lab S (f + 1) (SessionType.tRec X B)
  | trec_vac {f : Nat} {X : String} {B : SessionType}
      (hfree : X ∉ B.fv)
      (hsub : PruneAdequate p lab S f B) :
    PruneAdequate p lab S (f + 1) (SessionType.tRec X B)
  | intC {fuel : Nat} {branches : List (Role × Lab × DataSort × SessionType)}
      (hall : ∀ (x : Role × Lab × DataSort × SessionType), x ∈ branches →
        PruneAdequate p lab S fuel x.2.2.2) :
    PruneAdequate p lab S fuel (SessionType.internalChoice branches)
  | extC {fuel : Nat} {q : Role} {branches : List (Lab × DataSort × SessionType)}
      (hall : ∀ (x : Lab × DataSort × SessionType), x ∈ branches →
        PruneAdequate p lab S fuel x.2.2) :
    PruneAdequate p lab S fuel (SessionType.externalChoice q branches)

/-- Session type with input queue: T̈ = (T, σ). -/
abbrev SessionTypeWithQueue : Type := SessionType × Queue

/-- A session-type-with-queue is well-formed when the session type component is well-formed. -/
def SessionTypeWithQueue.WellFormed (stq : SessionTypeWithQueue) : Prop :=
  SessionType.WellFormed stq.1

-- ================================================================
-- Session types with queues LTS
-- ================================================================

/-- Labels β ::= p ! lab (S)  |  τ(p & lab (S))  |  p ? lab (S) -/
inductive sq_action : Type where
  | send : Role → Lab → DataSort → sq_action
  | dequeue : Role → Lab → DataSort → sq_action
  | recv : Role → Lab → DataSort → sq_action
  deriving DecidableEq

/-- External tag γ ::= p ! lab (S)  |  p ? lab (S). -/
inductive ext_tag : Type where
  | send : Role → Lab → DataSort → ext_tag
  | recv : Role → Lab → DataSort → ext_tag
  deriving DecidableEq

/-- LTS for session types with input queues.
    Rules: SQ-Send, SQ-Deq, SQ-Recv. -/
inductive sq_trans : SessionTypeWithQueue → sq_action → SessionTypeWithQueue → Prop where
  | send {T T' : SessionType} {Q : Queue} {p : Role} {lab : Lab} {S : DataSort}
      (h : st_trans T (st_label.out p lab S) T') :
    sq_trans (T, Q) (sq_action.send p lab S) (T', Q)
  | dequeue {T T' : SessionType} {Q Q' : Queue} {p : Role} {lab : Lab} {S : DataSort}
      (hST : st_trans T (st_label.inp p lab S) T')
      (hQ : Q.dequeue (QueueMessage.msg p lab S)  = some Q') :
    sq_trans (T, Q) (sq_action.dequeue p lab S) (T', Q')
  | recv {T : SessionType} {Q : Queue} {p : Role} {lab : Lab} {S : DataSort} :
    sq_trans (T, Q) (sq_action.recv p lab S) (T, (Q ++ [QueueMessage.msg p lab S]))

/-- If a session type with queue is well-formed and performs a transition,
    it remains well-formed. -/
lemma SessionTypeWithQueue.wellFormedPreserved (T : SessionTypeWithQueue) (α : sq_action) (T' : SessionTypeWithQueue)
  (hWF : T.WellFormed) (hTr : sq_trans T α T') : T'.WellFormed := by
  unfold SessionTypeWithQueue.WellFormed at hWF ⊢
  revert hWF
  induction hTr with
  | send hST =>
      rename_i T0 T0' Q0 p lab S
      intro hWF
      exact SessionType.wellFormedPreserved T0 (st_label.out p lab S) T0' hWF hST
  | dequeue hST hQ =>
      rename_i T0 T0' Q0 Q0' p lab S
      intro hWF
      exact SessionType.wellFormedPreserved T0 (st_label.inp p lab S) T0' hWF hST
  | recv =>
      rename_i T0 Q0 p lab S
      intro hWF
      exact hWF

-- ================================================================
-- Networks
-- ================================================================

/-- Network as a finite mapping from roles to session-type-with-queue.
    N ::= { p_i ↦ T̈_i }_{i∈I}   (flat-list representation) -/
abbrev Network : Type := List (Role × SessionTypeWithQueue)

/-- Replace role r's session type with queue in N (removes old entry for r). -/
def Network.replace (N : Network) (r : Role) (stq : SessionTypeWithQueue) : Network :=
  (r, stq) :: N.filter (λ (x : Role × SessionTypeWithQueue) => x.1 != r)

/-- A network is sender-closed when every queued message's sender is present as a role
    in the network. This discharges the `hmem_p` (sender-presence) hypothesis for
    half-duplexity / off-role arguments from well-formedness plus queue membership. -/
def Network.SenderClosed (N : Network) : Prop :=
  ∀ (q : Role) (T : SessionType) (Q : Queue) (p : Role) (lab : Lab) (S : DataSort),
    (q, (T, Q)) ∈ N → QueueMessage.msg p lab S ∈ Q → ∃ stq : SessionTypeWithQueue, (p, stq) ∈ N

/-- A network is well-formed when there are no duplicate roles, each session type
    is well-formed, and every queued message's sender is present (sender-closure). -/
def Network.WellFormed (N : Network) : Prop :=
  List.Nodup (List.map (λ (x : Role × SessionTypeWithQueue) => x.1) N) ∧
  (∀ (x : Role × SessionTypeWithQueue), x ∈ N →
    match x with
    | (_, (T, _)) => SessionType.WellFormed T) ∧
  Network.SenderClosed N

/-- A network has no self-mention when no role occurs in its own session
    type (paper `Def. network` side condition; queue senders are covered
    separately by `SenderClosed`). -/
def Network.NoSelf (N : Network) : Prop :=
  ∀ (q : Role) (T : SessionType) (Q : Queue), (q, (T, Q)) ∈ N → ¬ T.Occurs q

/-- Every role occurring in a member's session type is itself a member:
    send targets (which occur as branch senders) are present, so sends
    replay as `τ_comm`. -/
def Network.RolesPresent (N : Network) : Prop :=
  ∀ (q : Role) (T : SessionType) (Q : Queue) (s : Role),
    (q, (T, Q)) ∈ N → T.Occurs s → ∃ stq : SessionTypeWithQueue, (s, stq) ∈ N

/-- Network labels δ ::= p:γ  |  τ(p : q&lab(S))  |  τ(p → q : lab(S))
    where γ = p!lab(S) | p?lab(S). -/
inductive net_label : Type where
  | io_send : Role → Role → Lab → DataSort → net_label
  | io_recv : Role → Role → Lab → DataSort → net_label
  | τ_dequeue : Role → Role → Lab → DataSort → net_label
   | τ_comm : Role → Role → Lab → DataSort → net_label
  deriving DecidableEq

/-- Internal τ-labels for networks are τ_dequeue and τ_comm. -/
def is_internal_net_label (δ : net_label) : Prop :=
  match δ with
  | net_label.τ_dequeue _ _ _ _ => True
  | net_label.τ_comm _ _ _ _ => True
  | _ => False

/-- LTS for networks (flat-list representation).
    Rules: Net-γ, Net-Deq, Net-Comm.
    The par-left/par-right rules are eliminated – the flat list makes
    them unnecessary since any role present in the list can transition. -/
inductive net_trans : Network → net_label → Network → Prop where
  | io_send {r p : Role} {stq stq' : SessionTypeWithQueue} {lab : Lab} {S : DataSort}
      (h : sq_trans stq (sq_action.send p lab S) stq')
      (hmem : (r, stq) ∈ N) :
    net_trans N (net_label.io_send r p lab S) (Network.replace N r stq')
  | io_recv {r p : Role} {stq stq' : SessionTypeWithQueue} {lab : Lab} {S : DataSort}
      (h : sq_trans stq (sq_action.recv p lab S) stq')
      (hmem : (r, stq) ∈ N) :
    net_trans N (net_label.io_recv r p lab S) (Network.replace N r stq')
  | dequeue {r p : Role} {stq stq' : SessionTypeWithQueue} {lab : Lab} {S : DataSort}
      (h : sq_trans stq (sq_action.dequeue p lab S) stq')
      (hmem : (r, stq) ∈ N) :
    net_trans N (net_label.τ_dequeue r p lab S) (Network.replace N r stq')
  | comm {p q : Role} {lab : Lab} {S : DataSort}
      {stqp stqp' : SessionTypeWithQueue} {stqq stqq' : SessionTypeWithQueue}
      (hne : p ≠ q)
      (h_send : sq_trans stqp (sq_action.send q lab S) stqp')
      (h_recv : sq_trans stqq (sq_action.recv p lab S) stqq')
      (hmem_p : (p, stqp) ∈ N)
      (hmem_q : (q, stqq) ∈ N) :
    net_trans N (net_label.τ_comm p q lab S) ((N.replace p stqp').replace q stqq')

/-- The network LTS: states are networks, labels are `net_label`, steps are `net_trans`. -/
def netLTS : LTS Network net_label := LTS.mk net_trans

/-- Every role of `N` still occurs in `Network.replace N r stq` (with new data at `r`). -/
private lemma Network.role_preserved_replace {N : Network} {r : Role}
    {stq : SessionTypeWithQueue} {p : Role} {st : SessionTypeWithQueue}
    (hmem : (p, st) ∈ N) : ∃ stq', (p, stq') ∈ Network.replace N r stq := by
  by_cases heq : p = r
  · subst heq
    exact ⟨stq, by unfold Network.replace; simp⟩
  · exact ⟨st, by
      unfold Network.replace
      simp
      right
      exact ⟨hmem, heq⟩⟩

/-- Members of a `Queue.dequeue.go` result come from `seen ++ left`. -/
private lemma Queue.dequeue.go_mem_subset (seen left : Queue) (msg : QueueMessage)
    (Q' : Queue) (h : Queue.dequeue.go seen left msg = some Q') :
    ∀ x ∈ Q', x ∈ seen ++ left := by
  induction left generalizing seen with
  | nil =>
    simp [Queue.dequeue.go] at h
  | cons m left' ih =>
    simp only [Queue.dequeue.go] at h
    by_cases heq : m = msg
    · simp [heq] at h
      subst h
      intro x hx
      have hmem : x ∈ seen ∨ x ∈ left' := by
        simpa [List.mem_append] using hx
      rcases hmem with h1 | h1
      · exact List.mem_append.mpr (Or.inl h1)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h1)))
    · simp [heq] at h
      by_cases heq2 : m.1 = msg.1
      · simp [heq2] at h
      · simp [heq2] at h
        have hsub := ih (seen ++ [m]) h
        intro x hx
        have hx' := hsub x hx
        rw [List.mem_append] at hx' ⊢
        rcases hx' with h1 | h1
        · rw [List.mem_append] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · rw [List.mem_singleton] at h1
            subst h1
            exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · exact Or.inr (List.mem_cons.mpr (Or.inr h1))

/-- Members of a `Queue.dequeue` result come from the original queue. -/
private lemma Queue.dequeue_mem_subset (Q : Queue) (msg : QueueMessage) (Q' : Queue)
    (h : Q.dequeue msg = some Q') : ∀ x ∈ Q', x ∈ Q := by
  have hsub := Queue.dequeue.go_mem_subset [] Q msg Q' h
  intro x hx
  have := hsub x hx
  simpa using this

/-- A successful `dequeue.go` scan drops exactly one message. -/
private lemma Queue.dequeue.go_length (seen left : Queue) (msg : QueueMessage) (Q' : Queue)
    (h : Queue.dequeue.go seen left msg = some Q') :
    Q'.length + 1 = seen.length + left.length := by
  induction left generalizing seen Q' with
  | nil => simp [Queue.dequeue.go] at h
  | cons m rest ih =>
    by_cases hm : m = msg
    · subst hm
      simp [Queue.dequeue.go] at h
      subst h
      simp [List.length_append]
      omega
    · by_cases hs : m.1 = msg.1
      · simp [Queue.dequeue.go, hm, hs] at h
      · simp [Queue.dequeue.go, hm, hs] at h
        have hih := ih _ _ h
        simp at hih ⊢
        omega

/-- A successful `dequeue` drops exactly one message (needed for the queue-mass
    measure in the infiniteness-source argument). -/
lemma Queue.dequeue_length_drop {Q : Queue} {msg : QueueMessage} {Q' : Queue}
    (h : Q.dequeue msg = some Q') : Q'.length + 1 = Q.length := by
  unfold Queue.dequeue at h
  have hgo := Queue.dequeue.go_length [] Q msg Q' h
  simpa using hgo

/-- A `send` step keeps the queue. -/
lemma sq_trans_send_queue {stq stq' : SessionTypeWithQueue} {p : Role}
    {lab : Lab} {S : DataSort} (h : sq_trans stq (sq_action.send p lab S) stq') :
    stq'.2 = stq.2 := by
  cases h with
  | send hST => rfl

/-- A `recv` step appends the sender's message, keeping the session type. -/
lemma sq_trans_recv_shape {stq stq' : SessionTypeWithQueue} {p : Role}
    {lab : Lab} {S : DataSort} (h : sq_trans stq (sq_action.recv p lab S) stq') :
    stq' = (stq.1, stq.2 ++ [QueueMessage.msg p lab S]) := by
  cases h with
  | recv => rfl

/-- A `dequeue` step only removes a message: members of the new queue were already queued. -/
private lemma sq_trans_dequeue_mem_subset {stq stq' : SessionTypeWithQueue} {p : Role}
    {lab : Lab} {S : DataSort} (h : sq_trans stq (sq_action.dequeue p lab S) stq') :
    ∀ x ∈ stq'.2, x ∈ stq.2 := by
  cases h with
  | @dequeue T T' Q Q' pp ll SS hST hQ =>
    exact Queue.dequeue_mem_subset Q _ Q' hQ

/-- Replacing a role's session type with queue by a well-formed one preserves
    network well-formedness, provided the new queue introduces no foreign senders
    (every sender in the new queue already occurs in the replaced network). -/
private lemma networkReplace_wellFormed {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    (hWF : Network.WellFormed N) (hstq : SessionTypeWithQueue.WellFormed stq)
    (has_cover : ∀ (p : Role) (lab : Lab) (S : DataSort),
      QueueMessage.msg p lab S ∈ stq.2 → ∃ stq', (p, stq') ∈ Network.replace N r stq) :
    Network.WellFormed (Network.replace N r stq) := by
  unfold Network.WellFormed at hWF ⊢
  rcases hWF with ⟨hNodup, hAll, hClosed⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold Network.replace
    simp [List.nodup_cons]
    exact hNodup.sublist
      ((List.filter_sublist (p := fun x : Role × SessionTypeWithQueue => x.1 != r) (l := N)).map
        (fun x : Role × SessionTypeWithQueue => x.1))
  · intro x hx
    unfold Network.replace at hx
    rw [List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [hx]
      simpa [SessionTypeWithQueue.WellFormed] using hstq
    · rw [List.mem_filter] at hx
      exact hAll x hx.1
  · intro q0 T0 Q0 p0 lab0 S0 hmem hqmem
    unfold Network.replace at hmem
    rw [List.mem_cons] at hmem
    rcases hmem with hmem | hmem
    · have heq : (q0, (T0, Q0)) = (r, stq) := hmem
      have hQ0 : Q0 = stq.2 := congrArg (fun y : Role × SessionTypeWithQueue => y.2.2) heq
      subst hQ0
      exact has_cover p0 lab0 S0 hqmem
    · rw [List.mem_filter] at hmem
      obtain ⟨stq', hmem'⟩ := hClosed q0 T0 Q0 p0 lab0 S0 hmem.1 hqmem
      exact Network.role_preserved_replace hmem'

/-- If a network is well-formed and performs an internal transition,
    it remains well-formed (open `io_*` steps can introduce foreign senders,
    so preservation is stated for `τ` steps only — the `net_trans_star` domain). -/
lemma Network.wellFormedPreserved (N : Network) (α : net_label) (N' : Network)
  (hWF : N.WellFormed) (hTr : net_trans N α N') (hInt : is_internal_net_label α) :
  N'.WellFormed := by
  cases hTr with
  | @io_send r p stq stq' lab S h hm =>
    simp [is_internal_net_label] at hInt
  | @io_recv r p stq stq' lab S h hm =>
    simp [is_internal_net_label] at hInt
  | @dequeue r p0 stq0 stq0' lab0 S0 hSQ hmem0 =>
    have hstqWF : SessionTypeWithQueue.WellFormed stq0' := by
      apply SessionTypeWithQueue.wellFormedPreserved stq0
        (sq_action.dequeue p0 lab0 S0) stq0'
      · have h2 := hWF.2.1
        simpa [SessionTypeWithQueue.WellFormed] using h2 (r, stq0) hmem0
      · exact hSQ
    apply networkReplace_wellFormed hWF hstqWF
    intro p1 lab1 S1 hmemQ
    have hmemQ0 : QueueMessage.msg p1 lab1 S1 ∈ stq0.2 :=
      sq_trans_dequeue_mem_subset hSQ _ hmemQ
    obtain ⟨stq', hmem'⟩ := hWF.2.2 r stq0.1 stq0.2 p1 lab1 S1
      (by simpa using hmem0) hmemQ0
    exact Network.role_preserved_replace hmem'
  | @comm p q lab S stqp stqp' stqq stqq' _hne h_send h_recv hmem_p hmem_q =>
    have hstqpWF : SessionTypeWithQueue.WellFormed stqp' := by
      apply SessionTypeWithQueue.wellFormedPreserved stqp _ stqp'
      · have h2 := hWF.2.1
        simpa [SessionTypeWithQueue.WellFormed] using h2 (p, stqp) hmem_p
      · exact h_send
    have hMid : Network.WellFormed (Network.replace N p stqp') := by
      apply networkReplace_wellFormed hWF hstqpWF
      intro p1 lab1 S1 hmemQ
      have hQp := sq_trans_send_queue h_send
      rw [hQp] at hmemQ
      obtain ⟨stq', hmem'⟩ := hWF.2.2 p stqp.1 stqp.2 p1 lab1 S1
        (by simpa using hmem_p) hmemQ
      exact Network.role_preserved_replace hmem'
    have hstqqWF : SessionTypeWithQueue.WellFormed stqq' := by
      apply SessionTypeWithQueue.wellFormedPreserved stqq _ stqq'
      · have h2 := hWF.2.1
        simpa [SessionTypeWithQueue.WellFormed] using h2 (q, stqq) hmem_q
      · exact h_recv
    have hRecvEq := sq_trans_recv_shape h_recv
    subst hRecvEq
    apply networkReplace_wellFormed hMid hstqqWF
    intro p1 lab1 S1 hmemQ
    rw [List.mem_append] at hmemQ
    rcases hmemQ with hOld | hNew
    · obtain ⟨stq', hmem'⟩ := hWF.2.2 q stqq.1 stqq.2 p1 lab1 S1
        (by simpa using hmem_q) hOld
      obtain ⟨mid, hmid⟩ := Network.role_preserved_replace (r := p)
        (stq := stqp') hmem'
      exact Network.role_preserved_replace hmid
    · rw [List.mem_singleton] at hNew
      have hpeq : p1 = p := by
        have hcon := congrArg (fun m : QueueMessage => m.1) hNew
        simpa using hcon
      rw [hpeq]
      have hself : (p, stqp') ∈ Network.replace N p stqp' := by
        unfold Network.replace
        simp
      exact Network.role_preserved_replace hself


section OldestMessage

/-- A queue's oldest message from `p`: some split `Q = seen ++ [m] ++ rest`
    with `m` sent by `p` and a sender-free prefix. -/
def oldest_from (p : Role) (Q : Queue) (m : QueueMessage) : Prop :=
  ∃ seen rest : Queue, Q = seen ++ m :: rest ∧ m.1 = p ∧
    ∀ m' ∈ seen, m'.1 ≠ p

/-- Append left-cancellation, self-proved (no API risk). -/
theorem append_cancel_left' : ∀ (a b c : Queue),
    a ++ b = a ++ c → b = c := by
  intro a
  induction a with
  | nil =>
    intro b c h
    simpa using h
  | cons x a' ih =>
    intro b c h
    simp at h
    exact h



/-- Prefixes of one list are comparable (plain induction). -/
theorem prefix_comparable : ∀ (a b : Queue) (X Y : Queue),
    a ++ X = b ++ Y → (∃ Z, b = a ++ Z) ∨ (∃ Z, a = b ++ Z) := by
  intro a
  induction a with
  | nil =>
    intro b X Y h
    exact Or.inl ⟨b, by simp⟩
  | cons x a' ih =>
    intro b X Y h
    cases b with
    | nil => exact Or.inr ⟨x :: a', by simp⟩
    | cons y b' =>
      simp at h
      obtain ⟨rfl, htail⟩ := h
      rcases ih _ _ _ htail with ⟨Z, hZ⟩ | ⟨Z, hZ⟩
      · exact Or.inl ⟨Z, by simp [hZ, List.cons_append]⟩
      · exact Or.inr ⟨Z, by simp [hZ, List.cons_append]⟩



/-- Oldest-sender messages are unique: two sender-free prefixes of one
    queue force the same oldest message. -/
theorem oldest_unique {p : Role} {Q : Queue} {m0 f : QueueMessage}
    {seen rest seen2 left2 : Queue}
    (hQ : Q = seen ++ m0 :: rest) (hf0 : ∀ x ∈ seen, x.1 ≠ p)
    (hQ2 : Q = seen2 ++ f :: left2) (hf2 : ∀ x ∈ seen2, x.1 ≠ p)
    (hm0 : m0.1 = p) (hf : f.1 = p) : m0 = f := by
  have h := hQ.symm.trans hQ2
  have hcomp := prefix_comparable seen seen2 (m0 :: rest) (f :: left2) h
  rcases hcomp with ⟨Z, hZ⟩ | ⟨Z, hZ⟩
  · rw [hZ, List.append_assoc] at h
    have hcan := append_cancel_left' seen _ _ h
    cases Z with
    | nil =>
      simp at hcan
      exact hcan.1
    | cons z0 Z' =>
      simp at hcan
      obtain ⟨hz0, -⟩ := hcan
      have hmem : z0 ∈ seen2 := by rw [hZ]; simp
      have hne := hf2 z0 hmem
      rw [← hz0] at hne
      exact absurd hm0 hne
  · rw [hZ, List.append_assoc] at h
    have hcan := append_cancel_left' seen2 _ _ h
    cases Z with
    | nil =>
      simp at hcan
      exact hcan.1
    | cons z0 Z' =>
      simp at hcan
      obtain ⟨hz0, -⟩ := hcan
      subst hz0
      have hmem : z0 ∈ seen := by rw [hZ]; simp
      have hne := hf0 z0 hmem
      exact absurd hf hne



/-- Oldest messages are unique (packaged over `oldest_from`). -/
theorem oldest_from_unique {p : Role} {Q : Queue} {m0 f : QueueMessage}
    (h0 : oldest_from p Q m0) (h1 : oldest_from p Q f) : m0 = f := by
  obtain ⟨seen, rest, hQ, hm0, hf0⟩ := h0
  obtain ⟨seen2, left2, hQ2, hmf, hf2⟩ := h1
  exact oldest_unique hQ hf0 hQ2 hf2 hm0 hmf




/-- Any queue containing a `p`-message has an oldest `p`-message. -/
theorem oldest_of_mem (Q : Queue) (p : Role) :
    (∃ m ∈ Q, m.1 = p) → ∃ m, oldest_from p Q m ∧ m.1 = p := by
  induction Q with
  | nil =>
    intro h
    obtain ⟨m, hmem, -⟩ := h
    simp at hmem
  | cons m0 rest ih =>
    intro h
    by_cases h0 : m0.1 = p
    · exact ⟨m0, ⟨[], rest, rfl, h0, fun _ h => by simp at h⟩, h0⟩
    · obtain ⟨m, hmem, hm1⟩ := h
      simp at hmem
      rcases hmem with rfl | hmemR
      · exact absurd hm1 h0
      · obtain ⟨m', hOld, hm1'⟩ := ih ⟨m, hmemR, hm1⟩
        obtain ⟨seen, rest', hQeq, hm1b, hseen⟩ := hOld
        refine ⟨m', ⟨m0 :: seen, rest', by rw [hQeq, List.cons_append], hm1', ?_⟩,
          hm1'⟩
        intro x hx
        simp at hx
        rcases hx with rfl | hx
        · exact h0
        · exact hseen x hx


end OldestMessage
