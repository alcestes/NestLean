import Nest.NetworkLTS
import Nest.NetworkLiveness
import Nest.MonitorLTSCo
import Nest.MonitorCoRel

/-!
# ProofUtils: shared machinery for the NEST testbed examples.

Reusable infrastructure for proving, about each concrete example network,
`Network.WellFormed`, `Network.NoSelf`, `Network.RolesPresent`,
`IsHalfDuplex`, `IsOutputLiveNetwork`, and
`consistentInstrumentation_co _ = some _`:
- `rolesOf` (role occurrences as a computable list) with `occurs_mem`,
  discharging `NoSelf` premises and `RolesPresent` membership facts by `decide`;
- an all-empty-queues sender-closure lemma;
- the session-type dichotomy (`st_trans` out vs. `inp`): a type that can
  take an output step cannot take an input step;
- fairness helpers used by the output-liveness arguments.
-/

-- ================================================================
-- Role occurrences as a computable list.
-- ================================================================

/-- Roles occurring in a session type (senders + owners, recursively). -/
def rolesOf : SessionType → List Role
  | .tEnd => []
  | .tVar _ => []
  | .internalChoice bs => goInt bs
  | .externalChoice p bs => p :: goExt bs
  | .tRec _ B => rolesOf B
where
  goInt : List (Role × Lab × DataSort × SessionType) → List Role
    | [] => []
    | ((p, _, _, T) :: rest) => p :: rolesOf T ++ goInt rest
  goExt : List (Lab × DataSort × SessionType) → List Role
    | [] => []
    | ((_, _, T) :: rest) => rolesOf T ++ goExt rest

theorem mem_goInt_sender {bs : List (Role × Lab × DataSort × SessionType)}
    {p : Role} {lab : Lab} {S : DataSort} {T : SessionType}
    (h : (p, lab, S, T) ∈ bs) : p ∈ rolesOf.goInt bs := by
  induction bs with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨p', lab', S', T'⟩ := hd
    rw [List.mem_cons] at h
    rcases h with h | hmem
    · cases h
      exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (ih hmem))))

theorem mem_goInt_target {bs : List (Role × Lab × DataSort × SessionType)}
    {x : Role × Lab × DataSort × SessionType} {r : Role}
    (hmem : x ∈ bs) (h : r ∈ rolesOf x.2.2.2) : r ∈ rolesOf.goInt bs := by
  induction bs with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨p', lab', S', T'⟩ := hd
    obtain ⟨p, lab, S, T⟩ := x
    rw [List.mem_cons] at hmem
    rcases hmem with h | hmem
    · cases h
      exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (ih hmem))))

theorem mem_goExt_target {bs : List (Lab × DataSort × SessionType)}
    {x : Lab × DataSort × SessionType} {r : Role}
    (hmem : x ∈ bs) (h : r ∈ rolesOf x.2.2) : r ∈ rolesOf.goExt bs := by
  induction bs with
  | nil => simp at hmem
  | cons hd tl ih =>
    obtain ⟨lab', S', T'⟩ := hd
    obtain ⟨lab, S, T⟩ := x
    rw [List.mem_cons] at hmem
    rcases hmem with h | hmem
    · cases h
      exact List.mem_append.mpr (Or.inl h)
    · exact List.mem_append.mpr (Or.inr (ih hmem))

/-- Every role occurring in a type is listed by `rolesOf`. -/
theorem occurs_mem {r : Role} {T : SessionType} (h : SessionType.Occurs r T) :
    r ∈ rolesOf T := by
  induction h with
  | intSender hmem heq =>
    subst heq
    exact mem_goInt_sender hmem
  | intTarget hmem _ ih =>
    simp only [rolesOf]
    exact mem_goInt_target hmem ih
  | extOwner heq =>
    subst heq
    exact List.mem_cons.mpr (Or.inl rfl)
  | extTarget hmem _ ih =>
    simp only [rolesOf]
    exact List.mem_cons.mpr (Or.inr (mem_goExt_target hmem ih))
  | recBody _ ih =>
    simp only [rolesOf]
    exact ih

/-- A network has no self-mention when no entry's role occurs in its own type. -/
theorem Network.NoSelf_of_rolesOf {N : Network}
    (h : ∀ x ∈ N, x.1 ∉ rolesOf x.2.1) : N.NoSelf := by
  intro q T Q hmem hOcc
  exact absurd (occurs_mem hOcc) (h _ hmem)

/-- A network with all queues empty is sender-closed (vacuously). -/
theorem Network.SenderClosed_of_all_nil {N : Network}
    (h : ∀ x ∈ N, x.2.2 = []) : N.SenderClosed := by
  intro q T Q p lab S hmem hQ
  have hQ' : Q = [] := h _ hmem
  rw [hQ'] at hQ
  cases hQ

-- ================================================================
-- Permutation-invariant network facts.
-- ================================================================

/-- Two flat networks are equivalent when they differ only in list order. -/
def Network.Reordered (N M : Network) : Prop := N.Perm M

/-- Membership is invariant under reordering. -/
theorem Network.mem_reordered {N M : Network} (h : Network.Reordered N M)
    {x : Role × SessionTypeWithQueue} : x ∈ N ↔ x ∈ M := by
  exact h.mem_iff

/-- Queue ownership is invariant under reordering. -/
theorem Network.hasQueue_reordered {N M : Network} (h : Network.Reordered N M)
    {r : Role} {Q : Queue} : NetworkHasQueue N r Q ↔ NetworkHasQueue M r Q := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, (Network.mem_reordered h).mp hT⟩
  · rintro ⟨T, hT⟩
    exact ⟨T, (Network.mem_reordered h).mpr hT⟩

/-- Queue-message membership is invariant under reordering of network entries. -/
theorem Network.queueContains_reordered {N M : Network}
    (h : Network.Reordered N M) :
    (∀ r Q, NetworkHasQueue N r Q → QueueContainsFrom Q r) ↔
      (∀ r Q, NetworkHasQueue M r Q → QueueContainsFrom Q r) := by
  constructor <;> intro hall r Q hQ
  · exact hall r Q ((Network.hasQueue_reordered h).mpr hQ)
  · exact hall r Q ((Network.hasQueue_reordered h).mp hQ)

/-- Replacing the same role preserves reordering equivalence. -/
theorem Network.replace_reordered {N M : Network} (h : Network.Reordered N M)
    (r : Role) (stq : SessionTypeWithQueue) :
    Network.Reordered (N.replace r stq) (M.replace r stq) := by
  unfold Network.Reordered Network.replace
  exact List.Perm.cons _ (List.Perm.filter _ h)

/-- Internal network transitions are equivariant under reordering. -/
theorem net_trans_reordered {N M N' : Network} {δ : net_label}
    (hNM : Network.Reordered N M) (hTr : net_trans N δ N') :
    ∃ M', net_trans M δ M' ∧ Network.Reordered N' M' := by
  cases hTr with
  | @io_send r p stq stq' lab S hSQ hmem =>
    have hmem' := (Network.mem_reordered hNM).mp hmem
    refine ⟨M.replace _ _, net_trans.io_send hSQ hmem', ?_⟩
    exact Network.replace_reordered hNM _ _
  | @io_recv r p stq stq' lab S hSQ hmem =>
    have hmem' := (Network.mem_reordered hNM).mp hmem
    refine ⟨M.replace _ _, net_trans.io_recv hSQ hmem', ?_⟩
    exact Network.replace_reordered hNM _ _
  | @dequeue r p stq stq' lab S hSQ hmem =>
    have hmem' := (Network.mem_reordered hNM).mp hmem
    refine ⟨M.replace _ _, net_trans.dequeue hSQ hmem', ?_⟩
    exact Network.replace_reordered hNM _ _
  | @comm p q lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    have hmem_p' := (Network.mem_reordered hNM).mp hmem_p
    have hmem_q' := (Network.mem_reordered hNM).mp hmem_q
    have h1 : Network.Reordered (N.replace p stqp') (M.replace p stqp') :=
      Network.replace_reordered hNM p stqp'
    have h2 : Network.Reordered ((N.replace p stqp').replace q stqq')
        ((M.replace p stqp').replace q stqq') :=
      Network.replace_reordered h1 q stqq'
    refine ⟨((M.replace p stqp').replace q stqq'),
      net_trans.comm hne h_send h_recv hmem_p' hmem_q', h2⟩

/-- Internal transition stars are equivariant under reordering. -/
theorem net_trans_star_reordered {N M N' : Network}
    (hNM : Network.Reordered N M) (hStar : net_trans_star N N') :
    ∃ M', net_trans_star M M' ∧ Network.Reordered N' M' := by
  induction hStar generalizing M with
  | refl => exact ⟨M, net_trans_star.refl M, hNM⟩
  | @step N1 N2 N3 δ hInt hTr hTail ih =>
    obtain ⟨M2, hTr', hPerm2⟩ := net_trans_reordered hNM hTr
    obtain ⟨M3, hTail', hPerm3⟩ := ih hPerm2
    exact ⟨M3, net_trans_star.step hInt hTr' hTail', hPerm3⟩

/-- No-orphan status is invariant under reordering of network entries. -/
theorem noOrphanMessages_reordered {N M : Network}
    (h : Network.Reordered N M) : NoOrphanMessages N ↔ NoOrphanMessages M := by
  constructor <;> intro hNo r T Q p lab S Q' hmem hQ
  · exact hNo r T Q p lab S Q' ((Network.mem_reordered h).mpr hmem) hQ
  · exact hNo r T Q p lab S Q' ((Network.mem_reordered h).mp hmem) hQ

/-- Reordering is reflexive, symmetric, and transitive. -/
theorem Network.Reordered_rfl (N : Network) : Network.Reordered N N :=
  List.Perm.refl _

theorem Network.Reordered_symm {N M : Network}
    (h : Network.Reordered N M) : Network.Reordered M N :=
  List.Perm.symm h

theorem Network.Reordered_trans {N M K : Network}
    (h1 : Network.Reordered N M) (h2 : Network.Reordered M K) :
    Network.Reordered N K :=
  List.Perm.trans h1 h2

/-- Insertion into a role-sorted network. -/
def Network.canonInsert (x : Role × SessionTypeWithQueue) : Network → Network
  | [] => [x]
  | y :: ys => if decide (x.1 ≤ y.1) then x :: y :: ys else y :: Network.canonInsert x ys

/-- Canonical representative: the same entries sorted by role. -/
def Network.canon : Network → Network
  | [] => []
  | x :: xs => Network.canonInsert x (Network.canon xs)

/-- Insertion preserves the multiset of entries. -/
theorem Network.canonInsert_perm (x : Role × SessionTypeWithQueue)
    (ys : Network) : (Network.canonInsert x ys).Perm (x :: ys) := by
  induction ys with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    unfold Network.canonInsert
    split
    · exact List.Perm.refl _
    · exact (ih.cons y).trans (List.Perm.swap x y ys)

/-- Every network is a reordering of its canonical form. -/
theorem Network.canon_perm (N : Network) : Network.Reordered N (Network.canon N) := by
  unfold Network.Reordered
  induction N with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    unfold Network.canon
    exact (List.Perm.cons x ih).trans
      (List.Perm.symm (Network.canonInsert_perm x (Network.canon xs)))

/-- Half-duplex transfers across reordered networks. -/
theorem IsHalfDuplex_reordered {N M : Network} (h : Network.Reordered N M) :
    IsHalfDuplex N → IsHalfDuplex M := by
  intro hHD N' hStar p q Qp Qq hP hQ hPq hCq
  have hNM : Network.Reordered M N := List.Perm.symm h
  obtain ⟨N'', hStar'', hPerm⟩ := net_trans_star_reordered hNM hStar
  exact hHD N'' hStar'' p q Qp Qq
    ((Network.hasQueue_reordered hPerm).mp hP)
    ((Network.hasQueue_reordered hPerm).mp hQ) hPq hCq

/-- Being stuck transfers across reordered networks. -/
theorem IsStuckNetwork_reordered {N M : Network} (h : Network.Reordered N M) :
    IsStuckNetwork N ↔ IsStuckNetwork M := by
  constructor <;> intro hS hcon
  · obtain ⟨δ, M', hInt, hTr⟩ := hcon
    obtain ⟨N', hTr', _⟩ := net_trans_reordered (List.Perm.symm h) hTr
    exact hS ⟨δ, N', hInt, hTr'⟩
  · obtain ⟨δ, N', hInt, hTr⟩ := hcon
    obtain ⟨M', hTr', _⟩ := net_trans_reordered h hTr
    exact hS ⟨δ, M', hInt, hTr'⟩

-- ================================================================
-- Fuel-bounded executable session transitions.
-- ================================================================

/-- Boolean checker for one session-type transition. Fuel is consumed only
    when a recursive head is unfolded. -/
def st_transb : Nat → SessionType → st_label → SessionType → Bool
  | 0, _, _, _ => false
  | n + 1, SessionType.internalChoice bs, st_label.out p lab S, T =>
      bs.any (fun x =>
        decide (x.1 = p) && decide (x.2.1 = lab) &&
          decide (x.2.2.1 = S) && decide (x.2.2.2 = T))
  | n + 1, SessionType.externalChoice p bs, st_label.inp q lab S, T =>
      if p = q then
        bs.any (fun x =>
          decide (x.1 = lab) && decide (x.2.1 = S) && decide (x.2.2 = T))
      else false
  | n + 1, SessionType.tRec X B, α, T' =>
      st_transb n (substSessionType B X (SessionType.tRec X B)) α T'
  | _, _, _, _ => false

/-- A true bounded session-transition check produces an `st_trans` proof. -/
theorem st_transb_sound {n : Nat} {T T' : SessionType} {α : st_label}
    (h : st_transb n T α T' = true) : st_trans T α T' := by
  induction n generalizing T T' α with
  | zero => simp [st_transb] at h
  | succ n ih =>
    cases T with
    | tEnd => simp [st_transb] at h
    | tVar X => simp [st_transb] at h
    | internalChoice bs =>
      cases α with
      | tau => simp [st_transb] at h
      | inp q lab S => simp [st_transb] at h
      | out p lab S =>
        simp only [st_transb, List.any_eq_true] at h
        obtain ⟨x, hx, hval⟩ := h
        simp only [Bool.and_eq_true] at hval
        rcases hval with ⟨⟨⟨hp, hl⟩, hs⟩, ht⟩
        have hp' := of_decide_eq_true hp
        have hl' := of_decide_eq_true hl
        have hs' := of_decide_eq_true hs
        have ht' := of_decide_eq_true ht
        cases hp'; cases hl'; cases hs'; cases ht'
        exact st_trans.intC hx
    | externalChoice p bs =>
      cases α with
      | tau => simp [st_transb] at h
      | out q lab S => simp [st_transb] at h
      | inp q lab S =>
        simp only [st_transb] at h
        split at h
        · simp only [List.any_eq_true] at h
          subst q
          obtain ⟨x, hx, hval⟩ := h
          simp only [Bool.and_eq_true] at hval
          rcases hval with ⟨⟨hl, hs⟩, ht⟩
          have hl' := of_decide_eq_true hl
          have hs' := of_decide_eq_true hs
          have ht' := of_decide_eq_true ht
          cases hl'; cases hs'; cases ht'
          exact st_trans.extC hx
        · simp at h
    | tRec X B =>
      exact st_trans.tRec (ih h)

/-- Every `st_trans` derivation is found at some finite fuel. -/
theorem st_transb_complete {T T' : SessionType} {α : st_label}
    (h : st_trans T α T') : ∃ n, st_transb n T α T' = true := by
  induction h with
  | intC hmem =>
    refine ⟨1, ?_⟩
    simp [st_transb, hmem]
  | extC hmem =>
    refine ⟨1, ?_⟩
    simp [st_transb, hmem]
  | tRec h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simpa [st_transb] using hn⟩

/-- Boolean checker for one session-with-queue transition. -/
def sq_transb (fuel : Nat) (stq : SessionTypeWithQueue) (α : sq_action)
    (stq' : SessionTypeWithQueue) : Bool :=
  match stq, stq', α with
  | (T, Q), (T', Q'), sq_action.send p lab S =>
      st_transb fuel T (st_label.out p lab S) T' && decide (Q' = Q)
  | (T, Q), (T', Q'), sq_action.dequeue p lab S =>
      st_transb fuel T (st_label.inp p lab S) T' &&
        decide (Q.dequeue (QueueMessage.msg p lab S) = some Q')
  | (T, Q), (T', Q'), sq_action.recv p lab S =>
      decide (T' = T ∧ Q' = Q ++ [QueueMessage.msg p lab S])

/-- A true bounded queue-transition check produces an `sq_trans` proof. -/
theorem sq_transb_sound {n : Nat} {stq stq' : SessionTypeWithQueue} {α : sq_action}
    (h : sq_transb n stq α stq' = true) : sq_trans stq α stq' := by
  cases stq with
  | mk T Q =>
    cases stq' with
    | mk T' Q' =>
      cases α with
      | send p lab S =>
        simp only [sq_transb, Bool.and_eq_true] at h
        have hQ := of_decide_eq_true h.2
        subst Q'
        exact sq_trans.send (st_transb_sound h.1)
      | dequeue p lab S =>
        simp only [sq_transb, Bool.and_eq_true] at h
        exact sq_trans.dequeue (st_transb_sound h.1) (of_decide_eq_true h.2)
      | recv p lab S =>
        simp only [sq_transb, decide_eq_true_eq] at h
        rcases h with ⟨rfl, rfl⟩
        exact sq_trans.recv

/-- Every `sq_trans` derivation is found at some finite fuel. -/
theorem sq_transb_complete {stq stq' : SessionTypeWithQueue} {α : sq_action}
    (h : sq_trans stq α stq') : ∃ n, sq_transb n stq α stq' = true := by
  cases h with
  | send hST =>
    obtain ⟨n, hn⟩ := st_transb_complete hST
    exact ⟨n, by simp [sq_transb, hn]⟩
  | dequeue hST hQ =>
    obtain ⟨n, hn⟩ := st_transb_complete hST
    exact ⟨n, by simp [sq_transb, hn, hQ]⟩
  | recv =>
    exact ⟨0, by simp [sq_transb]⟩

/-- Executable lookup of a role's session entry. -/
def networkLookup : Network → Role → Option SessionTypeWithQueue
  | [], _ => none
  | (r, stq) :: rest, q => if r == q then some stq else networkLookup rest q

/-- A successful lookup identifies an actual network entry. -/
theorem networkLookup_mem {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    (h : networkLookup N r = some stq) : (r, stq) ∈ N := by
  induction N with
  | nil => simp [networkLookup] at h
  | cons hd rest ih =>
    rcases hd with ⟨r0, stq0⟩
    by_cases heq : r0 == r
    · have her : r0 = r := of_decide_eq_true heq
      subst r0
      simp [networkLookup] at h
      obtain rfl := h
      simp
    · simp [networkLookup, heq] at h
      exact List.mem_cons.mpr (Or.inr (ih h))

/-- With unique roles, every network entry is returned by lookup. -/
theorem networkLookup_some_of_mem {N : Network} {r : Role}
    (hnd : (N.map Prod.fst).Nodup) {stq : SessionTypeWithQueue}
    (hmem : (r, stq) ∈ N) : networkLookup N r = some stq := by
  induction N with
  | nil => simp at hmem
  | cons hd rest ih =>
    rcases hd with ⟨r0, stq0⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases hnd with ⟨hnot, hrest⟩
    simp only [List.mem_cons] at hmem
    by_cases heq : r0 = r
    · rcases hmem with hmem | hmem
      · cases hmem
        simp [networkLookup, heq]
      · exfalso
        apply hnot
        exact List.mem_map.mpr ⟨(r, stq), hmem, by exact heq.symm⟩
    · rcases hmem with hmem | hmem
      · exfalso
        exact heq (congrArg Prod.fst hmem).symm
      · simp [networkLookup, heq, ih hrest hmem]

/-- Lookup after replacing a role finds the new entry. -/
theorem networkLookup_replace {N : Network} {r : Role}
    (stq : SessionTypeWithQueue) :
    networkLookup (N.replace r stq) r = some stq := by
  unfold Network.replace
  simp only [networkLookup]
  simp

/-- Executable checker for a concrete network transition. The checker uses
    exact `Network.replace` equality, so it does not quotient away semantics;
    list-order quotienting is handled separately by `Network.Reordered`. -/
def net_transb (fuel : Nat) (N : Network) (δ : net_label) (N' : Network) : Bool :=
  match δ with
  | net_label.io_send r p lab S =>
      match networkLookup N r, networkLookup N' r with
      | some stq, some stq' =>
          sq_transb fuel stq (sq_action.send p lab S) stq' &&
            decide (N' = N.replace r stq')
      | _, _ => false
  | net_label.io_recv r p lab S =>
      match networkLookup N r, networkLookup N' r with
      | some stq, some stq' =>
          sq_transb fuel stq (sq_action.recv p lab S) stq' &&
            decide (N' = N.replace r stq')
      | _, _ => false
  | net_label.τ_dequeue r p lab S =>
      match networkLookup N r, networkLookup N' r with
      | some stq, some stq' =>
          sq_transb fuel stq (sq_action.dequeue p lab S) stq' &&
            decide (N' = N.replace r stq')
      | _, _ => false
  | net_label.τ_comm p q lab S =>
      match networkLookup N p, networkLookup N q,
        networkLookup N' p, networkLookup N' q with
      | some stqp, some stqq, some stqp', some stqq' =>
          sq_transb fuel stqp (sq_action.send q lab S) stqp' &&
          sq_transb fuel stqq (sq_action.recv p lab S) stqq' &&
          decide (p ≠ q) &&
          decide (N' = (N.replace p stqp').replace q stqq')
      | _, _, _, _ => false

/-- Soundness of the executable checker for single-entry transitions. -/
theorem net_transb_single_sound {fuel : Nat} {N N' : Network} {r p : Role}
    {lab : Lab} {S : DataSort}
    (hnd : (N.map Prod.fst).Nodup)
    (h : net_transb fuel N (net_label.τ_dequeue r p lab S) N' = true) :
    net_trans N (net_label.τ_dequeue r p lab S) N' := by
  simp only [net_transb] at h
  split at h <;> simp at h
  rename_i stq stq' hin hout
  have hsq : sq_trans stq (sq_action.dequeue p lab S) stq' :=
    sq_transb_sound h.1
  have hEq : N' = N.replace r stq' := h.2
  subst N'
  exact net_trans.dequeue hsq (networkLookup_mem hin)

/-- Soundness of the executable checker for an internal receive step. -/
theorem net_transb_recv_sound {fuel : Nat} {N N' : Network} {r p : Role}
    {lab : Lab} {S : DataSort}
    (h : net_transb fuel N (net_label.io_recv r p lab S) N' = true) :
    net_trans N (net_label.io_recv r p lab S) N' := by
  simp only [net_transb] at h
  split at h <;> simp at h
  rename_i stq stq' hin hout
  have hsq : sq_trans stq (sq_action.recv p lab S) stq' :=
    sq_transb_sound h.1
  have hEq : N' = N.replace r stq' := h.2
  subst N'
  exact net_trans.io_recv hsq (networkLookup_mem hin)

/-- Soundness of the executable checker for an internal send step. -/
theorem net_transb_send_sound {fuel : Nat} {N N' : Network} {r p : Role}
    {lab : Lab} {S : DataSort}
    (h : net_transb fuel N (net_label.io_send r p lab S) N' = true) :
    net_trans N (net_label.io_send r p lab S) N' := by
  simp only [net_transb] at h
  split at h <;> simp at h
  rename_i stq stq' hin hout
  have hsq : sq_trans stq (sq_action.send p lab S) stq' :=
    sq_transb_sound h.1
  have hEq : N' = N.replace r stq' := h.2
  subst N'
  exact net_trans.io_send hsq (networkLookup_mem hin)

/-- Soundness of the executable checker for a communication step. -/
theorem net_transb_comm_sound {fuel : Nat} {N N' : Network} {p q : Role}
    {lab : Lab} {S : DataSort}
    (h : net_transb fuel N (net_label.τ_comm p q lab S) N' = true) :
    net_trans N (net_label.τ_comm p q lab S) N' := by
  simp only [net_transb] at h
  split at h <;> simp at h
  rename_i stqp stqq stqp' stqq' hinp hinq houtp houtq
  have hs : sq_trans stqp (sq_action.send q lab S) stqp' :=
    sq_transb_sound h.1.1.1
  have hr : sq_trans stqq (sq_action.recv p lab S) stqq' :=
    sq_transb_sound h.1.1.2
  have hpq : p ≠ q := h.1.2
  have hEq : N' = (N.replace p stqp').replace q stqq' := h.2
  subst N'
  exact net_trans.comm hpq hs hr (networkLookup_mem hinp) (networkLookup_mem hinq)

/-- A successful dequeue implies the message was queued. -/
theorem Queue.dequeue_mem {Q : Queue} {msg : QueueMessage} {Q' : Queue}
    (h : Q.dequeue msg = some Q') : msg ∈ Q := by
  have key : ∀ (seen left : Queue) (Q' : Queue),
      Queue.dequeue.go seen left msg = some Q' → msg ∈ seen ++ left := by
    intro seen left
    induction left generalizing seen with
    | nil =>
      intro Q' h
      simp [Queue.dequeue.go] at h
    | cons m rest ih =>
      intro Q' h
      simp only [Queue.dequeue.go] at h
      by_cases heq : m = msg
      · subst heq
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      · simp only [heq, ↓reduceIte] at h
        by_cases heq2 : m.1 = msg.1
        · simp [heq2] at h
        · simp only [heq2, ↓reduceIte] at h
          have hmem := ih (seen ++ [m]) Q' h
          rw [List.append_assoc] at hmem
          exact hmem
  have hmem := key [] Q Q' h
  simpa using hmem

/-- An empty queue contains messages from no role. -/
theorem noContainsNil {r : Role} : ¬ QueueContainsFrom ([] : Queue) r := by
  rintro ⟨_, _, h⟩
  cases h

/-- Queue membership implies list membership. -/
theorem QueueMem.to_mem {m : QueueMessage} {Q : Queue}
    (h : QueueMem m Q) : m ∈ Q := by
  induction h with
  | head => exact List.mem_cons.mpr (Or.inl rfl)
  | tail _ ih => exact List.mem_cons.mpr (Or.inr ih)

/-- Reachability along an infinite path (each prefix is a τ-star). -/
theorem path_star_reachable {π : InfiniteNetworkPath} {Ni : Network}
    (h0 : π.seq 0 = Ni) (i : ℕ) : net_trans_star Ni (π.seq i) := by
  induction i with
  | zero => rw [h0]; exact net_trans_star.refl _
  | succ k ih =>
    have hTr := π.δ_tr k
    obtain ⟨r, p, lab, S, h | h⟩ := π.δ_form k
    · rw [h] at hTr
      exact net_trans_star.trans ih
        (net_trans_star.step (by trivial) hTr (net_trans_star.refl _))
    · rw [h] at hTr
      exact net_trans_star.trans ih
        (net_trans_star.step (by trivial) hTr (net_trans_star.refl _))

-- ================================================================
-- Session-type dichotomy: no step is both an output and an input step.
-- ================================================================

/-- A session type that can take an output step cannot take an input step.
    (By induction on the output derivation; the head constructor determines
    the label kind, and `tRec` unfolding is deterministic.) -/
theorem st_trans_out_ne_inp {T T' T'' : SessionType} {p q : Role}
    {lab lab' : Lab} {S S' : DataSort}
    (hOut : st_trans T (st_label.out p lab S) T')
    (hIn : st_trans T (st_label.inp q lab' S') T'') : False := by
  revert hIn
  generalize hlbl : st_label.out p lab S = l at hOut
  induction hOut with
  | intC hmem =>
    intro hIn
    cases hIn
  | extC hmem =>
    cases hlbl
  | tRec hST ih =>
    intro hIn
    cases hIn with
    | tRec hIn' => exact ih hlbl hIn'

-- ================================================================
-- Consistent instrumentation for empty-queue networks.
-- ================================================================

/-- The coinductive fold of an empty queue is witnessed by the type itself. -/
theorem exists_monitor_fold_val_partial_co_nil (T : SessionType) :
    ∃ M, monitor_fold_val_partial_co (T, []) = some M := by
  have hex : ∃ T', monitor_fold_co (T, []) T' := ⟨T, rfl⟩
  unfold monitor_fold_val_partial_co
  rw [dif_pos hex]
  exact ⟨_, rfl⟩

/-- Every all-empty-queue network admits a consistent coinductive
    instrumentation (by induction on the network; the fold of `[]` is
    always defined). -/
theorem exists_consistentInstrumentation_co_of_all_nil (N : Network)
    (h : ∀ x ∈ N, x.2.2 = []) : ∃ MN, consistentInstrumentation_co N = some MN := by
  induction N with
  | nil => exact ⟨_, rfl⟩
  | cons hd tl ih =>
    obtain ⟨r, T, Q⟩ := hd
    have hQ : Q = [] := h _ (List.mem_cons.mpr (Or.inl rfl))
    subst hQ
    obtain ⟨M, hM⟩ := exists_monitor_fold_val_partial_co_nil T
    obtain ⟨MN, hMN⟩ := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    exact ⟨_, by rw [consistentInstrumentation_co, hM, hMN]⟩

/-- Restatement of half-duplex with explicit role/queue witnesses. -/
theorem IsHalfDuplex_pairwise {N : Network} (hHD : IsHalfDuplex N)
    {N' : Network} (hStar : net_trans_star N N')
    {p q : Role} {Qp Qq : Queue}
    (hP : NetworkHasQueue N' p Qp) (hQ : NetworkHasQueue N' q Qq)
    (hPq : QueueContainsFrom Qp q) : ¬ QueueContainsFrom Qq p :=
  hHD N' hStar p q Qp Qq hP hQ hPq

/-- An enabled monitored dequeue eventually fires along a fair path. -/
theorem fair_fires_dequeue {path : InfiniteNetworkPath} (hfair : IsFair path)
    {i : ℕ} {r p : Role} {lab : Lab} {S : DataSort} {N' : Network}
    (hTr : net_trans (path.seq i) (net_label.τ_dequeue r p lab S) N') :
    ∃ k : ℕ, i ≤ k ∧ path.δ k = net_label.τ_dequeue r p lab S := by
  -- Fairness condition (2): an enabled dequeue eventually occurs.
  exact (hfair i).2 r p lab S ⟨N', hTr⟩

/-- An enabled monitored communication eventually fires along a fair path. -/
theorem fair_fires_comm {path : InfiniteNetworkPath} (hfair : IsFair path)
    {i : ℕ} {p q : Role} {lab : Lab} {S : DataSort} {N' : Network}
    (hTr : net_trans (path.seq i) (net_label.τ_comm p q lab S) N') :
    ∃ (k : ℕ), i ≤ k ∧
      (∃ (qq : Role) (labb : Lab) (SS : DataSort),
        path.δ k = net_label.τ_comm p qq labb SS) := by
  -- Fairness condition (1): communicating roles eventually communicate.
  exact (hfair i).1 p ⟨q, lab, S, N', hTr⟩

-- ================================================================
-- Lookup after replacement (replace-output membership certificates).
-- ================================================================

-- These close the network-level completeness gap noted in the module
-- header: looking up the *target* of a `Network.replace` (possibly a
-- double replace for `τ_comm`) returns the installed entry, and lookups
-- of untouched roles see through the replacement.

/-- Filtering out one role preserves lookup of every other role. -/
theorem networkLookup_filter_other {N : Network} {r r0 : Role}
    (hne : r ≠ r0) :
    networkLookup (N.filter fun x : Role × SessionTypeWithQueue => x.1 != r0) r =
      networkLookup N r := by
  induction N with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨r0', stq0⟩ := hd
    by_cases hf : r0' = r0
    · have hdrop : ((r0', stq0).1 != r0) = false := by simp [hf]
      have e : (List.filter (fun x : Role × SessionTypeWithQueue => x.1 != r0)
          ((r0', stq0) :: tl)) =
          List.filter (fun x : Role × SessionTypeWithQueue => x.1 != r0) tl := by
        simp [hdrop]
      rw [e]
      by_cases heq : r0 = r
      · exact absurd heq (Ne.symm hne)
      · simp [networkLookup, hf, heq, ih]
    · have hkeep : ((r0', stq0).1 != r0) = true := by simp [hf]
      have e : (List.filter (fun x : Role × SessionTypeWithQueue => x.1 != r0)
          ((r0', stq0) :: tl)) = (r0', stq0) ::
          List.filter (fun x : Role × SessionTypeWithQueue => x.1 != r0) tl := by
        simp [hkeep]
      rw [e]
      by_cases heq : r0' = r
      · simp [networkLookup, heq]
      · simp [networkLookup, heq, ih]

/-- Looking up an untouched role sees through a replacement. -/
theorem networkLookup_replace_other {N : Network} {r r0 : Role}
    {stq0 : SessionTypeWithQueue} (hne : r ≠ r0) :
    networkLookup (N.replace r0 stq0) r = networkLookup N r := by
  unfold Network.replace
  by_cases heq : r0 = r
  · exact absurd heq (Ne.symm hne)
  · simp [networkLookup, heq, networkLookup_filter_other hne]

/-- After a double replace (communication step), the sender entry is found. -/
theorem networkLookup_double_replace_left {N : Network} {p q : Role}
    {stqp' stqq' : SessionTypeWithQueue} (hne : p ≠ q) :
    networkLookup ((N.replace p stqp').replace q stqq') p = some stqp' := by
  rw [networkLookup_replace_other hne]
  exact networkLookup_replace stqp'

/-- After a double replace (communication step), the receiver entry is found. -/
theorem networkLookup_double_replace_right {N : Network} {p q : Role}
    {stqp' stqq' : SessionTypeWithQueue} :
    networkLookup ((N.replace p stqp').replace q stqq') q = some stqq' :=
  networkLookup_replace stqq'

-- ================================================================
-- Fuel monotonicity for the executable checkers.
-- ================================================================

-- A check that succeeds at some fuel also succeeds at any larger fuel
-- (only `tRec` unfolding consumes fuel). This lets generated proofs pick
-- one uniform fuel (e.g. the maximum over an enumeration) for every
-- `net_transb` certificate.

/-- The session-type checker is monotone in fuel. -/
theorem st_transb_mono {n m : Nat} {T T' : SessionType} {α : st_label}
    (hle : n ≤ m) (h : st_transb n T α T' = true) :
    st_transb m T α T' = true := by
  induction n generalizing m T T' α with
  | zero => simp [st_transb] at h
  | succ n ih =>
    cases m with
    | zero => omega
    | succ k =>
      cases T with
      | tRec X B =>
        simp only [st_transb] at h ⊢
        exact ih (Nat.le_of_succ_le_succ hle) h
      | tEnd => simp [st_transb] at h
      | tVar X => simp [st_transb] at h
      | internalChoice bs =>
        cases α with
        | tau => simp [st_transb] at h
        | inp q lab S => simp [st_transb] at h
        | out p lab S => simpa [st_transb] using h
      | externalChoice p bs =>
        cases α with
        | tau => simp [st_transb] at h
        | out q lab S => simp [st_transb] at h
        | inp q lab S => simpa [st_transb] using h

/-- The session-with-queue checker is monotone in fuel. -/
theorem sq_transb_mono {n m : Nat} {stq stq' : SessionTypeWithQueue}
    {α : sq_action} (hle : n ≤ m) (h : sq_transb n stq α stq' = true) :
    sq_transb m stq α stq' = true := by
  cases stq with
  | mk T Q =>
    cases stq' with
    | mk T' Q' =>
      cases α with
      | send p lab S =>
        simp only [sq_transb, Bool.and_eq_true] at h ⊢
        exact ⟨st_transb_mono hle h.1, h.2⟩
      | dequeue p lab S =>
        simp only [sq_transb, Bool.and_eq_true] at h ⊢
        exact ⟨st_transb_mono hle h.1, h.2⟩
      | recv => simpa [sq_transb] using h

/-- The network checker is monotone in fuel. -/
theorem net_transb_mono {n m : Nat} {N N' : Network} {δ : net_label}
    (hle : n ≤ m) (h : net_transb n N δ N' = true) :
    net_transb m N δ N' = true := by
  cases δ with
  | io_send r p lab S =>
    cases hNr : networkLookup N r with
    | none =>
      cases hNr' : networkLookup N' r with
      | none => simp [net_transb, hNr, hNr'] at h
      | some stq' => simp [net_transb, hNr, hNr'] at h
    | some stq =>
      cases hNr' : networkLookup N' r with
      | none => simp [net_transb, hNr, hNr'] at h
      | some stq' =>
        have h' : sq_transb n stq (sq_action.send p lab S) stq' = true ∧
            N' = N.replace r stq' := by
          simpa [net_transb, hNr, hNr'] using h
        have g : sq_transb m stq (sq_action.send p lab S) stq' = true ∧
            N' = N.replace r stq' :=
          ⟨sq_transb_mono hle h'.1, h'.2⟩
        simpa [net_transb, hNr, hNr'] using g
  | io_recv r p lab S =>
    cases hNr : networkLookup N r with
    | none =>
      cases hNr' : networkLookup N' r with
      | none => simp [net_transb, hNr, hNr'] at h
      | some stq' => simp [net_transb, hNr, hNr'] at h
    | some stq =>
      cases hNr' : networkLookup N' r with
      | none => simp [net_transb, hNr, hNr'] at h
      | some stq' =>
        have h' : sq_transb n stq (sq_action.recv p lab S) stq' = true ∧
            N' = N.replace r stq' := by
          simpa [net_transb, hNr, hNr'] using h
        have g : sq_transb m stq (sq_action.recv p lab S) stq' = true ∧
            N' = N.replace r stq' :=
          ⟨sq_transb_mono hle h'.1, h'.2⟩
        simpa [net_transb, hNr, hNr'] using g
  | τ_dequeue r p lab S =>
    cases hNr : networkLookup N r with
    | none =>
      cases hNr' : networkLookup N' r with
      | none => simp [net_transb, hNr, hNr'] at h
      | some stq' => simp [net_transb, hNr, hNr'] at h
    | some stq =>
      cases hNr' : networkLookup N' r with
      | none => simp [net_transb, hNr, hNr'] at h
      | some stq' =>
        have h' : sq_transb n stq (sq_action.dequeue p lab S) stq' = true ∧
            N' = N.replace r stq' := by
          simpa [net_transb, hNr, hNr'] using h
        have g : sq_transb m stq (sq_action.dequeue p lab S) stq' = true ∧
            N' = N.replace r stq' :=
          ⟨sq_transb_mono hle h'.1, h'.2⟩
        simpa [net_transb, hNr, hNr'] using g
  | τ_comm p q lab S =>
    cases hNp : networkLookup N p with
    | none =>
      cases hNq : networkLookup N q with
      | none =>
        cases hNp' : networkLookup N' p with
        | none =>
          cases hNq' : networkLookup N' q with
          | none => simp [net_transb, hNp, hNq, hNp', hNq'] at h
          | some _ => simp [net_transb, hNp, hNq, hNp', hNq'] at h
        | some _ =>
          cases hNq' : networkLookup N' q with
          | none => simp [net_transb, hNp, hNq, hNp', hNq'] at h
          | some _ => simp [net_transb, hNp, hNq, hNp', hNq'] at h
      | some _ =>
        cases hNp' : networkLookup N' p with
        | none =>
          cases hNq' : networkLookup N' q with
          | none => simp [net_transb, hNp, hNq, hNp', hNq'] at h
          | some _ => simp [net_transb, hNp, hNq, hNp', hNq'] at h
        | some _ =>
          cases hNq' : networkLookup N' q with
          | none => simp [net_transb, hNp, hNq, hNp', hNq'] at h
          | some _ => simp [net_transb, hNp, hNq, hNp', hNq'] at h
    | some stqp =>
      cases hNq : networkLookup N q with
      | none =>
        cases hNp' : networkLookup N' p with
        | none =>
          cases hNq' : networkLookup N' q with
          | none => simp [net_transb, hNp, hNq, hNp', hNq'] at h
          | some _ => simp [net_transb, hNp, hNq, hNp', hNq'] at h
        | some _ =>
          cases hNq' : networkLookup N' q with
          | none => simp [net_transb, hNp, hNq, hNp', hNq'] at h
          | some _ => simp [net_transb, hNp, hNq, hNp', hNq'] at h
      | some stqq =>
        cases hNp' : networkLookup N' p with
        | none =>
          cases hNq' : networkLookup N' q with
          | none => simp [net_transb, hNp, hNq, hNp', hNq'] at h
          | some _ => simp [net_transb, hNp, hNq, hNp', hNq'] at h
        | some stqp' =>
          cases hNq' : networkLookup N' q with
          | none => simp [net_transb, hNp, hNq, hNp', hNq'] at h
          | some stqq' =>
            have h' : ((sq_transb n stqp (sq_action.send q lab S) stqp' = true ∧
                sq_transb n stqq (sq_action.recv p lab S) stqq' = true) ∧
                p ≠ q) ∧ N' = (N.replace p stqp').replace q stqq' := by
              simpa [net_transb, hNp, hNq, hNp', hNq'] using h
            have g : ((sq_transb m stqp (sq_action.send q lab S) stqp' = true ∧
                sq_transb m stqq (sq_action.recv p lab S) stqq' = true) ∧
                p ≠ q) ∧ N' = (N.replace p stqp').replace q stqq' :=
              ⟨⟨⟨sq_transb_mono hle h'.1.1.1, sq_transb_mono hle h'.1.1.2⟩,
                h'.1.2⟩, h'.2⟩
            simpa [net_transb, hNp, hNq, hNp', hNq'] using g

-- ================================================================
-- Network-level completeness for `net_transb`.
-- ================================================================

-- Every network step is found by the executable checker at some finite
-- fuel (under role uniqueness of the source network, which holds for
-- every well-formed network). Together with the `*_sound` theorems this
-- makes `net_transb fuel N δ N' = true` (closed by `decide`) equivalent
-- to `net_trans N δ N'` for generated enumeration proofs.

/-- Every network step is certified by the executable checker at some fuel. -/
theorem net_transb_complete {N N' : Network} {δ : net_label}
    (hnd : (N.map Prod.fst).Nodup) (h : net_trans N δ N') :
    ∃ fuel, net_transb fuel N δ N' = true := by
  cases h with
  | @io_send r p stq stq' lab S hSQ hmem =>
    obtain ⟨n, hn⟩ := sq_transb_complete hSQ
    refine ⟨n, ?_⟩
    have hN : networkLookup N r = some stq := networkLookup_some_of_mem hnd hmem
    have hN' : networkLookup (N.replace r stq') r = some stq' :=
      networkLookup_replace stq'
    simp only [net_transb, hN, hN']
    simp [hn]
  | @io_recv r p stq stq' lab S hSQ hmem =>
    obtain ⟨n, hn⟩ := sq_transb_complete hSQ
    refine ⟨n, ?_⟩
    have hN : networkLookup N r = some stq := networkLookup_some_of_mem hnd hmem
    have hN' : networkLookup (N.replace r stq') r = some stq' :=
      networkLookup_replace stq'
    simp only [net_transb, hN, hN']
    simp [hn]
  | @dequeue r p stq stq' lab S hSQ hmem =>
    obtain ⟨n, hn⟩ := sq_transb_complete hSQ
    refine ⟨n, ?_⟩
    have hN : networkLookup N r = some stq := networkLookup_some_of_mem hnd hmem
    have hN' : networkLookup (N.replace r stq') r = some stq' :=
      networkLookup_replace stq'
    simp only [net_transb, hN, hN']
    simp [hn]
  | @comm p q lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    obtain ⟨n1, hn1⟩ := sq_transb_complete h_send
    obtain ⟨n2, hn2⟩ := sq_transb_complete h_recv
    refine ⟨n1 + n2, ?_⟩
    have hNp : networkLookup N p = some stqp := networkLookup_some_of_mem hnd hmem_p
    have hNq : networkLookup N q = some stqq := networkLookup_some_of_mem hnd hmem_q
    have hNp' : networkLookup ((N.replace p stqp').replace q stqq') p = some stqp' :=
      networkLookup_double_replace_left hne
    have hNq' : networkLookup ((N.replace p stqp').replace q stqq') q = some stqq' :=
      networkLookup_double_replace_right
    have hs1 : sq_transb (n1 + n2) stqp (sq_action.send q lab S) stqp' = true :=
      sq_transb_mono (Nat.le_add_right _ _) hn1
    have hs2 : sq_transb (n1 + n2) stqq (sq_action.recv p lab S) stqq' = true :=
      sq_transb_mono (Nat.le_add_left _ _) hn2
    simp only [net_transb, hNp, hNq, hNp', hNq']
    simp [hs1, hs2, hne]

-- ================================================================
-- `tRec` unfolding characterizations (for recursive example types).
-- ================================================================

-- The Vpn example's recursive types (`ARec`, `BTRec`, `QRec`, …) need
-- step characterizations that unfold one `tRec` layer before applying
-- the choice-head lemmas. These iff-characterizations package that
-- unfolding so generated `*_out_iff` / `*_no_inp` lemmas stay small.

/-- A recursive type steps exactly when its one-step unfolding steps. -/
theorem st_trans_tRec_iff {X : String} {B : SessionType} {α : st_label}
    {T' : SessionType} :
    st_trans (SessionType.tRec X B) α T' ↔
      st_trans (substSessionType B X (SessionType.tRec X B)) α T' := by
  constructor
  · intro h
    cases h with
    | tRec h' => exact h'
  · exact st_trans.tRec

/-- A send from a recursive session type unfolds one `tRec` layer. -/
theorem sq_trans_send_tRec_iff {X : String} {B : SessionType} {Q : Queue}
    {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} {Q' : Queue} :
    sq_trans (SessionType.tRec X B, Q) (sq_action.send p lab S) (T', Q') ↔
      (st_trans (substSessionType B X (SessionType.tRec X B))
          (st_label.out p lab S) T' ∧ Q' = Q) := by
  constructor
  · intro h
    cases h with
    | send hST =>
      cases hST with
      | tRec h' => exact ⟨h', rfl⟩
  · rintro ⟨h', rfl⟩
    exact sq_trans.send (st_trans.tRec h')

/-- A dequeue from a recursive session type unfolds one `tRec` layer. -/
theorem sq_trans_dequeue_tRec_iff {X : String} {B : SessionType} {Q Q' : Queue}
    {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    sq_trans (SessionType.tRec X B, Q) (sq_action.dequeue p lab S) (T', Q') ↔
      (st_trans (substSessionType B X (SessionType.tRec X B))
          (st_label.inp p lab S) T' ∧
        Q.dequeue (QueueMessage.msg p lab S) = some Q') := by
  constructor
  · intro h
    cases h with
    | dequeue hST hQ =>
      cases hST with
      | tRec h' => exact ⟨h', hQ⟩
  · rintro ⟨h', hQ⟩
    exact sq_trans.dequeue (st_trans.tRec h') hQ

-- ================================================================
-- Canonical-cover induction (for large enumerations like Store).
-- ================================================================

-- Store's ordered enumeration (1901 states) exceeds the feasible forcing
-- threshold for a flat disjunction, but its canonical quotient has only
-- 122 states. The induction below proves a canonical cover (`∃ C ∈ Cs`
-- with `N' ~ C`) by induction over `τ*`-steps starting from an arbitrary
-- `N1`: each ordered step is transported to its canonical representative
-- (`net_trans_reordered`) and re-covered by the per-canonical-state step
-- table (`hstep`, 122 cases instead of 1901). Half-duplex and stuck-state
-- no-orphan conclusions then transfer along the cover.

/-- Variable-start canonical-cover induction over `τ*`-reachability. -/
theorem canon_cover_star_aux {Cs : List Network}
    (hstep : ∀ C ∈ Cs, ∀ (δ : net_label) (N' : Network),
      net_trans C δ N' → is_internal_net_label δ →
      ∃ C' ∈ Cs, Network.Reordered N' C') :
    ∀ (N1 N2 : Network), net_trans_star N1 N2 →
      (∃ C ∈ Cs, Network.Reordered N1 C) →
      ∃ C' ∈ Cs, Network.Reordered N2 C' := by
  intro N1 N2 hStar
  induction hStar with
  | refl => intro h; exact h
  | step hInt hTr _ ih =>
    intro hN1
    obtain ⟨C, hCmem, hperm⟩ := hN1
    obtain ⟨M', hTr', hperm2⟩ := net_trans_reordered hperm hTr
    obtain ⟨C', hC'mem, hperm3⟩ := hstep C hCmem _ _ hTr' hInt
    exact ih ⟨C', hC'mem, Network.Reordered_trans hperm2 hperm3⟩

/-- Canonical cover of all states reachable from `Net`. -/
theorem canon_cover_of_star {Net : Network} {Cs : List Network}
    (hbase : ∃ C ∈ Cs, Network.Reordered Net C)
    (hstep : ∀ C ∈ Cs, ∀ (δ : net_label) (N' : Network),
      net_trans C δ N' → is_internal_net_label δ →
      ∃ C' ∈ Cs, Network.Reordered N' C')
    (N' : Network) (hStar : net_trans_star Net N') :
    ∃ C ∈ Cs, Network.Reordered N' C :=
  canon_cover_star_aux hstep Net N' hStar hbase

/-- Every prefix of an infinite path is canonically covered. -/
theorem path_canon_cover {π : InfiniteNetworkPath} {Net : Network}
    {Cs : List Network}
    (hcover : ∀ N', net_trans_star Net N' → ∃ C ∈ Cs, Network.Reordered N' C)
    (h0 : π.seq 0 = Net) (i : ℕ) :
    ∃ C ∈ Cs, Network.Reordered (π.seq i) C :=
  hcover _ (path_star_reachable h0 i)

/-- Half-duplex from a canonical cover (one case per canonical state). -/
theorem IsHalfDuplex_of_canon_cover {Net : Network} {Cs : List Network}
    (hcover : ∀ N', net_trans_star Net N' → ∃ C ∈ Cs, Network.Reordered N' C)
    (hHD : ∀ C ∈ Cs, ∀ (p q : Role) (Qp Qq : Queue),
      NetworkHasQueue C p Qp → NetworkHasQueue C q Qq →
      QueueContainsFrom Qp q → ¬ QueueContainsFrom Qq p) :
    IsHalfDuplex Net := by
  intro N' hStar p q Qp Qq hP hQ hPq hCq
  obtain ⟨C, hCmem, hperm⟩ := hcover N' hStar
  exact hHD C hCmem p q Qp Qq
    ((Network.hasQueue_reordered hperm).mp hP)
    ((Network.hasQueue_reordered hperm).mp hQ) hPq hCq

/-- Stuck-state no-orphan closure from a canonical cover. -/
theorem noOrphan_of_canon_cover_stuck {Net : Network} {Cs : List Network}
    (hcover : ∀ N', net_trans_star Net N' → ∃ C ∈ Cs, Network.Reordered N' C)
    (hNO : ∀ C ∈ Cs, IsStuckNetwork C → NoOrphanMessages C)
    (N' : Network) (hStar : net_trans_star Net N') (hStuck : IsStuckNetwork N') :
    NoOrphanMessages N' := by
  obtain ⟨C, hCmem, hperm⟩ := hcover N' hStar
  have hStuckC : IsStuckNetwork C := (IsStuckNetwork_reordered hperm).mp hStuck
  exact (noOrphanMessages_reordered hperm).mpr (hNO C hCmem hStuckC)
