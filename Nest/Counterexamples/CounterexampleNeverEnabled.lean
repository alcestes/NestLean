import Nest.SessionUtils

/-!
# Counterexample: never-enabled persistence is false as stated.

Certified witness against both `stuck_encQueue_dequeue_never_enabled` and
`stuck_witness_dequeue_never_enabled` in `Nest.StuckWitness` (the two share
the same statement): with `Tq` offering the distinguished input on a branch
targeting `tEnd`, prefix queue `[m]`, and monitor `M = tEnd`, every hypothesis
holds (`hEnc` by base-`extC`, `hNo` since `tEnd` is dead), yet the distinguished
dequeue fires immediately at `Ni` (double-copy queue `[m, m]`).

Nothing here depends on the old rigid definitions: only base-`extC`,
`st_trans`, and queue-scan computation, all valid under maximal semantics.

This file is evidence only (not imported by `Nest.lean`); it imports only
`Nest.SessionUtils`, never `BadStuff`/`Proofs`/`StuckWitness`/`NewStuckWitness`.
-/

/-- The distinguished message (sender `"p"`). -/
private def CxNE_m : QueueMessage := QueueMessage.msg "p" "l" "s"

/-- Session type offering exactly the distinguished input, into `tEnd`. -/
private def CxNE_Tq : SessionType :=
  SessionType.externalChoice "p" [("l", "s", SessionType.tEnd)]

/-- Witness network: `q` holds two copies, `p` idles (present for sender-closure). -/
private def CxNE_Ni : Network :=
  [("q", (CxNE_Tq, [CxNE_m, CxNE_m])), ("p", (SessionType.tEnd, []))]

private lemma CxNE_TqWF : CxNE_Tq.WellFormed := by
  refine ⟨?_, rfl, ?_⟩
  · show SessionType.NoDupl
      (SessionType.externalChoice "p" [("l", "s", SessionType.tEnd)])
    apply SessionType.NoDupl.externalChoice
    · decide
    · simp
    · intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact SessionType.NoDupl.end
  · show SessionType.Contractive
      (SessionType.externalChoice "p" [("l", "s", SessionType.tEnd)])
    apply SessionType.Contractive.externalChoice
    intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact SessionType.Contractive.end

private lemma CxNE_tEndWF : SessionType.tEnd.WellFormed :=
  ⟨SessionType.NoDupl.end, rfl, SessionType.Contractive.end⟩

/-- The queue fold reaches `tEnd` by base-`extC` on the prefix copy. -/
private lemma CxNE_hEnc : monitor_fold (CxNE_Tq, [CxNE_m]) SessionType.tEnd := by
  refine ⟨SessionType.tEnd, ?_, rfl⟩
  have hb : mon_tr_yes_base CxNE_Tq (ext_tag.recv "p" "l" "s") SessionType.tEnd := by
    unfold CxNE_Tq
    apply mon_tr_yes_base.extC
    · decide
    · simp
  exact ⟨mon_tr_yes_exist.base hb, @mon_tr_yes_max_deriv.base _ _ _ hb⟩

/-- `tEnd` admits no maximal yes-transition (all `Exist` rules conclude
    choices/`tRec`). -/
private lemma CxNE_hNo : ∀ M', ¬ mon_tr_yes SessionType.tEnd
    (ext_tag.recv "p" "l" "s") M' := by
  intro M' h
  rcases h with ⟨hE, _⟩
  cases hE with
  | base hb => cases hb

private lemma CxNE_hMem :
    ("q", (CxNE_Tq, [CxNE_m] ++ [CxNE_m])) ∈ CxNE_Ni := by
  unfold CxNE_Ni
  simp

/-- Other roles survive `Network.replace` (local copy; `Proofs` is downstream). -/
private lemma CxNE_mem_other {N : Network} {r0 : Role} {stq0 : SessionTypeWithQueue}
    {r : Role} {stq : SessionTypeWithQueue}
    (h : (r, stq) ∈ N) (hne : r ≠ r0) :
    (r, stq) ∈ Network.replace N r0 stq0 := by
  unfold Network.replace
  simp
  right
  exact ⟨h, hne⟩

/-- Membership in a replaced network is the new entry or an old one. -/
private lemma CxNE_mem_cases {N : Network} {a : Role} {s : SessionTypeWithQueue}
    {r : Role} {st : SessionTypeWithQueue} (h : (r, st) ∈ Network.replace N a s) :
    (r, st) = (a, s) ∨ (r, st) ∈ N := by
  unfold Network.replace at h
  rw [List.mem_cons, List.mem_filter] at h
  rcases h with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- `QueueMem` is list membership. -/
private lemma CxNE_qmem_mem {m : QueueMessage} {Q : Queue} (h : QueueMem m Q) : m ∈ Q := by
  induction h with
  | head => exact List.mem_cons_self ..
  | tail _ ih => exact List.mem_cons_of_mem _ ih

/-- No session type here can send. -/
private lemma CxNE_noOut {T : SessionType}
    (hT : T = CxNE_Tq ∨ T = SessionType.tEnd)
    {p' : Role} {lab' : Lab} {S' : DataSort} {T' : SessionType} :
    ¬ st_trans T (st_label.out p' lab' S') T' := by
  rcases hT with rfl | rfl
  · unfold CxNE_Tq
    intro hST
    cases hST
  · intro hST
    cases hST

/-- The scan for `m` in `[m, m]` drops exactly one copy. -/
private lemma CxNE_scan :
    Queue.dequeue [CxNE_m, CxNE_m] CxNE_m = some [CxNE_m] := by
  decide

/-- Invariant: `p` stays `(tEnd, [])`, `q` stays within its three shapes,
    and only `q`/`p` occur. -/
private def CxNE_inv (N : Network) : Prop :=
  (∀ T Q, ("p", (T, Q)) ∈ N → T = SessionType.tEnd ∧ Q = []) ∧
  (∀ T Q, ("q", (T, Q)) ∈ N →
    (T = CxNE_Tq ∧ Q = [CxNE_m, CxNE_m]) ∨
    (T = SessionType.tEnd ∧ Q = [CxNE_m]) ∨
    (T = SessionType.tEnd ∧ Q = [])) ∧
  (∀ r stq, (r, stq) ∈ N → r = "q" ∨ r = "p")

private lemma CxNE_inv_base : CxNE_inv CxNE_Ni := by
  refine ⟨?_, ?_, ?_⟩
  · intro T Q hmem
    unfold CxNE_Ni at hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with h | h | h
    · simp at h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · simp at h
  · intro T Q hmem
    unfold CxNE_Ni at hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with h | h | h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
    · simp at h
    · simp at h
  · intro r stq hmem
    unfold CxNE_Ni at hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with h | h | h
    · obtain rfl := congrArg Prod.fst h
      exact Or.inl rfl
    · obtain rfl := congrArg Prod.fst h
      exact Or.inr rfl
    · simp at h

/-- Single internal step preserves the invariant. -/
private lemma CxNE_step {N1 N2 : Network} {δ : net_label}
    (hTr : net_trans N1 δ N2) (hInt : is_internal_net_label δ)
    (hInv : CxNE_inv N1) : CxNE_inv N2 := by
  have hqp : ("q" : Role) ≠ "p" := by decide
  obtain ⟨hp1, hq1, hr1⟩ := hInv
  cases hTr with
  | io_send hSQ hmem0 =>
    simp [is_internal_net_label] at hInt
  | io_recv hSQ hmem0 =>
    simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem0 =>
    rename_i r p0 stq0 stq0' lab0 S0
    rcases hr1 r stq0 hmem0 with rfl | rfl
    · -- Dequeue at `q`: the entry shape determines the outcome.
      rcases stq0 with ⟨T0, Q0⟩
      rcases hq1 T0 Q0 hmem0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- `(Tq, [m, m])`: only the distinguished dequeue can fire.
        cases hSQ with
        | @dequeue _ T' _ Q' _ _ _ hST hQ =>
          unfold CxNE_Tq at hST
          cases hST with
          | extC hmemB =>
            rw [List.mem_singleton] at hmemB
            obtain ⟨rfl, rfl, rfl⟩ := hmemB
            have hQeq : Q' = [CxNE_m] :=
              Option.some.inj (hQ.symm.trans CxNE_scan)
            subst hQeq
            refine ⟨?_, ?_, ?_⟩
            · intro T Q hmem
              rcases CxNE_mem_cases hmem with h | h
              · have hEq : ("p" : Role) = "q" := congrArg Prod.fst h
                exact absurd hEq hqp.symm
              · exact hp1 T Q h
            · intro T Q hmem
              rcases CxNE_mem_cases hmem with h | h
              · obtain ⟨_, hTQ⟩ := Prod.mk.inj h
                obtain ⟨rfl, rfl⟩ := hTQ
                exact Or.inr (Or.inl ⟨rfl, rfl⟩)
              · exact hq1 T Q h
            · intro r2 stq2 hmem
              rcases CxNE_mem_cases hmem with h | h
              · obtain rfl := congrArg Prod.fst h
                exact Or.inl rfl
              · exact hr1 _ _ h
      · -- `(tEnd, [m])`: `tEnd` offers no input.
        cases hSQ with
        | dequeue hST hQ =>
          exact absurd hST (by intro h'; cases h')
      · -- `(tEnd, [])`: the scan finds nothing.
        cases hSQ with
        | dequeue hST hQ =>
          simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · -- Dequeue at `p`: `tEnd` offers no input.
      rcases stq0 with ⟨T0, Q0⟩
      rcases hp1 T0 Q0 hmem0 with ⟨rfl, rfl⟩
      cases hSQ with
      | dequeue hST hQ =>
        exact absurd hST (by intro h'; cases h')
  | comm _hne h_send h_recv hmem_p hmem_q =>
    rename_i p' q' lab' S' stqp stqp' stqq stqq'
    -- No role here can send, so no communication can fire.
    rcases hr1 p' stqp hmem_p with rfl | rfl
    · rcases stqp with ⟨T0, Q0⟩
      rcases hq1 T0 Q0 hmem_p with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · cases h_send with
        | send hST => exact absurd hST (CxNE_noOut (Or.inl rfl))
      · cases h_send with
        | send hST => exact absurd hST (CxNE_noOut (Or.inr rfl))
      · cases h_send with
        | send hST => exact absurd hST (CxNE_noOut (Or.inr rfl))
    · rcases stqp with ⟨T0, Q0⟩
      rcases hp1 T0 Q0 hmem_p with ⟨rfl, _⟩
      cases h_send with
      | send hST => exact absurd hST (CxNE_noOut (Or.inr rfl))

/-- The invariant holds on every `τ*`-successor. -/
private lemma CxNE_inv_star_aux {N0 N' : Network} (hS : net_trans_star N0 N')
    (hBase : CxNE_inv N0) : CxNE_inv N' := by
  induction hS with
  | refl => exact hBase
  | step hInt hTr hS' ih => exact ih (CxNE_step hTr hInt hBase)

private lemma CxNE_inv_star {N' : Network} (hS : net_trans_star CxNE_Ni N') :
    CxNE_inv N' :=
  CxNE_inv_star_aux hS CxNE_inv_base

/-- Well-formedness of the witness network (sender-closure: `p` is present). -/
private lemma CxNE_hNiWF : CxNE_Ni.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · show List.Nodup (List.map Prod.fst
      ([("q", (CxNE_Tq, [CxNE_m, CxNE_m])), ("p", (SessionType.tEnd, []))] :
        Network))
    decide
  · intro x hx
    unfold CxNE_Ni at hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · show SessionType.WellFormed CxNE_Tq
      exact CxNE_TqWF
    · show SessionType.WellFormed SessionType.tEnd
      exact CxNE_tEndWF
    · simp at hx
  · intro q T Q p lab S hmem hqmem
    unfold CxNE_Ni at hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | hmem
    · simp only [List.mem_cons] at hqmem
      rcases hqmem with hEq | hEq | hEq
      · unfold CxNE_m at hEq
        cases hEq
        exact ⟨(SessionType.tEnd, []), by simp [CxNE_Ni]⟩
      · unfold CxNE_m at hEq
        cases hEq
        exact ⟨(SessionType.tEnd, []), by simp [CxNE_Ni]⟩
      · simp at hEq
    · simp at hqmem
    · simp at hmem

/-- Every message in a `q`-entry's queue is `m` (from the three shapes). -/
private lemma CxNE_qallm {N' : Network}
    (hqI : ∀ T Q, ("q", (T, Q)) ∈ N' →
      (T = CxNE_Tq ∧ Q = [CxNE_m, CxNE_m]) ∨
      (T = SessionType.tEnd ∧ Q = [CxNE_m]) ∨
      (T = SessionType.tEnd ∧ Q = []))
    {T Q} (hmem : ("q", (T, Q)) ∈ N') : ∀ x ∈ Q, x = CxNE_m := by
  rcases hqI T Q hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx2
    · rfl
    · rfl
    · simp at hx2
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx2
    · rfl
    · simp at hx2
  · intro x hx
    simp at hx

/-- Half-duplexity: `p`'s queue stays empty and `q`'s queue holds only `m`. -/
private lemma CxNE_hHD : IsHalfDuplex CxNE_Ni := by
  intro N' hS a b Qa Qb ha hb hCa hCb
  obtain ⟨hpI, hqI, hrI⟩ := CxNE_inv_star hS
  obtain ⟨Ta, hmemA⟩ := ha
  obtain ⟨Tb, hmemB⟩ := hb
  rcases hrI a (Ta, Qa) hmemA with rfl | rfl <;>
    rcases hrI b (Tb, Qb) hmemB with rfl | rfl
  · -- (`q`, `q`): `q`'s queue holds no `"q"`-message.
    have hallQb := CxNE_qallm hqI hmemB
    obtain ⟨lab0, S0, hmem0⟩ := hCb
    have hEq := hallQb _ (CxNE_qmem_mem hmem0)
    have hqp : ("q" : Role) = "p" := by
      have h2 := congrArg (fun m : QueueMessage => m.1) hEq
      simp [CxNE_m] at h2
    exact absurd hqp (by decide)
  · -- (`q`, `p`): `p`'s queue is empty.
    obtain ⟨rfl, rfl⟩ := hpI Tb Qb hmemB
    obtain ⟨lab0, S0, hmem0⟩ := hCb
    cases hmem0
  · -- (`p`, `_`): `p`'s queue is empty, so the premise is impossible.
    obtain ⟨rfl, rfl⟩ := hpI Ta Qa hmemA
    obtain ⟨lab0, S0, hmem0⟩ := hCa
    cases hmem0
  · obtain ⟨rfl, rfl⟩ := hpI Ta Qa hmemA
    obtain ⟨lab0, S0, hmem0⟩ := hCa
    cases hmem0

/-- The distinguished dequeue fires immediately at `Ni`. -/
private lemma CxNE_fire : ∃ N' N'' : Network,
    net_trans_star CxNE_Ni N' ∧
      net_trans N' (net_label.τ_dequeue "q" "p" "l" "s") N'' := by
  have hST : st_trans CxNE_Tq (st_label.inp "p" "l" "s") SessionType.tEnd := by
    unfold CxNE_Tq
    apply st_trans.extC
    simp
  have hQ : Queue.dequeue [CxNE_m, CxNE_m] CxNE_m = some [CxNE_m] := CxNE_scan
  have hmem : ("q", (CxNE_Tq, [CxNE_m, CxNE_m])) ∈ CxNE_Ni := by
    unfold CxNE_Ni
    simp
  have hT : net_trans CxNE_Ni (net_label.τ_dequeue "q" "p" "l" "s")
      (Network.replace CxNE_Ni "q" (SessionType.tEnd, [CxNE_m])) :=
    net_trans.dequeue (sq_trans.dequeue hST hQ) hmem
  exact ⟨CxNE_Ni, _, net_trans_star.refl _, hT⟩

/-- Certified refutation of the never-enabled conclusion at this instance. -/
theorem CxNE_refutes_never_enabled :
    (∀ N' N'' : Network, net_trans_star CxNE_Ni N' →
      ¬ net_trans N' (net_label.τ_dequeue "q" "p" "l" "s") N'') → False := by
  intro hCon
  obtain ⟨N', N'', hS, hT⟩ := CxNE_fire
  exact hCon N' N'' hS hT
