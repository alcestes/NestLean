import Nest.SessionUtils
import Nest.NoRec.NoRecUtils

/-!
# NoRecToolkit: NoRec network toolkit: recursion-free preservation, termination, and non-liveness.

Network.NoRec, step/network preservation, size-shrink, budgets, stuck-reachability,
and output-liveness stability under NoRec. Import base for the whole `Nest.NoRec` tree.
-/

/-!
# NoRec network toolkit.

Recursion-free (`NoRec`) preservation, termination, and non-liveness:
all of these assume `NoRec` hypotheses and are used only inside `Nest.NoRec`
(none are referenced outside it). `path_star_reachable_of`,
`stuckStep_of_notStuck`, `closed_of_trec_closed_vacuous`,
`filter_ne_self`, and `Network.role_preserved_replace` are general
single-use helpers duplicated here since `private` declarations cannot
cross modules.
-/


-- ================================================================
-- Recursion-free networks (`NoRec`)
-- ================================================================

/-- A network is recursion-free (`NoRec`) when every entry's session type
    contains no `tRec`. Stepping stone for the NoRec soundness chain
    (`Nest.NoRec`): steps go to subterms, determinism holds, and
    maximality rebuilds by size induction. -/
def Network.NoRec (N : Network) : Prop :=
  ∀ (x : Role × SessionTypeWithQueue), x ∈ N → x.2.1.NoRec


/-- `st_trans` steps preserve `NoRec` (`cases`-only: branch targets are
    subterms; `tRec` pruned by `NoRec`). -/
lemma st_trans_preserves_norec' {T T' : SessionType} {α : st_label}
    (hST : st_trans T α T') (hNR : T.NoRec) : T'.NoRec := by
  cases hST with
  | intC hmem => exact noRec_of_mem_intBranches hNR hmem
  | extC hmem => exact noRec_of_mem_extBranches hNR hmem
  | tRec h => cases hNR


/-- `sq_trans` steps preserve `NoRec` of the session component. -/
lemma sq_trans_preserves_norec {stq stq' : SessionTypeWithQueue} {a : sq_action}
    (h : sq_trans stq a stq') (hNR : stq.1.NoRec) : stq'.1.NoRec := by
  cases h with
  | send hST => exact st_trans_preserves_norec' hST hNR
  | dequeue hST hQ => exact st_trans_preserves_norec' hST hNR
  | recv => exact hNR


/-- Membership transport through `Network.replace`: replaced entries keep
    the new fact, others keep facts from `N`. -/
lemma no_rec_replace {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    (hNR : N.NoRec) (hNew : stq.1.NoRec) : (Network.replace N r stq).NoRec := by
  intro x hx
  unfold Network.replace at hx
  simp only [List.mem_cons, List.mem_filter] at hx
  rcases hx with rfl | ⟨hxN, -⟩
  · exact hNew
  · exact hNR x hxN


/-- `net_trans` steps preserve `NoRec`-networks (per-arm session preservation +
    replace transport; receiver sessions are unchanged). -/
lemma net_trans_preserves_norec {N N' : Network} {δ : net_label}
    (hTr : net_trans N δ N') (hNR : N.NoRec) : N'.NoRec := by
  cases hTr with
  | io_send hSQ hmem =>
    exact no_rec_replace hNR (sq_trans_preserves_norec hSQ (hNR _ hmem))
  | io_recv hSQ hmem =>
    exact no_rec_replace hNR (sq_trans_preserves_norec hSQ (hNR _ hmem))
  | dequeue hSQ hmem =>
    exact no_rec_replace hNR (sq_trans_preserves_norec hSQ (hNR _ hmem))
  | comm _hne h_send h_recv hmem_p hmem_q =>
    cases h_recv with
    | recv =>
      exact no_rec_replace (no_rec_replace hNR
        (sq_trans_preserves_norec h_send (hNR _ hmem_p))) (hNR _ hmem_q)


/-- `NoRec`-networks persist along τ-stars. -/
lemma net_trans_star_preserves_norec {N N' : Network}
    (hStar : net_trans_star N N') (hNR : N.NoRec) : N'.NoRec := by
  revert hNR
  induction hStar with
  | refl =>
    intro hNR
    exact hNR
  | step hInt hTr _ ih =>
    intro hNR
    exact ih (net_trans_preserves_norec hTr hNR)


/-- `st_trans` targets are strictly smaller under `NoRec`. -/
lemma st_trans_size_lt_of_norec {T T' : SessionType} {α : st_label}
    (hST : st_trans T α T') (hNR : T.NoRec) : sizeOf T' < sizeOf T := by
  cases hST with
  | intC hmem => exact sizeOf_SessionType_lt_sizeOf_internalChoice hmem
  | extC hmem => exact sizeOf_SessionType_lt_sizeOf_externalChoice hmem
  | tRec h => cases hNR


/-- Filtering out absent roles preserves the budget (no entry removed). -/
private lemma filter_sum_eq_of_no_role (l : List (Role × SessionTypeWithQueue)) (r : Role)
    (h : ∀ x ∈ l, x.1 ≠ r) :
    (((l.filter fun x => x.1 != r).map fun x : Role × SessionTypeWithQueue => sizeOf x.2.1).sum) =
    ((l.map fun x => sizeOf x.2.1).sum) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hpos : ((fun x : Role × SessionTypeWithQueue => x.1 != r) hd) :=
      bne_iff_ne.mpr (h hd (List.mem_cons.mpr (Or.inl rfl)))
    have htl : ∀ x ∈ tl, x.1 ≠ r :=
      fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
    rw [List.filter_cons_of_pos (p := fun x : Role × SessionTypeWithQueue => x.1 != r)
      (a := hd) hpos, List.map_cons, List.map_cons,
      List.sum_cons, List.sum_cons, ih htl]

/-- Replace-bookkeeping as an equation: the new budget plus the old entry
    size equals the old budget plus the new entry size. -/
lemma budget_replace_eq (l : List (Role × SessionTypeWithQueue)) (r : Role)
    (stq stq' : SessionTypeWithQueue)
    (hmem : (r, stq) ∈ l)
    (hnd : (l.map fun x : Role × SessionTypeWithQueue => x.1).Nodup) :
    ((((r, stq') :: l.filter fun x => x.1 != r).map
      fun x : Role × SessionTypeWithQueue => sizeOf x.2.1).sum) + sizeOf stq.1 =
    ((l.map fun x => sizeOf x.2.1).sum) + sizeOf stq'.1 := by
  revert hmem hnd
  induction l with
  | nil =>
    intro hmem hnd
    simp at hmem
  | cons hd tl ih =>
    intro hmem hnd
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotin, htlnd⟩ := hnd
    by_cases heq : hd.1 = r
    · -- `hd` is the replaced entry: the filter drops exactly it.
      have hhd : hd = (r, stq) := by
        rcases List.mem_cons.mp hmem with heq2 | hmemT
        · exact heq2.symm
        · exfalso
          rw [heq] at hnotin
          exact hnotin (List.mem_map.mpr ⟨(r, stq), hmemT, rfl⟩)
      subst hhd
      have hno : ∀ x ∈ tl, x.1 ≠ r := by
        intro x hx heq2
        exact hnotin (List.mem_map.mpr ⟨x, hx, heq2⟩)
      have hfsum := filter_sum_eq_of_no_role tl r hno
      rw [List.filter_cons_of_neg (p := fun x : Role × SessionTypeWithQueue => x.1 != r)
        (a := (r, stq)) (fun h => (bne_iff_ne.mp h) rfl)]
      simp only [List.map_cons, List.sum_cons]
      rw [hfsum]
      show (sizeOf stq'.1 + _) + sizeOf stq.1 = (sizeOf stq.1 + _) + sizeOf stq'.1
      omega
    · -- `hd` kept: recurse on the tail.
      have hmemT : (r, stq) ∈ tl := by
        rcases List.mem_cons.mp hmem with heq2 | hT
        · exfalso
          have hrh : hd.1 = r := by rw [← heq2]
          exact heq hrh
        · exact hT
      rw [List.filter_cons_of_pos (p := fun x : Role × SessionTypeWithQueue => x.1 != r)
        (a := hd) (bne_iff_ne.mpr heq)]
      simp only [List.map_cons, List.sum_cons]
      have ih' := ih hmemT htlnd
      simp only [List.map_cons, List.sum_cons] at ih'
      omega

/-- Mapped filter is a sublist of the mapped list. -/
private lemma map_filter_sublist (l : List (Role × SessionTypeWithQueue))
    (p : (Role × SessionTypeWithQueue) → Bool) (f : (Role × SessionTypeWithQueue) → Role) :
    List.Sublist ((l.filter p).map f) (l.map f) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons hd tl ih =>
    by_cases h : p hd = true
    · rw [List.filter_cons_of_pos (a := hd) (by rw [h])]
      simp only [List.map_cons]
      exact List.Sublist.cons_cons _ ih
    · rw [List.filter_cons_of_neg (a := hd) h]
      exact List.Sublist.cons _ ih

/-- Role-nodup survives `Network.replace`. -/
lemma nodup_replace_roles {N : Network} {r : Role} {stq : SessionTypeWithQueue}
    (hnd : (N.map fun x : Role × SessionTypeWithQueue => x.1).Nodup) :
    (((Network.replace N r stq).map fun x : Role × SessionTypeWithQueue => x.1)).Nodup := by
  unfold Network.replace
  simp only [List.map_cons]
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hmem
    obtain ⟨x, hx, hxx⟩ := List.mem_map.mp hmem
    have hpred : ((fun x : Role × SessionTypeWithQueue => x.1 != r) x) :=
      (List.mem_filter.mp hx).2
    exact (bne_iff_ne.mp hpred) hxx
  · exact hnd.sublist (map_filter_sublist _ _ _)

/-- Every internal step strictly decreases the budget (`NoRec` + WF +
    `p ≠ q`: some role's session moves to a strict subterm; receiver
    sessions are unchanged and distinct roles never overwrite). -/
lemma budget_step_norec {N N' : Network} {δ : net_label}
    (hTr : net_trans N δ N') (hInt : is_internal_net_label δ)
    (hNR : N.NoRec) (hWF : N.WellFormed) :
    networkBudget N' < networkBudget N := by
  cases hTr with
  | io_send _ _ => simp [is_internal_net_label] at hInt
  | io_recv _ _ => simp [is_internal_net_label] at hInt
  | @dequeue r p stq stq' lab S hSQ hmem =>
    obtain ⟨T, Q⟩ := stq
    obtain ⟨T', Q'⟩ := stq'
    cases hSQ with
    | dequeue hST hQ =>
      have hTNR := hNR _ hmem
      have hlt : sizeOf T' < sizeOf T := st_trans_size_lt_of_norec hST hTNR
      have heq : networkBudget (Network.replace N r (T', Q')) + sizeOf T =
          networkBudget N + sizeOf T' :=
        budget_replace_eq N r (T, Q) (T', Q') hmem hWF.1
      unfold networkBudget at heq ⊢
      omega
  | @comm p q lab S stqp stqp' stqq stqq' hne h_send h_recv hmem_p hmem_q =>
    obtain ⟨Tp, Qp⟩ := stqp
    obtain ⟨Tp', Qp'⟩ := stqp'
    obtain ⟨Tq, Qq⟩ := stqq
    cases h_send with
    | send hST =>
      cases h_recv with
      | recv =>
        have hTNR := hNR _ hmem_p
        have hltS : sizeOf Tp' < sizeOf Tp := st_trans_size_lt_of_norec hST hTNR
        have heq1 : networkBudget (Network.replace N p (Tp', Qp)) + sizeOf Tp =
            networkBudget N + sizeOf Tp' :=
          budget_replace_eq N p (Tp, Qp) (Tp', Qp) hmem_p hWF.1
        have hmem_q' : (q, (Tq, Qq)) ∈ Network.replace N p (Tp', Qp) :=
          mem_replace_other hmem_q (Ne.symm hne)
        have heq2 : networkBudget (Network.replace (Network.replace N p (Tp', Qp))
              q (Tq, Qq ++ [QueueMessage.msg p lab S])) + sizeOf Tq =
            networkBudget (Network.replace N p (Tp', Qp)) + sizeOf Tq :=
          budget_replace_eq _ q (Tq, Qq) (Tq, Qq ++ [QueueMessage.msg p lab S])
            hmem_q' (nodup_replace_roles hWF.1)
        unfold networkBudget at heq1 heq2 ⊢
        omega


/-- Every overapprox step moves the session to a strict subterm (under
    `NoRec`), so the session-size measure decreases along any reduction. -/
lemma over_trans_session_shrink_norec {stq stq' : SessionTypeWithQueue} {α : st_label}
    (h : over_trans stq α stq') (hNR : stq.1.NoRec) : sizeOf stq'.1 < sizeOf stq.1 := by
  cases h with
  | dequeue hEq hmem hQ =>
    rw [hEq]
    exact sizeOf_SessionType_lt_sizeOf_externalChoice hmem
  | specInp hEq hmem hAbs =>
    rw [hEq]
    exact sizeOf_SessionType_lt_sizeOf_externalChoice hmem
  | sendFresh hEq hST hFresh =>
    subst hEq
    exact st_trans_size_lt_of_norec hST hNR
  | tauUnfold hU =>
    cases hU with
    | tRec => cases hNR


/-- Reachability along an infinite path (each prefix is a τ-star). -/
lemma path_star_reachable_of (π : InfiniteNetworkPath) (Ni : Network)
    (h0 : π.seq 0 = Ni) (i : ℕ) : net_trans_star Ni (π.seq i) := by
  induction i with
  | zero =>
    rw [h0]
    exact net_trans_star.refl _
  | succ k ih =>
    have hTr := π.δ_tr k
    obtain ⟨r, p, lab, S, h | h⟩ := π.δ_form k
    · rw [h] at hTr
      exact net_trans_star.trans ih (net_trans_star.step (by trivial) hTr (net_trans_star.refl _))
    · rw [h] at hTr
      exact net_trans_star.trans ih (net_trans_star.step (by trivial) hTr (net_trans_star.refl _))



/-- A non-stuck network has an outgoing internal step (classical). -/
lemma stuckStep_of_notStuck {N : Network} (h : ¬ IsStuckNetwork N) :
    ∃ δ N', is_internal_net_label δ ∧ net_trans N δ N' := by
  unfold IsStuckNetwork at h
  exact Classical.byContradiction h



/-- Single-step role preservation: every role of `N` still occurs in any `net_trans`
    successor; in particular, every role occurs in `Network.replace N r stq`
    (with new data at `r`). -/
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

private lemma net_trans_role_preserved_single {N N' : Network} {δ : net_label}
    (h : net_trans N δ N') (r : Role) (stq : SessionTypeWithQueue) (hmem : (r, stq) ∈ N) :
    ∃ stq', (r, stq') ∈ N' := by
  cases h with
  | io_send _ _ =>
    exact Network.role_preserved_replace hmem
  | io_recv _ _ =>
    exact Network.role_preserved_replace hmem
  | dequeue _ _ =>
    exact Network.role_preserved_replace hmem
  | comm _ _ _ _ _ =>
    obtain ⟨mid, hmid⟩ := Network.role_preserved_replace hmem
    exact Network.role_preserved_replace hmid


/-- Role preservation along `τ*`: every role of `N` still occurs in any reachable `N'`. -/
lemma net_trans_role_preserved {N N' : Network} (hStar : net_trans_star N N')
    (r : Role) (stq : SessionTypeWithQueue) (hmem : (r, stq) ∈ N) :
    ∃ stq', (r, stq') ∈ N' := by
  revert r stq hmem
  induction hStar with
  | refl =>
    intro r stq hmem
    exact ⟨stq, hmem⟩
  | step hInt hTr hStar' ih =>
    intro r stq hmem
    obtain ⟨mid, hmid⟩ := net_trans_role_preserved_single hTr r stq hmem
    exact ih _ _ hmid


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


/-- A vacuous head binder preserves closedness into its body. -/
theorem closed_of_trec_closed_vacuous {Y : String} {B : SessionType}
    (hfree : Y ∉ B.fv) (hCl : (SessionType.tRec Y B).IsClosed) : B.IsClosed := by
  unfold SessionType.IsClosed at hCl ⊢
  simp only [SessionType.fv] at hCl
  rw [filter_ne_self hfree] at hCl
  exact hCl

/-- Well-formedness transfers to `tRec` bodies under vacuousness
    (closedness needs the binder absent; `NoDupl`/`Contractive`
    invert directly). Feeds size-IH applications at `tRec` bodies in
    vacuous inductions (e.g. the duality aux). -/
lemma SessionType.WellFormed.of_tRecBody {X : String} {B : SessionType}
    (hWF : (SessionType.tRec X B).WellFormed) (hfree : X ∉ B.fv) :
    B.WellFormed := by
  obtain ⟨hND, hCl, hCo⟩ := hWF
  refine ⟨?_, ?_, ?_⟩
  · cases hND with
    | tRec h => exact h
  · exact closed_of_trec_closed_vacuous hfree hCl
  · cases hCo with
    | tRec hC _ => exact hC

/-- Grafting a closed replacer is a no-op. -/
private theorem subst_closed_eq {R : SessionType} (Z : String) (U : SessionType)
    (hRCl : R.IsClosed) : substSessionType R Z U = R := by
  have hfv : R.fv = [] := hRCl
  have hmem : Z ∉ R.fv := by
    rw [hfv]
    simp
  exact subst_noop R Z U hmem

/-- Closed types are fixed by graft chains. -/
private theorem graftFold_fix_closed {R : SessionType} (hRCl : R.IsClosed)
    (G : List (String × SessionType)) : graftFold G R = R := by
  induction G with
  | nil => simp [graftFold]
  | cons hd tl ih =>
    rcases hd with ⟨Z, U⟩
    simp only [graftFold]
    rw [subst_closed_eq _ _ hRCl]
    exact ih

/-- Chained grafts hit the head binding first (later grafts never apply). -/
private theorem graftFold_endpoint {R : SessionType} (hRCl : R.IsClosed)
    (G : List (String × SessionType)) (X : String) :
    graftFold ((X, R) :: G) (SessionType.tVar X) = R := by
  simp only [graftFold]
  have hsub : substSessionType (SessionType.tVar X) X R = R := by
    simp [substSessionType]
  rw [hsub]
  exact graftFold_fix_closed hRCl G

/-- Chains distribute over internal choices (mapped targets). -/
private theorem graftFold_dist_intC (G : List (String × SessionType))
    (branches : List (Role × Lab × DataSort × SessionType)) :
    graftFold G (SessionType.internalChoice branches) =
    SessionType.internalChoice
      (branches.map (fun x : Role × Lab × DataSort × SessionType =>
        (x.1, x.2.1, x.2.2.1, graftFold G x.2.2.2))) := by
  induction G generalizing branches with
  | nil => simp [graftFold]
  | cons hd tl ih =>
    rcases hd with ⟨Z, U⟩
    simp only [graftFold]
    have hEq : substSessionType (SessionType.internalChoice branches) Z U =
        SessionType.internalChoice (substSessionType.goInt Z U branches) := by
      simp [substSessionType]
    rw [hEq, go_int_eq_map, ih]
    simp [List.map_map]

/-- Chains distribute over external choices (mapped targets). -/
private theorem graftFold_dist_extC (G : List (String × SessionType))
    (q : Role) (branches : List (Lab × DataSort × SessionType)) :
    graftFold G (SessionType.externalChoice q branches) =
    SessionType.externalChoice q
      (branches.map (fun x : Lab × DataSort × SessionType =>
        (x.1, x.2.1, graftFold G x.2.2))) := by
  induction G generalizing branches with
  | nil => simp [graftFold]
  | cons hd tl ih =>
    rcases hd with ⟨Z, U⟩
    simp only [graftFold]
    have hEq : substSessionType (SessionType.externalChoice q branches) Z U =
        SessionType.externalChoice q (substSessionType.goExt Z U branches) := by
      simp [substSessionType]
    rw [hEq, go_ext_eq_map, ih]
    simp [List.map_map]

/-- Chains distribute over `tRec` up to shadowing: a graft layer for the
    bound variable freezes the subtree for that layer, so the body keeps
    all other layers. -/
private theorem graftFold_dist_tRec (G : List (String × SessionType))
    (Y : String) (B : SessionType) :
    graftFold G (SessionType.tRec Y B) =
    SessionType.tRec Y
      (graftFold (G.filter (fun g : String × SessionType => g.1 != Y)) B) := by
  induction G generalizing B with
  | nil => simp [graftFold, List.filter_nil]
  | cons hd tl ih =>
    rcases hd with ⟨Z, U⟩
    by_cases hZY : Z = Y
    · have hsh : substSessionType (SessionType.tRec Y B) Z U =
          SessionType.tRec Y B := by
        simp [substSessionType, hZY]
      have hfil : List.filter (fun g : String × SessionType => g.1 != Y)
          ((Z, U) :: tl) =
          List.filter (fun g : String × SessionType => g.1 != Y) tl := by
        simp [hZY]
      simp only [graftFold, hsh, hfil]
      exact ih B
    · have hsub : substSessionType (SessionType.tRec Y B) Z U =
          SessionType.tRec Y (substSessionType B Z U) := by
        simp [substSessionType, hZY]
      have hfil : List.filter (fun g : String × SessionType => g.1 != Y)
          ((Z, U) :: tl) =
          (Z, U) :: List.filter (fun g : String × SessionType => g.1 != Y) tl := by
        simp [hZY]
      simp only [graftFold, hsub, hfil]
      rw [ih]

/-- Single grafts are plain substitution. -/
private theorem graftFold_single (X : String) (R B : SessionType) :
    graftFold [(X, R)] B = substSessionType B X R := by
  simp [graftFold]

/-- Chains fuse outside-in. -/
private theorem graftFold_append (G₁ G₂ : List (String × SessionType))
    (T : SessionType) :
    graftFold (G₁ ++ G₂) T = graftFold G₂ (graftFold G₁ T) := by
  induction G₁ generalizing T with
  | nil => simp [graftFold]
  | cons hd tl ih =>
    rcases hd with ⟨Z, U⟩
    simp only [graftFold, List.cons_append]
    exact ih _

/-- Premise rewrapping: unfolding inside a chain extends it. -/
private theorem trec_premise_rewrap (FILT : List (String × SessionType))
    (Y : String) (B' : SessionType) (R₂ : SessionType) :
    substSessionType (graftFold FILT B') Y R₂ =
    graftFold (FILT ++ [(Y, R₂)]) B' := by
  simp [graftFold_append, graftFold_single]

/-- Replaying a `LeadsTo` path in an adequacy derivation reaches a grafted
    copy: branch choices replay via `hall` at same fuel, `tRec` premises
    extend the chain (fuel-dropping); the head graft survives filtering
    (`X ≠ Y` throughout, from `LeadsTo` shadowing-freedom) so the endpoint
    collapses to the replacer. -/
private theorem nav_follow (p : Role) (lab : Lab) (S : DataSort)
    (B : SessionType) (X : String) (R : SessionType) (hRCl : R.IsClosed)
    {Ss : List Role} (hp : SessionType.LeadsTo X B Ss)
    (G : List (String × SessionType))
    (f : Nat) (h : PruneAdequate p lab S f (graftFold ((X, R) :: G) B)) :
    ∃ (g : Nat), g ≤ f ∧ PruneAdequate p lab S g R := by
  revert f G h
  induction hp with
  | var =>
    intro G f h
    rw [graftFold_endpoint hRCl] at h
    exact ⟨f, Nat.le_refl _, h⟩
  | @intC branches bp blab bS T0 Ssub hmem hsub ih =>
    intro G f h
    rw [graftFold_dist_intC] at h
    cases h with
    | intC hall =>
      have hmem' : (bp, blab, bS, graftFold ((X, R) :: G) T0) ∈
          (branches.map (fun x : Role × Lab × DataSort × SessionType =>
            (x.1, x.2.1, x.2.2.1, graftFold ((X, R) :: G) x.2.2.2))) :=
        List.mem_map.mpr ⟨(bp, blab, bS, T0), hmem, rfl⟩
      have hT0 := hall _ hmem'
      obtain ⟨g, hle, hAdR⟩ := ih _ _ hT0
      exact ⟨g, hle, hAdR⟩
  | @extC q branches blab bS T0 Ssub hmem hsub ih =>
    intro G f h
    rw [graftFold_dist_extC] at h
    cases h with
    | extC hall =>
      have hmem' : (blab, bS, graftFold ((X, R) :: G) T0) ∈
          (branches.map (fun x : Lab × DataSort × SessionType =>
            (x.1, x.2.1, graftFold ((X, R) :: G) x.2.2))) :=
        List.mem_map.mpr ⟨(blab, bS, T0), hmem, rfl⟩
      have hT0 := hall _ hmem'
      obtain ⟨g, hle, hAdR⟩ := ih _ _ hT0
      exact ⟨g, hle, hAdR⟩
  | @trec Y B' Ssub hne hsub ih =>
    intro G f h
    have hXne : X ≠ Y := Ne.symm hne
    have hkeep : ((X, R).1 != Y) = true := bne_iff_ne.mpr hXne
    have hFIL : List.filter (fun g : String × SessionType => g.1 != Y)
        ((X, R) :: G) =
        (X, R) :: List.filter (fun g : String × SessionType => g.1 != Y) G := by
      simp [List.filter_cons, hkeep]
    rw [graftFold_dist_tRec, hFIL] at h
    cases h with
    | trec_yes hHas hprem =>
      rw [trec_premise_rewrap, List.cons_append] at hprem
      obtain ⟨g, hle, hAdR⟩ := ih _ _ hprem
      exact ⟨g, by omega, hAdR⟩
    | trec_vac _ hprem =>
      obtain ⟨g, hle, hAdR⟩ := ih _ _ hprem
      exact ⟨g, by omega, hAdR⟩


/-- Unfolding a non-vacuous head admits no adequate fuel: strong fuel
    induction — navigate to a grafted copy, invert its `trec_yes` for
    strict descent. -/
private theorem subst_no_adequate (p : Role) (lab : Lab) (S : DataSort)
    (B : SessionType) (X : String) (hmem : X ∈ B.fv)
    (hCl : (SessionType.tRec X B).IsClosed) :
    ∀ (f : Nat), ¬ PruneAdequate p lab S f
      (substSessionType B X (SessionType.tRec X B)) := by
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    intro hAd
    obtain ⟨Ss, hpath⟩ := SessionType.LeadsTo_of_mem_fv hmem
    have hsingle : graftFold [(X, SessionType.tRec X B)] B =
        substSessionType B X (SessionType.tRec X B) :=
      graftFold_single _ _ _
    rw [← hsingle] at hAd
    obtain ⟨g, hle, hAdR⟩ :=
      nav_follow p lab S B X (SessionType.tRec X B) hCl hpath [] f hAd
    cases hAdR with
    | trec_yes _ hsub =>
      exact ih _ (by omega) hsub
    | trec_vac hfree _ =>
      exact absurd hmem hfree


/-- A non-vacuous `tRec` head admits no adequate fuel at any fuel. -/
theorem trec_head_no_adequate (p : Role) (lab : Lab) (S : DataSort)
    (B : SessionType) (X : String) (hmem : X ∈ B.fv)
    (hCl : (SessionType.tRec X B).IsClosed)
    (f : Nat) (hAd : PruneAdequate p lab S f (SessionType.tRec X B)) :
    False := by
  cases hAd with
  | trec_yes _ hsub =>
    exact subst_no_adequate p lab S B X hmem hCl _ hsub
  | trec_vac hfree _ =>
    exact absurd hmem hfree

/-- No infinite internal paths from NoRec well-formed networks (budget
    strictly decreases each step; counting contradiction). Hence the
    infinite-path half of output-liveness is vacuous there. -/
lemma noInfiniteInternalPath_of_NoRec {Ni : Network}
    (hNR : Ni.NoRec) (hWF : Ni.WellFormed) :
    ¬ ∃ path : InfiniteNetworkPath, path.seq 0 = Ni := by
  rintro ⟨path, h0⟩
  have hdec : ∀ i, networkBudget (path.seq (i + 1)) < networkBudget (path.seq i) := by
    intro i
    have hTr := path.δ_tr i
    obtain ⟨r, p, lab, S, h | h⟩ := path.δ_form i
    · rw [h] at hTr
      have hstar := path_star_reachable_of path Ni h0 i
      exact budget_step_norec hTr (by trivial)
        (net_trans_star_preserves_norec hstar hNR)
        (net_trans_preserves_well_formed hWF hstar)
    · rw [h] at hTr
      have hstar := path_star_reachable_of path Ni h0 i
      exact budget_step_norec hTr (by trivial)
        (net_trans_star_preserves_norec hstar hNR)
        (net_trans_preserves_well_formed hWF hstar)
  have hbound : ∀ n, networkBudget (path.seq n) + n ≤ networkBudget Ni := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ k ih =>
      have h := hdec k
      omega
  have hcon := hbound (networkBudget Ni + 1)
  omega


/-- For NoRec well-formed networks the infinite-path half of output-liveness
    holds vacuously (no infinite internal paths exist). -/
lemma norec_live_infinite_vacuous {N : Network}
    (hNR : N.NoRec) (hWF : N.WellFormed) : IsOutputLiveInfinitePathNetwork N := by
  intro path h0 hfair
  exfalso
  exact noInfiniteInternalPath_of_NoRec hNR hWF ⟨path, h0⟩


/-- Every NoRec well-formed network reaches a stuck configuration
    (well-founded induction on the budget; dichotomy's infinite disjunct
    is impossible here). -/
lemma exists_stuck_reachable_of_NoRec {Ni : Network}
    (hNR : Ni.NoRec) (hWF : Ni.WellFormed) :
    ∃ N', net_trans_star Ni N' ∧ IsStuckNetwork N' := by
  suffices key : ∀ (n : ℕ) (N : Network), N.NoRec → N.WellFormed →
      networkBudget N ≤ n → ∃ N', net_trans_star N N' ∧ IsStuckNetwork N' from
    key _ _ hNR hWF (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro N hNR hWF hle
    by_cases hst : IsStuckNetwork N
    · exact ⟨N, net_trans_star.refl N, hst⟩
    · exfalso
      obtain ⟨δ, N2, hInt, hTr⟩ := stuckStep_of_notStuck hst
      have hlt := budget_step_norec hTr hInt hNR hWF
      omega
  | succ n ih =>
    intro N hNR hWF hle
    by_cases hst : IsStuckNetwork N
    · exact ⟨N, net_trans_star.refl N, hst⟩
    · obtain ⟨δ, N2, hInt, hTr⟩ := stuckStep_of_notStuck hst
      have hlt := budget_step_norec hTr hInt hNR hWF
      obtain ⟨N', hStar', hStuck'⟩ := ih N2 (net_trans_preserves_norec hTr hNR)
        (Network.wellFormedPreserved _ _ _ hWF hTr hInt) (by omega)
      exact ⟨N', net_trans_star.step hInt hTr hStar', hStuck'⟩


/-- Persistent message implies non-liveness (NoRec): if `N` reaches `N'` where role `q`
    occurs, and the message `m` persists in `q`'s queue along every `τ*` from `N'`,
    then `N` is not output-live. Proof: `N'` reaches a stuck `N''` (NoRec termination);
    role preservation plus persistence make `q`'s queue in `N''` nonempty, so its head
    self-dequeues and `NoOrphanMessages N''` fails; `N` reaches that stuck `N''`. -/
theorem msg_always_present_imples_not_output_live_norec {N N' : Network} {q : Role}
    {m : QueueMessage} {T' : SessionType} {Q' : Queue}
    (hNR : N.NoRec) (hWF : N.WellFormed)
    (hStar : net_trans_star N N')
    (hMem : (q, (T', Q')) ∈ N')
    (hPersist : ∀ N'' T'' Q'', net_trans_star N' N'' → (q, (T'', Q'')) ∈ N'' → QueueMem m Q'') :
    ¬ IsOutputLiveNetwork N := by
  intro hLive
  have hNR' : N'.NoRec := net_trans_star_preserves_norec hStar hNR
  have hWF' : N'.WellFormed := net_trans_preserves_well_formed hWF hStar
  obtain ⟨N'', hStar', hStuck''⟩ := exists_stuck_reachable_of_NoRec hNR' hWF'
  obtain ⟨⟨T'', Q''⟩, hmem''⟩ := net_trans_role_preserved hStar' q (T', Q') hMem
  have hMemQ : QueueMem m Q'' := hPersist N'' T'' Q'' hStar' hmem''
  revert hmem'' hMemQ
  cases Q'' with
  | nil =>
    intro hmem'' hMemQ
    cases hMemQ
  | cons hd tl =>
    intro hmem'' _
    obtain ⟨p0, lab0, S0⟩ := hd
    have hDeq : Queue.dequeue (QueueMessage.msg p0 lab0 S0 :: tl)
        (QueueMessage.msg p0 lab0 S0) = some tl := by
      simp [Queue.dequeue, Queue.dequeue.go]
    have hNoOrph : ¬ NoOrphanMessages N'' := by
      intro hNo
      exact hNo q T'' _ p0 lab0 S0 tl hmem'' hDeq
    exact hNoOrph (hLive.2 N'' (net_trans_star.trans hStar hStar') hStuck'')



/-- Output-liveness persists along τ-stars for NoRec well-formed networks
    (infinite half vacuous by termination; stuck half by transitivity). -/
lemma IsOutputLiveNetwork_stable_of_NoRec {Ni N' : Network}
    (hLive : IsOutputLiveNetwork Ni) (hStar : net_trans_star Ni N')
    (hNR : Ni.NoRec) (hWF : Ni.WellFormed) : IsOutputLiveNetwork N' := by
  refine ⟨?_, ?_⟩
  · exact norec_live_infinite_vacuous
      (net_trans_star_preserves_norec hStar hNR) (net_trans_preserves_well_formed hWF hStar)
  · intro N'' hStar' hStuck
    exact hLive.2 N'' (net_trans_star.trans hStar hStar') hStuck
