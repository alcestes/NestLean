import Nest.SessionUtils
import Nest.Drainability
import Nest.SessionAdequacy

open Drainability

-- Example where Can (Q++[msg]) holds but has_coverGoU fails.
-- T = intC [(p,a,s1,U),(p,a,s2,U)] with s1≠s2, U = extC q [(x,sx,tEnd)].
-- Duplicate (role,lab) = (p,a) breaks NoDupl (so T not WF), but Can tolerates it
-- (intC_drain universal over good targets). GoU needs Nodup kept covering both
-- Has-true branches (same (p,a) twice) — impossible.
-- Q = [], msg = (q,x,sx), Qext = [(q,x,sx)].
def JxU : SessionType :=
  SessionType.externalChoice "q" [("x", "sx", SessionType.tEnd)]
def JxT : SessionType :=
  SessionType.internalChoice
    [("p", "a", "s1", JxU), ("p", "a", "s2", JxU)]
def JxMsg : QueueMessage := QueueMessage.msg "q" "x" "sx"

theorem Jx_s1_ne_s2 : ("s1" : String) ≠ "s2" := by decide
theorem Jx_p_ne_q : ("p" : String) ≠ "q" := by decide

theorem Jx_has_U : pruneFirstInputDeepHas "q" "x" "sx" JxU = true := by
  decide

theorem Jx_deq : Queue.dequeue ([QueueMessage.msg "q" "x" "sx"] : Queue)
    (QueueMessage.msg "q" "x" "sx") = some ([] : Queue) := rfl

-- Can target: U accepts [(q,x,sx)] then nil.
theorem Jx_Can_U : CanAlwaysDrainInternalDeepRec JxU [JxMsg] := by
  unfold JxU JxMsg
  apply CanAlwaysDrainInternalDeepRec.extC_deq "q"
    [("x", "sx", SessionType.tEnd)] [QueueMessage.msg "q" "x" "sx"] []
    "x" "sx" SessionType.tEnd (List.mem_cons.mpr (Or.inl rfl)) Jx_deq ?_
  exact CanAlwaysDrainInternalDeepRec.drained_nil _

-- Can ext: intC_drain, Q senders {q} disjoint from branch roles {p},
-- both targets good via Jx_Can_U.
theorem Jx_Can_ext : CanAlwaysDrainInternalDeepRec JxT [JxMsg] := by
  unfold JxT
  apply CanAlwaysDrainInternalDeepRec.intC_drain
    [("p", "a", "s1", JxU), ("p", "a", "s2", JxU)]
    [JxMsg] ?hfresh ?hall
  · intro r' l' s' U' hmem m hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · simp only [JxMsg, List.mem_cons, List.mem_nil_iff, or_false] at hm
      subst hm
      decide
    · simp only [JxMsg, List.mem_cons, List.mem_nil_iff, or_false] at hm
      subst hm
      decide
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · simpa [JxMsg] using Jx_Can_U
    · simpa [JxMsg] using Jx_Can_U

-- No GoU for (q,x,sx) from JxT: intC only; hfull forces two kept entries
-- (p,a,s1,_) and (p,a,s2,_) with s1≠s2, so kept.length≥2 while
-- kept.map (role,lab) Nodup sublist of [(p,a),(p,a)] forces equality to the
-- duplicate list — contradicting Nodup.
theorem Jx_noGoU : ¬ ∃ n U, go_unfold_rel "q" "x" "sx" n JxT U := by
  rintro ⟨n, U, d⟩
  unfold JxT at d
  cases d with
  | intC _ branches kept hall hkey hNodupKept horder horder3 hfull =>
    -- branches must be the concrete two-element list (from JxT shape).
    -- hfull for both Has-true branches (targets JxU, Has true).
    have hB1 : ("p", "a", "s1", JxU) ∈
        ([("p", "a", "s1", JxU), ("p", "a", "s2", JxU)] :
          List (Role × Lab × DataSort × SessionType)) :=
      List.mem_cons.mpr (Or.inl rfl)
    have hB2 : ("p", "a", "s2", JxU) ∈
        ([("p", "a", "s1", JxU), ("p", "a", "s2", JxU)] :
          List (Role × Lab × DataSort × SessionType)) :=
      List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨T1, hK1⟩ := hfull "p" "a" "s1" JxU hB1 Jx_has_U
    obtain ⟨T2, hK2⟩ := hfull "p" "a" "s2" JxU hB2 Jx_has_U
    -- K1 = (p,a,s1,T1), K2 = (p,a,s2,T2) distinct via s1≠s2.
    have hne : (("p", "a", "s1", T1) : Role × Lab × DataSort × SessionType) ≠
        ("p", "a", "s2", T2) := by
      intro hcon
      have hs : ("s1" : String) = "s2" := congrArg (fun x => x.2.2.1) hcon
      exact absurd hs Jx_s1_ne_s2
    have hK1' : (("p", "a", "s1", T1) : Role × Lab × DataSort × SessionType) ∈ kept := hK1
    have hK2' : (("p", "a", "s2", T2) : Role × Lab × DataSort × SessionType) ∈ kept := hK2
    -- kept.length ≥ 2 by casing kept (nil/singleton impossible via distinct mems).
    have hlen2 : 2 ≤ kept.length := by
      cases kept with
      | nil =>
        simp at hK1'
      | cons hd tl =>
        cases tl with
        | nil =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK1' hK2'
          have hEq : (("p", "a", "s1", T1) : Role × Lab × DataSort × SessionType) =
              (("p", "a", "s2", T2) : Role × Lab × DataSort × SessionType) :=
            hK1'.trans hK2'.symm
          exact absurd hEq hne
        | cons _ _ =>
          simp
    -- kept.map (role,lab) sublist of [(p,a),(p,a)], Nodup, length ≥2 forces dup.
    have hmap_len : (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))).length = kept.length := by
      simp
    have hle : (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))).length ≤ 2 :=
      calc (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))).length
          ≤ ([("p", "a"), ("p", "a")] : List (Role × Lab)).length :=
            horder.length_le
        _ = 2 := rfl
    rw [hmap_len] at hle
    have hlen_eq : kept.length = 2 := by omega
    have hmap_eq : kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1)) =
        ([("p", "a"), ("p", "a")] : List (Role × Lab)) := by
      have hlen_map : (kept.map (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))).length =
          ([("p", "a"), ("p", "a")] : List (Role × Lab)).length := by
        simp [hmap_len, hlen_eq]
      -- horder : kept.map Sublist branches.map; branches.map = [(p,a),(p,a)].
      have hbr : (([("p", "a", "s1", JxU), ("p", "a", "s2", JxU)] :
          List (Role × Lab × DataSort × SessionType)).map
          (fun x : Role × Lab × DataSort × SessionType => (x.1, x.2.1))) =
          ([("p", "a"), ("p", "a")] : List (Role × Lab)) := rfl
      rw [hbr] at horder
      exact horder.eq_of_length hlen_map
    rw [hmap_eq] at hNodupKept
    simp at hNodupKept

-- has_coverGoU (with Q = []) fails: pre=[] forces V=T and head (q,x,sx), i.e. GoU.
theorem Jx_noCover : ¬ ∀ (pre Q0 : Queue) (V : SessionType)
    (p0 : Role) (lab0 : Lab) (S0 : DataSort) (Q0' : Queue),
    ([] : Queue) ++ [JxMsg] = pre ++ Q0 →
    monitor_fold_aux pre JxT V →
    Q0 = QueueMessage.msg p0 lab0 S0 :: Q0' →
    ∃ n U, go_unfold_rel p0 lab0 S0 n V U := by
  intro has_cover
  have hGet := has_cover [] [JxMsg] JxT "q" "x" "sx" [] rfl rfl rfl
  exact Jx_noGoU hGet

-- Verdict: CanExt holds, cover fails.
theorem Jx_verdict : CanAlwaysDrainInternalDeepRec JxT ([] ++ [JxMsg]) ∧
    ¬ ∀ (pre Q0 : Queue) (V : SessionType)
    (p0 : Role) (lab0 : Lab) (S0 : DataSort) (Q0' : Queue),
    ([] : Queue) ++ [JxMsg] = pre ++ Q0 →
    monitor_fold_aux pre JxT V →
    Q0 = QueueMessage.msg p0 lab0 S0 :: Q0' →
    ∃ n U, go_unfold_rel p0 lab0 S0 n V U :=
  ⟨by simpa using Jx_Can_ext, Jx_noCover⟩

-- Well-formed closed variant: same phenomenon (Can holds, cover fails) with WF.
-- KxT = tRec X (extC r [(a,sa,D),(b,sb,X)]), D = extC q [(x,sx,tEnd)], r≠q, a≠b.
-- Has T true via D (direct); X-branch after subst becomes T (Has-true) forcing
-- GoU cycle T(n+1) → S(n) → T(n) — impossible by induction on n.
-- Can holds existentially via D (ignoring the loop); WF holds (keys a,b distinct).
def KxD : SessionType :=
  SessionType.externalChoice "q" [("x", "sx", SessionType.tEnd)]
def KxB : SessionType :=
  SessionType.externalChoice "r"
    [("a", "sa", KxD), ("b", "sb", SessionType.tVar "X")]
def KxT : SessionType := SessionType.tRec "X" KxB
def KxS : SessionType :=
  SessionType.externalChoice "r" [("a", "sa", KxD), ("b", "sb", KxT)]
def KxMsg : QueueMessage := QueueMessage.msg "q" "x" "sx"

theorem KxS_eq : substSessionType KxB "X" KxT = KxS := rfl

theorem Kx_r_ne_q : ("r" : String) ≠ "q" := by decide
theorem Kx_a_ne_b : ("a" : String) ≠ "b" := by decide

theorem Kx_has_D : pruneFirstInputDeepHas "q" "x" "sx" KxD = true := by
  decide
theorem Kx_has_T : pruneFirstInputDeepHas "q" "x" "sx" KxT = true := by
  decide

theorem KxD_nodupl : KxD.NoDupl := by
  unfold KxD
  apply SessionType.NoDupl.externalChoice (by decide) (by decide)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  subst hx
  exact SessionType.NoDupl.end

theorem KxT_wf : KxT.WellFormed := by
  unfold KxT
  refine ⟨?_, ?_, ?_⟩
  · apply SessionType.NoDupl.tRec
    unfold KxB
    apply SessionType.NoDupl.externalChoice (by decide) (by decide)
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact KxD_nodupl
    · exact SessionType.NoDupl.tVar _
  · unfold SessionType.IsClosed
    decide
  · apply SessionType.Contractive.tRec
    · unfold KxB
      apply SessionType.Contractive.externalChoice
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl
      · unfold KxD
        apply SessionType.Contractive.externalChoice
        intro y hy
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        subst hy
        exact SessionType.Contractive.end
      · exact SessionType.Contractive.tVar _
    · simp [KxB, SessionType.Guarded]

theorem Kx_closed : KxT.IsClosed := KxT_wf.2.1

theorem Kx_deq : Queue.dequeue ([QueueMessage.msg "q" "x" "sx"] : Queue)
    (QueueMessage.msg "q" "x" "sx") = some ([] : Queue) := rfl

theorem Kx_Can_D : CanAlwaysDrainInternalDeepRec KxD [KxMsg] := by
  unfold KxD KxMsg
  apply CanAlwaysDrainInternalDeepRec.extC_deq "q"
    [("x", "sx", SessionType.tEnd)] [QueueMessage.msg "q" "x" "sx"] []
    "x" "sx" SessionType.tEnd (List.mem_cons.mpr (Or.inl rfl)) Kx_deq ?_
  exact CanAlwaysDrainInternalDeepRec.drained_nil _

-- Can ext via trec → S, extC_spec choosing good (a,sa,D); Q senders {q} ≠ r.
theorem Kx_Can_ext : CanAlwaysDrainInternalDeepRec KxT [KxMsg] := by
  unfold KxT
  apply CanAlwaysDrainInternalDeepRec.trec_step _ _ _ (by decide) ?_
  have hS : substSessionType KxB "X" (SessionType.tRec "X" KxB) = KxS := rfl
  rw [hS]
  unfold KxS
  apply CanAlwaysDrainInternalDeepRec.extC_spec "r"
    [("a", "sa", KxD), ("b", "sb", KxT)] [KxMsg] ?habs
    ("a", "sa", KxD) (List.mem_cons.mpr (Or.inl rfl)) ?_
  · intro m hm
    simp only [KxMsg, List.mem_cons, List.mem_nil_iff, or_false] at hm
    subst hm
    decide
  · simpa [KxMsg] using Kx_Can_D

-- No GoU for (q,x,sx) from KxT at any height: trec forces S, extC_q forces
-- the looping (b,sb,T) branch (Has-true), giving GoU n T from GoU (n+1) T.
theorem Kx_noGoU : ∀ n U, ¬ go_unfold_rel "q" "x" "sx" n KxT U := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U hD
    unfold KxT at hD
    cases hD with
    | trec n' X' B' U' hsub =>
      have hS : substSessionType KxB "X" (SessionType.tRec "X" KxB) = KxS := rfl
      rw [hS] at hsub
      unfold KxS at hsub
      cases hsub with
      | extC_p n'' q'' branches hq hmem =>
        exact absurd hq Kx_r_ne_q
      | extC_p_miss n'' q'' branches hq hmiss =>
        exact absurd hq Kx_r_ne_q
      | extC_q n'' q'' branches kept hq hall hkey hNodupKept horder horder3 hfull =>
        have hmemB : ("b", "sb", KxT) ∈
            ([("a", "sa", KxD), ("b", "sb", KxT)] :
              List (Lab × DataSort × SessionType)) :=
          List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
        obtain ⟨T1, hK⟩ := hfull "b" "sb" KxT hmemB Kx_has_T
        have hGo : go_unfold_rel "q" "x" "sx" n'' KxT T1 :=
          hall KxT T1 "b" "sb" hmemB hK Kx_has_T
        exact ih n'' (by omega) T1 hGo

theorem Kx_noGoU_ex : ¬ ∃ n U, go_unfold_rel "q" "x" "sx" n KxT U := by
  rintro ⟨n, U, d⟩
  exact Kx_noGoU n U d

-- has_coverGoU (with Q = []) fails: pre=[] forces V=T and head (q,x,sx), i.e. GoU.
theorem Kx_noCover : ¬ ∀ (pre Q0 : Queue) (V : SessionType)
    (p0 : Role) (lab0 : Lab) (S0 : DataSort) (Q0' : Queue),
    ([] : Queue) ++ [KxMsg] = pre ++ Q0 →
    monitor_fold_aux pre KxT V →
    Q0 = QueueMessage.msg p0 lab0 S0 :: Q0' →
    ∃ n U, go_unfold_rel p0 lab0 S0 n V U := by
  intro has_cover
  have hGet := has_cover [] [KxMsg] KxT "q" "x" "sx" [] rfl rfl rfl
  exact Kx_noGoU_ex hGet

-- Verdict: WF + closed, CanExt holds, cover fails.
theorem Kx_verdict : KxT.WellFormed ∧ KxT.IsClosed ∧
    CanAlwaysDrainInternalDeepRec KxT ([] ++ [KxMsg]) ∧
    ¬ ∀ (pre Q0 : Queue) (V : SessionType)
    (p0 : Role) (lab0 : Lab) (S0 : DataSort) (Q0' : Queue),
    ([] : Queue) ++ [KxMsg] = pre ++ Q0 →
    monitor_fold_aux pre KxT V →
    Q0 = QueueMessage.msg p0 lab0 S0 :: Q0' →
    ∃ n U, go_unfold_rel p0 lab0 S0 n V U :=
  ⟨KxT_wf, Kx_closed, by simpa using Kx_Can_ext, Kx_noCover⟩

-- KxT is monitorable (root PruneStep closure = {T,S,D,tEnd}, finite),
-- yet not acyclic (T → S → T) so GoU need not exist.
theorem Kx_monitorable : _root_.Monitorable KxT := by
  show Set.Finite {U : SessionType | Relation.ReflTransGen _root_.PruneStep KxT U}
  apply Set.Finite.subset (Finset.finite_toSet _)
  intro U hU
  simp only [Finset.mem_coe, Set.mem_ofPred_eq] at hU ⊢
  have hmem : ∀ V : SessionType,
      Relation.ReflTransGen _root_.PruneStep KxT V →
      V ∈ ({KxT, KxS, KxD, SessionType.tEnd} : Finset SessionType) := by
    intro V hV
    induction hV with
    | refl =>
      simp
    | tail hRTC hStep ih =>
      simp only [Finset.mem_insert, Finset.mem_singleton] at ih
      rcases ih with rfl | rfl | rfl | rfl
      · -- V = KxT (tRec): only trec fires, to KxS.
        unfold KxT at hStep
        cases hStep with
        | trec =>
          have hEq : SessionType.tRec "X" KxB = KxT := rfl
          -- goal: subst .. ∈ finset; it is KxS by rfl.
          have : substSessionType KxB "X" (SessionType.tRec "X" KxB) ∈
              ({KxT, KxS, KxD, SessionType.tEnd} : Finset SessionType) := by
            have hKS : substSessionType KxB "X" (SessionType.tRec "X" KxB) = KxS := rfl
            rw [hKS]
            simp
          simpa using this
      · -- V = KxS (extC r): to KxD or KxT.
        unfold KxS at hStep
        cases hStep with
        | extC hmem =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
          rcases hmem with rfl | rfl
          · simp
          · simp
      · -- V = KxD (extC q singleton): to tEnd.
        unfold KxD at hStep
        cases hStep with
        | extC hmem =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
          subst hmem
          simp
      · -- V = tEnd: stuck.
        cases hStep
  exact hmem U hU

-- Owner-mismatch Base refutations. The tag is generalized to a variable first
-- so dependent elimination never sees the closed literals "q" and "r" at once.
theorem base_KxS_false {V : SessionType}
    (hb : mon_tr_yes_base KxS (ext_tag.recv "q" "x" "sx") V) : False := by
  generalize hγ : (ext_tag.recv "q" "x" "sx") = γ' at hb
  unfold KxS at hb
  cases hb with
  | extC huniq hmem =>
    simp at hγ

theorem base_KxT_false {V : SessionType}
    (hb : mon_tr_yes_base KxT (ext_tag.recv "q" "x" "sx") V) : False := by
  unfold KxT at hb
  cases hb with
  | tRec hS =>
    have hSk : substSessionType KxB "X" (SessionType.tRec "X" KxB) = KxS := rfl
    rw [hSk] at hS
    exact base_KxS_false hS

-- Key induction: no maximal derivation about KxT or KxS. The tag γ is also
-- generalized (with equation hγ) since `induction` needs every index variable.
-- The disjunctive motive covers both the outer KxT goal and the S-level
-- sub-derivation (reached by rfl, since the unfolded subst is KxS).
-- The pfxExt-about-KxS branch uses the outer KxT-acceptor E0 for
-- MaxDeriv-hcover on the looping (b,sb,T) branch.
theorem Kx_noMax_gen {Tmid : SessionType}
    (E0 : mon_tr_yes_exist KxT (ext_tag.recv "q" "x" "sx") Tmid) :
    ∀ (T : SessionType) (γ : ext_tag) (V : SessionType)
    (E : mon_tr_yes_exist T γ V)
    (_M : mon_tr_yes_max_deriv E),
    γ = ext_tag.recv "q" "x" "sx" → T = KxT ∨ T = KxS → False := by
  intro T γ V E M
  induction M with
  | @base T' γ' V' hb =>
    intro hγ hT
    subst hγ
    rcases hT with hL | hR
    · subst hL
      exact base_KxT_false hb
    · subst hR
      exact base_KxS_false hb
  | @pfxInt branches kept q lab S T' hne hno hkept hall hNodupKept hkey hallMax
      hcover horder ih =>
    intro hγ hT
    cases hγ
    rcases hT with hL | hR
    · unfold KxT at hL
      nomatch hL
    · unfold KxS at hR
      nomatch hR
  | @pfxExt p branches kept q lab S T' hne hneq hkept hall hNodupKept hkey hallMax
      hcover horder ih =>
    intro hγ hT
    cases hγ
    rcases hT with hL | hR
    · unfold KxT at hL
      nomatch hL
    · unfold KxS at hR
      cases hR
      have hmemB : ("b", "sb", KxT) ∈
          ([("a", "sa", KxD), ("b", "sb", KxT)] : List (Lab × DataSort × SessionType)) :=
        List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      obtain ⟨T1, hK⟩ := hcover "b" "sb" KxT hmemB ⟨Tmid, E0⟩
      have hsubE : mon_tr_yes_exist KxT (ext_tag.recv "q" "x" "sx") T1 :=
        hall KxT T1 "b" "sb" hmemB hK
      exact ih KxT T1 "b" "sb" hmemB hK hsubE rfl (Or.inl rfl)
  | @unfold X B γ' V' h hmax ih =>
    intro hγ hT
    rcases hT with hL | hR
    · unfold KxT at hL
      cases hL
      exact ih hγ (Or.inr rfl)
    · unfold KxS at hR
      nomatch hR

-- No monitor run for the single-message queue.
theorem Kx_noEnc : ¬ ∃ M', monitor_fold (KxT, [KxMsg]) M' := by
  intro h
  obtain ⟨M', hQ⟩ := h
  simp only [monitor_fold, monitor_fold_aux, KxMsg] at hQ
  obtain ⟨Tmid, hYes, hRest⟩ := hQ
  obtain ⟨E0, M0⟩ := hYes
  cases M0 with
  | @unfold X B γ' V' h hmax =>
    exact Kx_noMax_gen (mon_tr_yes_exist.unfold h) _ _ _ _ hmax rfl (Or.inr rfl)
  | @base T' γ' V' hb =>
    exact base_KxT_false hb

-- Drainability-namespace variant (for the duality lemmas): same four-state closure.
theorem Kx_monitorable_DR : Drainability.Monitorable KxT := by
  show Set.Finite {U : SessionType | Relation.ReflTransGen Drainability.PruneStep KxT U}
  apply Set.Finite.subset (Finset.finite_toSet _)
  intro U hU
  simp only [Finset.mem_coe, Set.mem_ofPred_eq] at hU ⊢
  have hmem : ∀ V : SessionType,
      Relation.ReflTransGen Drainability.PruneStep KxT V →
      V ∈ ({KxT, KxS, KxD, SessionType.tEnd} : Finset SessionType) := by
    intro V hV
    induction hV with
    | refl =>
      simp
    | tail hRTC hStep ih =>
      simp only [Finset.mem_insert, Finset.mem_singleton] at ih
      rcases ih with rfl | rfl | rfl | rfl
      · unfold KxT at hStep
        cases hStep with
        | trec =>
          have : substSessionType KxB "X" (SessionType.tRec "X" KxB) ∈
              ({KxT, KxS, KxD, SessionType.tEnd} : Finset SessionType) := by
            have hKS : substSessionType KxB "X" (SessionType.tRec "X" KxB) = KxS := rfl
            rw [hKS]
            simp
          simpa using this
      · unfold KxS at hStep
        cases hStep with
        | extC hmem =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
          rcases hmem with rfl | rfl
          · simp
          · simp
      · unfold KxD at hStep
        cases hStep with
        | extC hmem =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
          subst hmem
          simp
      · cases hStep
  exact hmem U hU

theorem Kx_can_nil : CanAlwaysDrainInternalDeepRec KxT [] :=
  CanAlwaysDrainInternalDeepRec.drained_nil _

theorem Kx_enc_nil : ∃ M, monitor_fold (KxT, []) M :=
  ⟨KxT, by simp [monitor_fold, monitor_fold_aux]⟩

theorem Kx_not_cannot : ¬ CannotAlwaysDrainInternalDeepRec KxT ([] ++ [KxMsg]) := by
  have h : ¬ CannotAlwaysDrainInternalDeepRec KxT [KxMsg] :=
    drainrec_not_cannot_of_can KxT_wf Kx_Can_ext
  simpa using h

-- Refutation of the inverse (¬enc → Cannot): KxT has no monitor run on [msg]
-- yet drains fine (hence no failure tableau, by the WF-only forward direction).
theorem Kx_refutes_noenc_implies_cannot :
    KxT.WellFormed ∧ KxT.IsClosed ∧ Drainability.Monitorable KxT ∧
    (¬ ∃ M, monitor_fold (KxT, [KxMsg]) M) ∧
    ¬ CannotAlwaysDrainInternalDeepRec KxT [KxMsg] :=
  ⟨KxT_wf, Kx_closed, Kx_monitorable_DR, Kx_noEnc,
    drainrec_not_cannot_of_can KxT_wf Kx_Can_ext⟩

-- Full refutation: all premises of the as-stated monitor_no_implies_cannotdrain
-- hold for (KxT, [], KxMsg), but its conclusion is false.
theorem Kx_refutes :
    KxT.WellFormed ∧ KxT.IsClosed ∧ Drainability.Monitorable KxT ∧
    CanAlwaysDrainInternalDeepRec KxT [] ∧ (∃ M, monitor_fold (KxT, []) M) ∧
    (¬ ∃ M', monitor_fold (KxT, [] ++ [KxMsg]) M') ∧
    ¬ CannotAlwaysDrainInternalDeepRec KxT ([] ++ [KxMsg]) := by
  refine ⟨KxT_wf, Kx_closed, Kx_monitorable_DR, Kx_can_nil, Kx_enc_nil, ?_,
    Kx_not_cannot⟩
  simpa using Kx_noEnc
