import Nest.SessionUtils
import Nest.Drainability
import Nest.SessionAdequacy
import Nest.MonitorToolkit

open Drainability

-- Example 1 (non-recursive): T = extC p [(a, Ta), (b, Tb)],
-- Ta = extC q [(x, l, end)], Tb = extC q [(y, l, end)], Q = [(q, x, l)],
-- p ≠ q, a ≠ b, x ≠ y. Final msg for extended queue: msg p a sa.
def Ex1Ta : SessionType :=
  SessionType.externalChoice "q" [("x", "l", SessionType.tEnd)]
def Ex1Tb : SessionType :=
  SessionType.externalChoice "q" [("y", "l", SessionType.tEnd)]
def Ex1T : SessionType :=
  SessionType.externalChoice "p" [("a", "sa", Ex1Ta), ("b", "sb", Ex1Tb)]
def Ex1Q : Queue := [QueueMessage.msg "q" "x" "l"]
def Ex1Msg : QueueMessage := QueueMessage.msg "p" "a" "sa"

theorem Ex1Ta_nodupl : Ex1Ta.NoDupl := by
  unfold Ex1Ta
  apply SessionType.NoDupl.externalChoice (by decide) (by decide)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  subst hx
  exact SessionType.NoDupl.end

theorem Ex1Tb_nodupl : Ex1Tb.NoDupl := by
  unfold Ex1Tb
  apply SessionType.NoDupl.externalChoice (by decide) (by decide)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  subst hx
  exact SessionType.NoDupl.end

theorem Ex1T_nodupl : Ex1T.NoDupl := by
  unfold Ex1T
  apply SessionType.NoDupl.externalChoice (by decide) (by decide)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact Ex1Ta_nodupl
  · exact Ex1Tb_nodupl

theorem Ex1T_closed : Ex1T.IsClosed := by
  unfold Ex1T Ex1Ta Ex1Tb SessionType.IsClosed
  decide

theorem Ex1Ta_contractive : Ex1Ta.Contractive := by
  unfold Ex1Ta
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  subst hx
  exact SessionType.Contractive.end

theorem Ex1Tb_contractive : Ex1Tb.Contractive := by
  unfold Ex1Tb
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  subst hx
  exact SessionType.Contractive.end

theorem Ex1T_contractive : Ex1T.Contractive := by
  unfold Ex1T
  apply SessionType.Contractive.externalChoice
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact Ex1Ta_contractive
  · exact Ex1Tb_contractive

theorem Ex1T_wf : Ex1T.WellFormed :=
  ⟨Ex1T_nodupl, Ex1T_closed, Ex1T_contractive⟩

-- Q head sender q ≠ p owner, so absent p holds via decide (p≠q distinct lits).
theorem Ex1_absent : ∀ m ∈ Ex1Q, m.1 ≠ "p" := by
  intro m hm
  simp only [Ex1Q, List.mem_cons, List.mem_nil_iff, or_false] at hm
  subst hm
  decide

-- Dequeue head q-x in Ta to [] via rfl (concrete dequeue computation).
theorem Ex1Q_deq_Ta : Ex1Q.dequeue (QueueMessage.msg "q" "x" "l") = some ([] : Queue) := by
  rfl

theorem Ex1_Can_Q : CanAlwaysDrainInternalDeepRec Ex1T Ex1Q := by
  unfold Ex1T Ex1Q
  apply CanAlwaysDrainInternalDeepRec.extC_spec "p"
    _ _ (fun m hm => by simpa using Ex1_absent m hm)
    ("a", "sa", Ex1Ta) (List.mem_cons.mpr (Or.inl rfl)) ?_
  -- Ta drains [q-x] via deq to tEnd [].
  unfold Ex1Ta
  apply CanAlwaysDrainInternalDeepRec.extC_deq "q" _ _ _ "x" "l" SessionType.tEnd
    (List.mem_cons.mpr (Or.inl rfl)) Ex1Q_deq_Ta ?_
  exact CanAlwaysDrainInternalDeepRec.drained_nil _

-- Tb has no Exist for head (q,x): base needs key (x) present in [(y,_,_)] (y≠x),
-- pfx needs owner≠head (false, owner=head=q). Cases + decide.
theorem Ex1Tb_noExist : ∀ (T1 : SessionType),
    ¬ mon_tr_yes_exist Ex1Tb (ext_tag.recv "q" "x" "l") T1 := by
  intro T1 hE
  unfold Ex1Tb at hE
  cases hE with
  | base hb =>
    cases hb with
    | extC _ hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      have hxy : ("x" : String) = "y" := congrArg Prod.fst hmem
      exact absurd hxy (by decide)
  | pfxExt hne hneq _ _ _ _ =>
    exact absurd rfl hneq

theorem Ex1Ta_yes : mon_tr_yes Ex1Ta (ext_tag.recv "q" "x" "l") SessionType.tEnd := by
  refine ⟨mon_tr_yes_exist.base ?_, @mon_tr_yes_max_deriv.base _ _ _ ?_⟩
  · apply mon_tr_yes_base.extC (by decide) (List.mem_cons.mpr (Or.inl rfl))
  · apply mon_tr_yes_base.extC (by decide) (List.mem_cons.mpr (Or.inl rfl))

theorem Ex1_fold_Q : ∃ M, monitor_fold (Ex1T, Ex1Q) M := by
  refine ⟨SessionType.externalChoice "p" [("a", "sa", SessionType.tEnd)],
    SessionType.externalChoice "p" [("a", "sa", SessionType.tEnd)],
    ⟨?hE, ?hM⟩, rfl⟩
  · -- Exist via pfxExt singleton (Tb pruned: no Exist via Tb_noExist for coverage? No,
    -- Exist pfxExt needs hall (sub-Exist for kept) + hkey (kept→source key existence, no Has/Exist
    -- requirement for pruned branches). hall for kept (a,tEnd) via base Ta_yes.1; hkey via mem.
    case hE =>
      unfold Ex1T
      apply @mon_tr_yes_exist.pfxExt "p" [("a", "sa", Ex1Ta), ("b", "sb", Ex1Tb)]
        [("a", "sa", SessionType.tEnd)] "q" "x" "l"
        (SessionType.externalChoice "p" [("a", "sa", SessionType.tEnd)])
        (by decide) (by decide) rfl ?hall (by decide) ?hkey
      · case hall =>
        intro T0 T1 l s hB hK
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB hK
        rcases hB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · obtain ⟨rfl, rfl, rfl⟩ := hK
          exact Ex1Ta_yes.1
        · -- hK : (b,sb,T1) = (a,sa,tEnd) requiring b=a (false, a≠b distinct lits).
          have hba : ("b" : String) = "a" := congrArg Prod.fst hK
          exact absurd hba (by decide)
      · case hkey =>
        intro l s T1 hK
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
        obtain ⟨rfl, rfl, rfl⟩ := hK
        exact ⟨Ex1Ta, List.mem_cons.mpr (Or.inl rfl)⟩
  · -- Maximality: hallMax base, hcover via Tb_noExist (all acceptors kept), horder singleton.
    case hM =>
      unfold Ex1T
      apply mon_tr_yes_max_deriv.pfxExt ?hallMax ?hcover ?horder
      · case hallMax =>
        intro T0 T1 l s hB hK hsub
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB hK
        rcases hB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hK
          obtain ⟨rfl, rfl, rfl⟩ := hK
          -- hsub : Exist Ta recv tEnd. Ta head extC q with owner=head sender → base only
          -- (pfx impossible via hneq false, unfold impossible via head mismatch).
          -- Show MaxDeriv base via cases discarding pfx/unfold, then base.
          cases hsub with
          | base hb =>
            exact @mon_tr_yes_max_deriv.base _ _ _ hb
          | pfxExt hne hneq _ _ _ _ =>
            exact absurd rfl hneq
        · simp at hK
      · case hcover =>
        intro l s T0 hB hex
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hB
        rcases hB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · obtain ⟨T1, hE⟩ := hex
          -- T0 = Ta, Exist Ta → kept (a,tEnd) via ⟨rfl, rfl, rfl⟩ (same key a,sa? Actually outer keys
          -- (a,sa) vs (b,sb) distinct labs a≠b. Good – kept contains (a,sa,tEnd) with same key.
          -- Need T1 = tEnd? Actually Exist Ta recv T1 with Ta=extC q [(x,...)] head (q,x)
          -- owner=head sender → base only, so T1 = tEnd via uniqueness? Actually base target
          -- pinned by key present (x ∈ [(x,...)] singleton, so T1 = tEnd via ...? Need ext_target_unique?
          -- Simpler: kept contains (a,sa,tEnd) with same outer key (a,sa), regardless of T1 value?
          -- hcover requires ∃ T1, (l,s,T1)∈kept with same (l,s) = (a,sa)? Actually hcover quantifies
          -- over (l,s,T0)∈branches with Exist T0 → ∃ T1, (l,s,T1)∈kept (same l,s, any T1).
          -- For (a,sa,Ta) with Exist Ta (via base to tEnd), kept (a,sa,tEnd) works (same l=a,s=sa).
          -- Provide ⟨tEnd, mem_cons inl rfl⟩ (rfl, since kept singleton contains (a,sa,tEnd)).
          exact ⟨SessionType.tEnd, List.mem_cons.mpr (Or.inl rfl)⟩
        · obtain ⟨T1, hE⟩ := hex
          -- T0 = Tb, Exist Tb impossible via Tb_noExist → ex falso.
          have hcon := Ex1Tb_noExist T1 hE
          exact False.elim hcon
      · case horder =>
        -- kept keys [(a)] sublist source keys [(a),(b)] with a≠b distinct.
        simp only [List.map_cons, List.map_nil]
        exact List.Sublist.cons_cons _ (List.Sublist.slnil _)
