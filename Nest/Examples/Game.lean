import Nest.SessionUtils
import Nest.SessionAdequacy
import Nest.Tests.PrunableTest
import Nest.Drainability
import Nest.Examples.ProofUtils
import Nest.MonitorLTSCo
import Nest.MonitorCoFun

namespace Game

/- Session types from the NEST P4 testbed:
   `NEST/nest/nest_scala/src/main/scala/examples/10_game.scala`
   (Scala package `game`; file `10_game.scala` maps to this module
   since Lean module names may not start with a digit).
   Translated below are the three `lst_*` local session types
   (`lst_Coordinator`, `lst_GameServer`, `lst_Player`). The single
   `lst_Player` type is shared by `a_Player1` and `a_Player2` in the
   Scala file, so it appears once here. The commented-out `Player_3` /
   `Player_4` agents have no session types and are skipped. Switch
   setup, IP rules, port checks and monitor wiring from `setup` are
   not session types and are not translated. Translation conventions:
   `IntChoice` branches become `internalChoice` branches
   `(agent, label, sort, cont)`; `ExtChoice` branches become
   `externalChoice` branches `(label, sort, cont)`; `Rec`/`Var`/`End`
   become `tRec`/`tVar`/`tEnd`. Agents become roles, labels stay
   labels. The Scala types carry no payload sorts, so every branch
   uses the placeholder sort `"unit"`. -/

/-- `lst_Coordinator`. -/
def Coordinator : SessionType :=
  SessionType.internalChoice
    [("Player_1", "Init", "unit",
      SessionType.internalChoice
        [("Player_2", "Init", "unit",
          SessionType.externalChoice "Player_1"
            [("LookForGame", "unit",
              SessionType.externalChoice "Player_2"
                [("LookForGame", "unit",
                  SessionType.internalChoice
                    [("Player_1", "GameFound", "unit",
                      SessionType.internalChoice
                        [("Player_2", "GameFound", "unit",
                          SessionType.internalChoice
                            [("GameServer", "GameFound", "unit",
                              SessionType.externalChoice "GameServer"
                                [("GameOver", "unit",
                                  SessionType.tEnd)])])])])])])])]

/-- `lst_GameServer`. -/
def GameServer : SessionType :=
  SessionType.externalChoice "Coordinator"
    [("GameFound", "unit",
      SessionType.tRec "GameRound"
        (SessionType.internalChoice
          [("Player_1", "TurnStart", "unit",
            SessionType.externalChoice "Player_1"
              [("TakeAction", "unit",
                SessionType.internalChoice
                  [("Player_2", "TurnStart", "unit",
                    SessionType.externalChoice "Player_2"
                      [("TakeAction", "unit",
                        SessionType.tVar "GameRound")])])]),
           ("Player_1", "YouWon", "unit",
            SessionType.internalChoice
              [("Player_2", "YouLost", "unit",
                SessionType.internalChoice
                  [("Coordinator", "GameOver", "unit",
                    SessionType.tEnd)])]),
           ("Player_1", "YouLost", "unit",
            SessionType.internalChoice
              [("Player_2", "YouWon", "unit",
                SessionType.internalChoice
                  [("Coordinator", "GameOver", "unit",
                    SessionType.tEnd)])])]))]

/-- `lst_Player` (shared by `Player_1` and `Player_2`). -/
def Player : SessionType :=
  SessionType.externalChoice "Coordinator"
    [("Init", "unit",
      SessionType.internalChoice
        [("Coordinator", "LookForGame", "unit",
          SessionType.externalChoice "Coordinator"
            [("GameFound", "unit",
              SessionType.tRec "GameRound"
                (SessionType.externalChoice "GameServer"
                  [("TurnStart", "unit",
                    SessionType.internalChoice
                      [("GameServer", "TakeAction", "unit",
                        SessionType.tVar "GameRound")]),
                  ("YouWon", "unit",
                    SessionType.tEnd),
                  ("YouLost", "unit",
                    SessionType.tEnd)]))])])]

-- `Coordinator` is recursion-free: certified by the generic `NoRec` lemmas
-- (`GameServer` and `Player` use recursion and are covered separately).
/-- `The witness` is recursion-free. -/
theorem Coordinator_norec : Coordinator.NoRec := no_rec_bool_true (by decide)
/-- Deep adequacy of `Coordinator` with empty seen set. -/
theorem Coordinator_deep : Prunable [] Coordinator :=
  norec_deep Coordinator_norec []
/-- Monitorability of `Coordinator` (finite prune closure). -/
theorem Coordinator_mon : Drainability.Monitorable Coordinator :=
  norec_monitorable Coordinator_norec


-- Mirror defs for `Player` (ungrafted; loop keeps the var)
/-- Internal choice: `(GameServer, TakeAction, unit)` looping on `GameRound` (`Player` mirror). -/
def PTA : SessionType :=
  SessionType.internalChoice
    [("GameServer", "TakeAction", "unit", SessionType.tVar "GameRound")]
/-- External offer by `GameServer`: `(TurnStart, unit)` continuing as `PTA`; `(YouWon, unit)`
   ending in `tEnd`; `(YouLost, unit)` ending in `tEnd` (`Player` mirror). -/
def PBody : SessionType :=
  SessionType.externalChoice "GameServer"
    [("TurnStart", "unit", PTA),
     ("YouWon", "unit", SessionType.tEnd),
     ("YouLost", "unit", SessionType.tEnd)]
/-- Recursive type: loop on `GameRound` with body `PBody` (`Player` mirror). -/
def PRec := SessionType.tRec "GameRound" PBody
/-- External offer by `Coordinator`: `(GameFound, unit)` continuing as `PRec` (`Player` mirror). -/
def PG : SessionType :=
  SessionType.externalChoice "Coordinator" [("GameFound", "unit", PRec)]
/-- Internal choice: `(Coordinator, LookForGame, unit)` continuing as `PG` (`Player` mirror). -/
def PL : SessionType :=
  SessionType.internalChoice [("Coordinator", "LookForGame", "unit", PG)]
-- Grafted side (loop points at the rec)
/-- Internal choice: `(GameServer, TakeAction, unit)` continuing as `PRec` (`Player` mirror). -/
def PTAS : SessionType :=
  SessionType.internalChoice [("GameServer", "TakeAction", "unit", PRec)]
/-- External offer by `GameServer`: `(TurnStart, unit)` continuing as `PTAS`; `(YouWon, unit)`
   ending in `tEnd`; `(YouLost, unit)` ending in `tEnd` (`Player` mirror). -/
def PSub : SessionType :=
  SessionType.externalChoice "GameServer"
    [("TurnStart", "unit", PTAS),
     ("YouWon", "unit", SessionType.tEnd),
     ("YouLost", "unit", SessionType.tEnd)]

/-- Grafting equation: substituting `PRec` for `GameRound` in `PBody` yields `PSub`. -/
theorem PSub_subst :
    substSessionType PBody "GameRound" PRec = PSub := rfl

-- `Has`-false facts (all by decide)
/-- The prune `Has` check for (`GameServer`, `TurnStart`, `unit`) on `PTAS` is `false` (absent
   from the type). -/
theorem P_has_TAS_Turn_false :
    pruneFirstInputDeepHas "GameServer" "TurnStart" "unit" PTAS = false := by decide
/-- The prune `Has` check for (`GameServer`, `YouWon`, `unit`) on `PTAS` is `false` (absent from
   the type). -/
theorem P_has_TAS_Won_false :
    pruneFirstInputDeepHas "GameServer" "YouWon" "unit" PTAS = false := by decide
/-- The prune `Has` check for (`GameServer`, `YouLost`, `unit`) on `PTAS` is `false` (absent
   from the type). -/
theorem P_has_TAS_Lost_false :
    pruneFirstInputDeepHas "GameServer" "YouLost" "unit" PTAS = false := by decide

-- FA facts about the grafted body (3 branches each)
/-- One-message prunability of `PSub` for (`GameServer`, `TurnStart`, `unit`). -/
theorem FA_PSub_Turn : PrunableOneMsg "GameServer" "TurnStart" "unit" PSub := by
  apply prunable_one_msg_extC_of_step "GameServer" _ "GameServer" "TurnStart" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [P_has_TAS_Turn_false] at hHas
      cases hHas
    · exact prunable_one_msg_end _ _ _
    · exact prunable_one_msg_end _ _ _
/-- One-message prunability of `PSub` for (`GameServer`, `YouWon`, `unit`). -/
theorem FA_PSub_Won : PrunableOneMsg "GameServer" "YouWon" "unit" PSub := by
  apply prunable_one_msg_extC_of_step "GameServer" _ "GameServer" "YouWon" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [P_has_TAS_Won_false] at hHas
      cases hHas
    · exact prunable_one_msg_end _ _ _
    · exact prunable_one_msg_end _ _ _
/-- One-message prunability of `PSub` for (`GameServer`, `YouLost`, `unit`). -/
theorem FA_PSub_Lost : PrunableOneMsg "GameServer" "YouLost" "unit" PSub := by
  apply prunable_one_msg_extC_of_step "GameServer" _ "GameServer" "YouLost" "unit"
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [P_has_TAS_Lost_false] at hHas
      cases hHas
    · exact prunable_one_msg_end _ _ _
    · exact prunable_one_msg_end _ _ _

-- Lift to the rec + owner-head Init
/-- One-message prunability of `PRec` for (`GameServer`, `TurnStart`, `unit`). -/
theorem FA_PRec_Turn : PrunableOneMsg "GameServer" "TurnStart" "unit" PRec :=
  prunable_one_msg_trec_of_succ "GameServer" "TurnStart" "unit" FA_PSub_Turn
/-- One-message prunability of `PRec` for (`GameServer`, `YouWon`, `unit`). -/
theorem FA_PRec_Won : PrunableOneMsg "GameServer" "YouWon" "unit" PRec :=
  prunable_one_msg_trec_of_succ "GameServer" "YouWon" "unit" FA_PSub_Won
/-- One-message prunability of `PRec` for (`GameServer`, `YouLost`, `unit`). -/
theorem FA_PRec_Lost : PrunableOneMsg "GameServer" "YouLost" "unit" PRec :=
  prunable_one_msg_trec_of_succ "GameServer" "YouLost" "unit" FA_PSub_Lost
/-- One-message prunability of `Player` for (`Coordinator`, `Init`, `unit`). -/
theorem FA_P_Init : PrunableOneMsg "Coordinator" "Init" "unit" Player :=
  prunable_one_msg_extC_owner "Coordinator" _ "Init" "unit"

/-- One-message prunability fact. -/
theorem hfaPRec : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PRec pm lab0 S0 → PrunableOneMsg pm lab0 S0 PRec := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | extC_here hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact FA_PRec_Turn
      · exact FA_PRec_Won
      · exact FA_PRec_Lost
    | extC_step hne hmem hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
          cases hsub3
      · cases hsub2
      · cases hsub2

-- Style-B hfa facts (hexp ignored; Has threaded down)
/-- One-message prunability fact. -/
theorem hfaPG : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PG pm lab0 S0 → PrunableOneMsg pm lab0 S0 PG := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "Coordinator" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact hfaPRec _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaPL : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PL pm lab0 S0 → PrunableOneMsg pm lab0 S0 PL := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact hfaPG _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaPlayer : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom Player pm lab0 S0 → PrunableOneMsg pm lab0 S0 Player := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact FA_P_Init
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "Coordinator" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' hHas =>
      obtain ⟨l, s, U⟩ := x
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      exact hfaPL _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaPTAS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PTAS pm lab0 S0 → PrunableOneMsg pm lab0 S0 PTAS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact hfaPRec _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaPBodyS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom PSub pm lab0 S0 → PrunableOneMsg pm lab0 S0 PSub := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "GameServer" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact hfaPTAS _ _ _ (has_to_exposed _ _ _ _ hHas)
    · exact prunable_one_msg_end _ _ _
    · exact prunable_one_msg_end _ _ _

/-- Deep adequacy of `Player` with empty seen set. -/
theorem Player_deep : Prunable [] Player := by
  apply Prunable.extC [] "Coordinator" _ _ hfaPlayer
  intro x hmem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  obtain ⟨rfl, rfl, rfl⟩ := hmem
  apply Prunable.intC [] _ _ hfaPL
  intro y hmemY
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemY
  apply Prunable.extC [] "Coordinator" _ _ hfaPG
  intro z hmemZ
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemZ
  obtain ⟨rfl, rfl, rfl⟩ := hmemZ
  apply Prunable.trec_new [] "GameRound" PBody _ _ hfaPRec
  · simp
  · have hSub : substSessionType PBody "GameRound"
        (SessionType.tRec "GameRound" PBody) = PSub := PSub_subst
    rw [hSub]
    apply Prunable.extC [PRec] "GameServer" _ _ hfaPBodyS
    intro w hmemW
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemW
    rcases hmemW with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · apply Prunable.intC [PRec] _ _ hfaPTAS
      intro v hmemV
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemV
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemV
      exact Prunable.trec_seen [PRec] "GameRound" PBody
        (List.mem_cons.mpr (Or.inl rfl)) hfaPRec
    · exact Prunable.tEnd [PRec]
    · exact Prunable.tEnd [PRec]

/-- Monitorability of `Player` (finite prune closure). -/
theorem Player_mon : Drainability.Monitorable Player := by
  apply Monitorable_of_closed_set Player
    {Player, PL, PG, PRec, PSub, PTAS,
     SessionType.tEnd, SessionType.tVar "GameRound"}
  · simp
  · intro U hU V hStep
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        show PL ∈ ({Player, PL, PG, PRec, PSub, PTAS,
          SessionType.tEnd, SessionType.tVar "GameRound"} : Finset SessionType)
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        show PG ∈ ({Player, PL, PG, PRec, PSub, PTAS,
          SessionType.tEnd, SessionType.tVar "GameRound"} : Finset SessionType)
        simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        show PRec ∈ ({Player, PL, PG, PRec, PSub, PTAS,
          SessionType.tEnd, SessionType.tVar "GameRound"} : Finset SessionType)
        simp
    · cases hStep with
      | trec =>
        show PSub ∈ ({Player, PL, PG, PRec, PSub, PTAS,
          SessionType.tEnd, SessionType.tVar "GameRound"} : Finset SessionType)
        simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · simp
        · simp
        · simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep
    · cases hStep


-- Mirror defs for `GameServer` (ungrafted; loop keeps the var)
/-- Internal choice: `(Coordinator, GameOver, unit)` ending in `tEnd` (`GameServer` mirror). -/
def GSOver : SessionType :=
  SessionType.internalChoice
    [("Coordinator", "GameOver", "unit", SessionType.tEnd)]
/-- Internal choice: `(Player_2, YouLost, unit)` continuing as `GSOver` (`GameServer` mirror). -/
def GWin : SessionType :=
  SessionType.internalChoice [("Player_2", "YouLost", "unit", GSOver)]
/-- Internal choice: `(Player_2, YouWon, unit)` continuing as `GSOver` (`GameServer` mirror). -/
def GLose : SessionType :=
  SessionType.internalChoice [("Player_2", "YouWon", "unit", GSOver)]
/-- External offer by `Player_2`: `(TakeAction, unit)` looping on `GameRound` (`GameServer`
   mirror). -/
def GTA2 : SessionType :=
  SessionType.externalChoice "Player_2"
    [("TakeAction", "unit", SessionType.tVar "GameRound")]
/-- Internal choice: `(Player_2, TurnStart, unit)` continuing as `GTA2` (`GameServer` mirror). -/
def GT2 : SessionType :=
  SessionType.internalChoice [("Player_2", "TurnStart", "unit", GTA2)]
/-- External offer by `Player_1`: `(TakeAction, unit)` continuing as `GT2` (`GameServer`
   mirror). -/
def GTA1 : SessionType :=
  SessionType.externalChoice "Player_1" [("TakeAction", "unit", GT2)]
/-- Internal choice: `(Player_1, TurnStart, unit)` continuing as `GTA1`; `(Player_1, YouWon,
   unit)` continuing as `GWin`; `(Player_1, YouLost, unit)` continuing as `GLose` (`GameServer`
   mirror). -/
def GBody : SessionType :=
  SessionType.internalChoice
    [("Player_1", "TurnStart", "unit", GTA1),
     ("Player_1", "YouWon", "unit", GWin),
     ("Player_1", "YouLost", "unit", GLose)]
/-- Recursive type: loop on `GameRound` with body `GBody` (`GameServer` mirror). -/
def GRec := SessionType.tRec "GameRound" GBody
-- Grafted side (loop points at the rec)
/-- External offer by `Player_2`: `(TakeAction, unit)` continuing as `GRec` (`GameServer`
   mirror). -/
def GTAS : SessionType :=
  SessionType.externalChoice "Player_2" [("TakeAction", "unit", GRec)]
/-- Internal choice: `(Player_2, TurnStart, unit)` continuing as `GTAS` (`GameServer` mirror). -/
def GT2S : SessionType :=
  SessionType.internalChoice [("Player_2", "TurnStart", "unit", GTAS)]
/-- External offer by `Player_1`: `(TakeAction, unit)` continuing as `GT2S` (`GameServer`
   mirror). -/
def GTA1S : SessionType :=
  SessionType.externalChoice "Player_1" [("TakeAction", "unit", GT2S)]
/-- Internal choice: `(Player_1, TurnStart, unit)` continuing as `GTA1S`; `(Player_1, YouWon,
   unit)` continuing as `GWin`; `(Player_1, YouLost, unit)` continuing as `GLose` (`GameServer`
   mirror). -/
def GSub : SessionType :=
  SessionType.internalChoice
    [("Player_1", "TurnStart", "unit", GTA1S),
     ("Player_1", "YouWon", "unit", GWin),
     ("Player_1", "YouLost", "unit", GLose)]

/-- Grafting equation: substituting `GRec` for `GameRound` in `GBody` yields `GSub`. -/
theorem GSub_subst :
    substSessionType GBody "GameRound" GRec = GSub := rfl

-- `Has`-false facts (all by decide)
/-- The prune `Has` check for (`Player_1`, `TakeAction`, `unit`) on `GT2S` is `false` (absent
   from the type). -/
theorem G_has_T2S_TakeA_false :
    pruneFirstInputDeepHas "Player_1" "TakeAction" "unit" GT2S = false := by decide
/-- The prune `Has` check for (`Player_2`, `TakeAction`, `unit`) on `GTA1S` is `false` (absent
   from the type). -/
theorem G_has_TA1S_TakeB_false :
    pruneFirstInputDeepHas "Player_2" "TakeAction" "unit" GTA1S = false := by decide
/-- The prune `Has` check for (`Player_1`, `TakeAction`, `unit`) on `GWin` is `false` (absent
   from the type). -/
theorem G_has_Win_TakeA_false :
    pruneFirstInputDeepHas "Player_1" "TakeAction" "unit" GWin = false := by decide
/-- The prune `Has` check for (`Player_1`, `TakeAction`, `unit`) on `GLose` is `false` (absent
   from the type). -/
theorem G_has_Lose_TakeA_false :
    pruneFirstInputDeepHas "Player_1" "TakeAction" "unit" GLose = false := by decide
/-- The prune `Has` check for (`Player_2`, `TakeAction`, `unit`) on `GWin` is `false` (absent
   from the type). -/
theorem G_has_Win_TakeB_false :
    pruneFirstInputDeepHas "Player_2" "TakeAction" "unit" GWin = false := by decide
/-- The prune `Has` check for (`Player_2`, `TakeAction`, `unit`) on `GLose` is `false` (absent
   from the type). -/
theorem G_has_Lose_TakeB_false :
    pruneFirstInputDeepHas "Player_2" "TakeAction" "unit" GLose = false := by decide

-- FA facts about the grafted body
/-- One-message prunability of `GSub` for (`Player_1`, `TakeAction`, `unit`). -/
theorem FA_GSub_TakeA : PrunableOneMsg "Player_1" "TakeAction" "unit" GSub := by
  apply prunable_one_msg_intC_of_step _ "Player_1" "TakeAction" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · show PrunableOneMsg "Player_1" "TakeAction" "unit" GTA1S
      apply prunable_one_msg_extC_of_step "Player_1" _ "Player_1" "TakeAction" "unit"
      intro W hS2
      cases hS2 with
      | @extCQ _ _ y _ hmem2 hHas2 =>
        obtain ⟨l2, s2, U2⟩ := y
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
        obtain ⟨rfl, rfl, rfl⟩ := hmem2
        show PrunableOneMsg "Player_1" "TakeAction" "unit" GT2S
        apply prunable_one_msg_intC_of_step _ "Player_1" "TakeAction" "unit"
        intro Z hS3
        cases hS3 with
        | @intC _ z hmem3 hHas3 =>
          obtain ⟨r3, l3, s3, U3⟩ := z
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem3
          have hHas3r : pruneFirstInputDeepHas "Player_1" "TakeAction" "unit" GT2S = true := hHas3
          rw [G_has_T2S_TakeA_false] at hHas3r
          cases hHas3r
    · rw [G_has_Win_TakeA_false] at hHas
      cases hHas
    · rw [G_has_Lose_TakeA_false] at hHas
      cases hHas

/-- One-message prunability of `GSub` for (`Player_2`, `TakeAction`, `unit`). -/
theorem FA_GSub_TakeB : PrunableOneMsg "Player_2" "TakeAction" "unit" GSub := by
  apply prunable_one_msg_intC_of_step _ "Player_2" "TakeAction" "unit"
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · rw [G_has_TA1S_TakeB_false] at hHas
      cases hHas
    · rw [G_has_Win_TakeB_false] at hHas
      cases hHas
    · rw [G_has_Lose_TakeB_false] at hHas
      cases hHas

-- Lift to the rec + owner-head GameFound
/-- One-message prunability of `GRec` for (`Player_1`, `TakeAction`, `unit`). -/
theorem FA_GRec_TakeA : PrunableOneMsg "Player_1" "TakeAction" "unit" GRec :=
  prunable_one_msg_trec_of_succ "Player_1" "TakeAction" "unit" FA_GSub_TakeA
/-- One-message prunability of `GRec` for (`Player_2`, `TakeAction`, `unit`). -/
theorem FA_GRec_TakeB : PrunableOneMsg "Player_2" "TakeAction" "unit" GRec :=
  prunable_one_msg_trec_of_succ "Player_2" "TakeAction" "unit" FA_GSub_TakeB
/-- One-message prunability of `GameServer` for (`Coordinator`, `GameFound`, `unit`). -/
theorem FA_G_Found : PrunableOneMsg "Coordinator" "GameFound" "unit" GameServer :=
  prunable_one_msg_extC_owner "Coordinator" _ "GameFound" "unit"

/-- One-message prunability fact. -/
theorem hfaGRec : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GRec pm lab0 S0 → PrunableOneMsg pm lab0 S0 GRec := by
  intro pm lab0 S0 hexp
  cases hexp with
  | trec hsub =>
    cases hsub with
    | intC_step hmem hne hsub2 =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · cases hsub2 with
        | extC_here hmem2 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          exact FA_GRec_TakeA
        | extC_step hne2 hmem2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl⟩ := hmem2
          cases hsub3 with
          | intC_step hmem3 hne3 hsub4 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem3
            cases hsub4 with
            | extC_here hmem4 =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
              obtain ⟨rfl, rfl, rfl⟩ := hmem4
              exact FA_GRec_TakeB
            | extC_step hne4 hmem4 hsub5 =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem4
              obtain ⟨rfl, rfl, rfl⟩ := hmem4
              cases hsub5
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
          cases hsub3 with
          | intC_step hmem3 hne3 hsub4 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem3
            cases hsub4
      · cases hsub2 with
        | intC_step hmem2 hne2 hsub3 =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem2
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem2
          cases hsub3 with
          | intC_step hmem3 hne3 hsub4 =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem3
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem3
            cases hsub4

-- Style-B hfa facts (hexp ignored; Has threaded down)
/-- One-message prunability fact. -/
theorem hfaGSOver : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GSOver pm lab0 S0 → PrunableOneMsg pm lab0 S0 GSOver := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact prunable_one_msg_end _ _ _
/-- One-message prunability fact. -/
theorem hfaGWin : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GWin pm lab0 S0 → PrunableOneMsg pm lab0 S0 GWin := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    have hHasr : pruneFirstInputDeepHas pm lab0 S0 GSOver = true := hHas
    exact hfaGSOver _ _ _ (has_to_exposed _ _ _ _ hHasr)
/-- One-message prunability fact. -/
theorem hfaGLose : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GLose pm lab0 S0 → PrunableOneMsg pm lab0 S0 GLose := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact hfaGSOver _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaGTAS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GTAS pm lab0 S0 → PrunableOneMsg pm lab0 S0 GTAS := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "Player_2" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact hfaGRec _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaGT2S : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GT2S pm lab0 S0 → PrunableOneMsg pm lab0 S0 GT2S := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
    exact hfaGTAS _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaGTA1S : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GTA1S pm lab0 S0 → PrunableOneMsg pm lab0 S0 GTA1S := by
  intro pm lab0 S0 _
  apply prunable_one_msg_extC_of_step "Player_1" _ pm lab0 S0
  intro V hS
  cases hS with
  | @extCQ _ _ x _ hmem hHas =>
    obtain ⟨l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact hfaGT2S _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaGSub : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GSub pm lab0 S0 → PrunableOneMsg pm lab0 S0 GSub := by
  intro pm lab0 S0 _
  apply prunable_one_msg_intC_of_step _ pm lab0 S0
  intro V hS
  cases hS with
  | @intC _ x hmem hHas =>
    obtain ⟨r, l, s, U⟩ := x
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact hfaGTA1S _ _ _ (has_to_exposed _ _ _ _ hHas)
    · exact hfaGWin _ _ _ (has_to_exposed _ _ _ _ hHas)
    · exact hfaGLose _ _ _ (has_to_exposed _ _ _ _ hHas)
/-- One-message prunability fact. -/
theorem hfaGS : ∀ (pm : Role) (lab0 : Lab) (S0 : DataSort),
    ExposedFrom GameServer pm lab0 S0 → PrunableOneMsg pm lab0 S0 GameServer := by
  intro pm lab0 S0 hexp
  cases hexp with
  | extC_here hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    exact FA_G_Found
  | extC_step hne hmem hsub =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    obtain ⟨rfl, rfl, rfl⟩ := hmem
    apply prunable_one_msg_extC_of_step "Coordinator" _ pm lab0 S0
    intro V hS
    cases hS with
    | @extCQ _ _ x _ hmem' hHas =>
      obtain ⟨l, s, U⟩ := x
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem'
      obtain ⟨rfl, rfl, rfl⟩ := hmem'
      have hE : ExposedFrom GRec pm lab0 S0 := has_to_exposed _ _ _ _ hHas
      exact hfaGRec _ _ _ hE

/-- Deep adequacy of `GameServer` with empty seen set. -/
theorem GameServer_deep : Prunable [] GameServer := by
  apply Prunable.extC [] "Coordinator" _ _ hfaGS
  intro x hmem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  obtain ⟨rfl, rfl, rfl⟩ := hmem
  apply Prunable.trec_new [] "GameRound" GBody _ _ hfaGRec
  · simp
  · have hSub : substSessionType GBody "GameRound"
        (SessionType.tRec "GameRound" GBody) = GSub := GSub_subst
    rw [hSub]
    apply Prunable.intC [GRec] _ _ hfaGSub
    intro y hmemY
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemY
    rcases hmemY with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · apply Prunable.extC [GRec] "Player_1" _ _ hfaGTA1S
      intro z hmemZ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemZ
      obtain ⟨rfl, rfl, rfl⟩ := hmemZ
      apply Prunable.intC [GRec] _ _ hfaGT2S
      intro w hmemW
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemW
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemW
      apply Prunable.extC [GRec] "Player_2" _ _ hfaGTAS
      intro v hmemV
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemV
      obtain ⟨rfl, rfl, rfl⟩ := hmemV
      exact Prunable.trec_seen [GRec] "GameRound" GBody
        (List.mem_cons.mpr (Or.inl rfl)) hfaGRec
    · apply Prunable.intC [GRec] _ _ hfaGWin
      intro z hmemZ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemZ
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemZ
      apply Prunable.intC [GRec] _ _ hfaGSOver
      intro w hmemW
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemW
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemW
      exact Prunable.tEnd [GRec]
    · apply Prunable.intC [GRec] _ _ hfaGLose
      intro z hmemZ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemZ
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemZ
      apply Prunable.intC [GRec] _ _ hfaGSOver
      intro w hmemW
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemW
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hmemW
      exact Prunable.tEnd [GRec]

/-- Monitorability of `GameServer` (finite prune closure). -/
theorem GameServer_mon : Drainability.Monitorable GameServer := by
  apply Monitorable_of_closed_set GameServer
    {GameServer, GRec, GSub, GTA1S, GT2S, GTAS, GWin, GLose, GSOver,
     SessionType.tEnd, SessionType.tVar "GameRound"}
  · simp
  · intro U hU V hStep
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        show GRec ∈ ({GameServer, GRec, GSub, GTA1S, GT2S, GTAS, GWin, GLose,
          GSOver, SessionType.tEnd, SessionType.tVar "GameRound"} : Finset SessionType)
        simp
    · cases hStep with
      | trec =>
        show GSub ∈ ({GameServer, GRec, GSub, GTA1S, GT2S, GTAS, GWin, GLose,
          GSOver, SessionType.tEnd, SessionType.tVar "GameRound"} : Finset SessionType)
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · simp
        · simp
        · simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | extC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep with
      | intC hmem =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hmem
        simp
    · cases hStep
    · cases hStep

/-- Empty-queue network for the four game roles. -/
def Net : Network :=
  [("Coordinator", (Coordinator, [])),
   ("GameServer", (GameServer, [])),
   ("Player_1", (Player, [])),
   ("Player_2", (Player, []))]

/-- `Net` is well-formed: distinct roles, well-formed types, vacuous sender-closure. -/
theorem Net_wellFormed : Net.WellFormed := by
  refine ⟨by decide, ?_, Network.SenderClosed_of_all_nil (by decide)⟩
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Coordinator.wfCheck_sound (by decide)
  · exact GameServer.wfCheck_sound (by decide)
  · exact Player.wfCheck_sound (by decide)
  · exact Player.wfCheck_sound (by decide)

/-- `Net` has no self-mention: each role is absent from its own type. -/
theorem Net_noSelf : Net.NoSelf := by
  apply Network.NoSelf_of_rolesOf
  intro x hx
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

/-- `Net` contains every role occurring in its member types. -/
theorem Net_rolesPresent : Net.RolesPresent := by
  intro q T Q s hmem hOcc
  have hmemR : s ∈ rolesOf T := occurs_mem hOcc
  simp only [Net, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [Coordinator, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    have hs : s = "Player_1" ∨ s = "Player_2" ∨ s = "GameServer" := by tauto
    rcases hs with rfl | rfl | rfl
    · exact ⟨(Player, []), by decide⟩
    · exact ⟨(Player, []), by decide⟩
    · exact ⟨(GameServer, []), by decide⟩
  · simp only [GameServer, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    have hs : s = "Coordinator" ∨ s = "Player_1" ∨ s = "Player_2" := by tauto
    rcases hs with rfl | rfl | rfl
    · exact ⟨(Coordinator, []), by decide⟩
    · exact ⟨(Player, []), by decide⟩
    · exact ⟨(Player, []), by decide⟩
  · simp only [Player, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    have hs : s = "Coordinator" ∨ s = "GameServer" := by tauto
    rcases hs with rfl | rfl
    · exact ⟨(Coordinator, []), by decide⟩
    · exact ⟨(GameServer, []), by decide⟩
  · simp only [Player, rolesOf, rolesOf.goInt, rolesOf.goExt,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmemR
    have hs : s = "Coordinator" ∨ s = "GameServer" := by tauto
    rcases hs with rfl | rfl
    · exact ⟨(Coordinator, []), by decide⟩
    · exact ⟨(GameServer, []), by decide⟩

/-- `Net` admits a consistent coinductive instrumentation (empty queues fold trivially). -/
theorem Net_consistent : ∃ MN, consistentInstrumentation_co Net = some MN :=
  exists_consistentInstrumentation_co_of_all_nil Net (by decide)


-- ============ Coordinator intermediates (ungrafted, linear) ============
/-- After `Init` to `Player_1`: sends `Init` to `Player_2` then continues. -/
def C1 : SessionType :=
  SessionType.internalChoice
    [("Player_2", "Init", "unit",
      SessionType.externalChoice "Player_1"
        [("LookForGame", "unit",
          SessionType.externalChoice "Player_2"
            [("LookForGame", "unit",
              SessionType.internalChoice
                [("Player_1", "GameFound", "unit",
                  SessionType.internalChoice
                    [("Player_2", "GameFound", "unit",
                      SessionType.internalChoice
                        [("GameServer", "GameFound", "unit",
                          SessionType.externalChoice "GameServer"
                            [("GameOver", "unit",
                              SessionType.tEnd)])])])])])])]
/-- After `Init` to `Player_2`: waits for `LookForGame` from `Player_1`. -/
def C2 : SessionType :=
  SessionType.externalChoice "Player_1"
    [("LookForGame", "unit",
      SessionType.externalChoice "Player_2"
        [("LookForGame", "unit",
          SessionType.internalChoice
            [("Player_1", "GameFound", "unit",
              SessionType.internalChoice
                [("Player_2", "GameFound", "unit",
                  SessionType.internalChoice
                    [("GameServer", "GameFound", "unit",
                      SessionType.externalChoice "GameServer"
                        [("GameOver", "unit",
                          SessionType.tEnd)])])])])])]
/-- Waits for `LookForGame` from `Player_2`. -/
def C3 : SessionType :=
  SessionType.externalChoice "Player_2"
    [("LookForGame", "unit",
      SessionType.internalChoice
        [("Player_1", "GameFound", "unit",
          SessionType.internalChoice
            [("Player_2", "GameFound", "unit",
              SessionType.internalChoice
                [("GameServer", "GameFound", "unit",
                  SessionType.externalChoice "GameServer"
                    [("GameOver", "unit",
                      SessionType.tEnd)])])])])]
/-- Sends `GameFound` to `Player_1`. -/
def C4 : SessionType :=
  SessionType.internalChoice
    [("Player_1", "GameFound", "unit",
      SessionType.internalChoice
        [("Player_2", "GameFound", "unit",
          SessionType.internalChoice
            [("GameServer", "GameFound", "unit",
              SessionType.externalChoice "GameServer"
                [("GameOver", "unit",
                  SessionType.tEnd)])])])]
/-- Sends `GameFound` to `Player_2`. -/
def C5 : SessionType :=
  SessionType.internalChoice
    [("Player_2", "GameFound", "unit",
      SessionType.internalChoice
        [("GameServer", "GameFound", "unit",
          SessionType.externalChoice "GameServer"
            [("GameOver", "unit",
              SessionType.tEnd)])])]
/-- Sends `GameFound` to `GameServer`. -/
def C6 : SessionType :=
  SessionType.internalChoice
    [("GameServer", "GameFound", "unit",
      SessionType.externalChoice "GameServer"
        [("GameOver", "unit",
          SessionType.tEnd)])]
/-- Waits for `GameOver` from `GameServer`. -/
def C7 : SessionType :=
  SessionType.externalChoice "GameServer"
    [("GameOver", "unit", SessionType.tEnd)]

-- ============ Messages (sender, label, sort) ============
/-- `Init` from `Coordinator` (queued at players). -/
abbrev mInit : QueueMessage := QueueMessage.msg "Coordinator" "Init" "unit"
/-- `LookForGame` from `Player_1` (queued at coordinator). -/
abbrev mLook1 : QueueMessage := QueueMessage.msg "Player_1" "LookForGame" "unit"
/-- `LookForGame` from `Player_2` (queued at coordinator). -/
abbrev mLook2 : QueueMessage := QueueMessage.msg "Player_2" "LookForGame" "unit"
/-- `GameFound` from `Coordinator` (queued at players and game server). -/
abbrev mFound : QueueMessage := QueueMessage.msg "Coordinator" "GameFound" "unit"
/-- `TurnStart` from `GameServer` (queued at players). -/
abbrev mTurn : QueueMessage := QueueMessage.msg "GameServer" "TurnStart" "unit"
/-- `TakeAction` from `Player_1` (queued at game server). -/
abbrev mTake1 : QueueMessage := QueueMessage.msg "Player_1" "TakeAction" "unit"
/-- `TakeAction` from `Player_2` (queued at game server). -/
abbrev mTake2 : QueueMessage := QueueMessage.msg "Player_2" "TakeAction" "unit"
/-- `YouWon` from `GameServer` (queued at players). -/
abbrev mWon : QueueMessage := QueueMessage.msg "GameServer" "YouWon" "unit"
/-- `YouLost` from `GameServer` (queued at players). -/
abbrev mLost : QueueMessage := QueueMessage.msg "GameServer" "YouLost" "unit"
/-- `GameOver` from `GameServer` (queued at coordinator). -/
abbrev mOver : QueueMessage := QueueMessage.msg "GameServer" "GameOver" "unit"

-- ============ OUT-step characterizations ============

-- Uniform tRec-aware step characterizations for every session type
-- occurring in reachable Game network entries (generated).
theorem C1_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans C1 (st_label.out p lab S) T' →
    (p = "Player_2" ∧ lab = "Init" ∧ S = "unit" ∧ T' = C2) := by
  intro h
  unfold C1 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem C1_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans C1 (st_label.inp p lab S) T') : False := by
  unfold C1 at h
  cases h

theorem C2_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans C2 (st_label.out p lab S) T') : False := by
  unfold C2 at h
  cases h

theorem C2_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans C2 (st_label.inp p lab S) T' →
    (p = "Player_1" ∧ lab = "LookForGame" ∧ S = "unit" ∧ T' = C3) := by
  intro h
  unfold C2 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem C3_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans C3 (st_label.out p lab S) T') : False := by
  unfold C3 at h
  cases h

theorem C3_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans C3 (st_label.inp p lab S) T' →
    (p = "Player_2" ∧ lab = "LookForGame" ∧ S = "unit" ∧ T' = C4) := by
  intro h
  unfold C3 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem C4_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans C4 (st_label.out p lab S) T' →
    (p = "Player_1" ∧ lab = "GameFound" ∧ S = "unit" ∧ T' = C5) := by
  intro h
  unfold C4 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem C4_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans C4 (st_label.inp p lab S) T') : False := by
  unfold C4 at h
  cases h

theorem C5_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans C5 (st_label.out p lab S) T' →
    (p = "Player_2" ∧ lab = "GameFound" ∧ S = "unit" ∧ T' = C6) := by
  intro h
  unfold C5 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem C5_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans C5 (st_label.inp p lab S) T') : False := by
  unfold C5 at h
  cases h

theorem C6_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans C6 (st_label.out p lab S) T' →
    (p = "GameServer" ∧ lab = "GameFound" ∧ S = "unit" ∧ T' = C7) := by
  intro h
  unfold C6 at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem C6_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans C6 (st_label.inp p lab S) T') : False := by
  unfold C6 at h
  cases h

theorem C7_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans C7 (st_label.out p lab S) T') : False := by
  unfold C7 at h
  cases h

theorem C7_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans C7 (st_label.inp p lab S) T' →
    (p = "GameServer" ∧ lab = "GameOver" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold C7 at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem Coordinator_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans Coordinator (st_label.out p lab S) T' →
    (p = "Player_1" ∧ lab = "Init" ∧ S = "unit" ∧ T' = C1) := by
  intro h
  unfold Coordinator at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem Coordinator_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans Coordinator (st_label.inp p lab S) T') : False := by
  unfold Coordinator at h
  cases h

theorem GLose_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans GLose (st_label.out p lab S) T' →
    (p = "Player_2" ∧ lab = "YouWon" ∧ S = "unit" ∧ T' = GSOver) := by
  intro h
  unfold GLose at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem GLose_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans GLose (st_label.inp p lab S) T') : False := by
  unfold GLose at h
  cases h

theorem GRec_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans GRec (st_label.out p lab S) T' →
    (p = "Player_1" ∧ lab = "TurnStart" ∧ S = "unit" ∧ T' = GTA1S) ∨
    (p = "Player_1" ∧ lab = "YouWon" ∧ S = "unit" ∧ T' = GWin) ∨
    (p = "Player_1" ∧ lab = "YouLost" ∧ S = "unit" ∧ T' = GLose) := by
  intro h
  unfold GRec at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans GSub (st_label.out p lab S) T' := hsub
    unfold GSub at h2
    cases h2 with
    | intC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      · exact Or.inr (Or.inr (⟨rfl, rfl, rfl, rfl⟩))

theorem GRec_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans GRec (st_label.inp p lab S) T') : False := by
  unfold GRec at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans GSub (st_label.inp p lab S) T' := hsub
    unfold GSub at h2
    cases h2

theorem GSOver_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans GSOver (st_label.out p lab S) T' →
    (p = "Coordinator" ∧ lab = "GameOver" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold GSOver at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem GSOver_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans GSOver (st_label.inp p lab S) T') : False := by
  unfold GSOver at h
  cases h

theorem GT2S_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans GT2S (st_label.out p lab S) T' →
    (p = "Player_2" ∧ lab = "TurnStart" ∧ S = "unit" ∧ T' = GTAS) := by
  intro h
  unfold GT2S at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem GT2S_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans GT2S (st_label.inp p lab S) T') : False := by
  unfold GT2S at h
  cases h

theorem GTA1S_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans GTA1S (st_label.out p lab S) T') : False := by
  unfold GTA1S at h
  cases h

theorem GTA1S_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans GTA1S (st_label.inp p lab S) T' →
    (p = "Player_1" ∧ lab = "TakeAction" ∧ S = "unit" ∧ T' = GT2S) := by
  intro h
  unfold GTA1S at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem GTAS_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans GTAS (st_label.out p lab S) T') : False := by
  unfold GTAS at h
  cases h

theorem GTAS_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans GTAS (st_label.inp p lab S) T' →
    (p = "Player_2" ∧ lab = "TakeAction" ∧ S = "unit" ∧ T' = GRec) := by
  intro h
  unfold GTAS at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem GWin_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans GWin (st_label.out p lab S) T' →
    (p = "Player_2" ∧ lab = "YouLost" ∧ S = "unit" ∧ T' = GSOver) := by
  intro h
  unfold GWin at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem GWin_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans GWin (st_label.inp p lab S) T') : False := by
  unfold GWin at h
  cases h

theorem GameServer_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans GameServer (st_label.out p lab S) T') : False := by
  unfold GameServer at h
  cases h

theorem GameServer_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans GameServer (st_label.inp p lab S) T' →
    (p = "Coordinator" ∧ lab = "GameFound" ∧ S = "unit" ∧ T' = GRec) := by
  intro h
  unfold GameServer at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem PG_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans PG (st_label.out p lab S) T') : False := by
  unfold PG at h
  cases h

theorem PG_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PG (st_label.inp p lab S) T' →
    (p = "Coordinator" ∧ lab = "GameFound" ∧ S = "unit" ∧ T' = PRec) := by
  intro h
  unfold PG at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem PL_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PL (st_label.out p lab S) T' →
    (p = "Coordinator" ∧ lab = "LookForGame" ∧ S = "unit" ∧ T' = PG) := by
  intro h
  unfold PL at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem PL_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans PL (st_label.inp p lab S) T') : False := by
  unfold PL at h
  cases h

theorem PRec_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans PRec (st_label.out p lab S) T') : False := by
  unfold PRec at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PSub (st_label.out p lab S) T' := hsub
    unfold PSub at h2
    cases h2

theorem PRec_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PRec (st_label.inp p lab S) T' →
    (p = "GameServer" ∧ lab = "TurnStart" ∧ S = "unit" ∧ T' = PTAS) ∨
    (p = "GameServer" ∧ lab = "YouWon" ∧ S = "unit" ∧ T' = SessionType.tEnd) ∨
    (p = "GameServer" ∧ lab = "YouLost" ∧ S = "unit" ∧ T' = SessionType.tEnd) := by
  intro h
  unfold PRec at h
  cases h with
  | tRec hsub =>
    have h2 : st_trans PSub (st_label.inp p lab S) T' := hsub
    unfold PSub at h2
    cases h2 with
    | extC hmem =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      · exact Or.inr (Or.inr (⟨rfl, rfl, rfl, rfl⟩))

theorem PTAS_out_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans PTAS (st_label.out p lab S) T' →
    (p = "GameServer" ∧ lab = "TakeAction" ∧ S = "unit" ∧ T' = PRec) := by
  intro h
  unfold PTAS at h
  cases h with
  | intC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem PTAS_no_inp {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans PTAS (st_label.inp p lab S) T') : False := by
  unfold PTAS at h
  cases h

theorem Player_no_out {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans Player (st_label.out p lab S) T') : False := by
  unfold Player at h
  cases h

theorem Player_inp_iff {p : Role} {lab : Lab} {S : DataSort} {T' : SessionType} :
    st_trans Player (st_label.inp p lab S) T' →
    (p = "Coordinator" ∧ lab = "Init" ∧ S = "unit" ∧ T' = PL) := by
  intro h
  unfold Player at h
  cases h with
  | extC hmem =>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩

theorem tEnd_no_out_game {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.out p lab S) T') : False := by
  cases h

theorem tEnd_no_inp_game {p lab : Role} {S : DataSort} {T' : SessionType}
    (h : st_trans SessionType.tEnd (st_label.inp p lab S) T') : False := by
  cases h

-- Canonical representatives (role-sorted) of the 338 ordered
-- states, one per `Network.Reordered` class (109 classes).
def CS_0 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))]
def CS_1 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_2 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_3 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_4 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_5 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_6 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_7 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_8 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_9 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_10 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_11 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_12 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_13 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_14 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_15 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_16 : Network := [("Coordinator", (SessionType.tEnd, [])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_17 : Network := [("Coordinator", (C6, [])), ("GameServer", (GameServer, [])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))]
def CS_18 : Network := [("Coordinator", (C6, [])), ("GameServer", (GameServer, [])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_19 : Network := [("Coordinator", (C6, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PRec, []))]
def CS_20 : Network := [("Coordinator", (C6, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_21 : Network := [("Coordinator", (C4, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PG, []))]
def CS_22 : Network := [("Coordinator", (Coordinator, [])), ("GameServer", (GameServer, [])), ("Player_1", (Player, [])), ("Player_2", (Player, []))]
def CS_23 : Network := [("Coordinator", (C5, [])), ("GameServer", (GameServer, [])), ("Player_1", (PRec, [])), ("Player_2", (PG, []))]
def CS_24 : Network := [("Coordinator", (C5, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PG, []))]
def CS_25 : Network := [("Coordinator", (C1, [QueueMessage.msg "Player_1" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (Player, []))]
def CS_26 : Network := [("Coordinator", (C1, [])), ("GameServer", (GameServer, [])), ("Player_1", (PL, [])), ("Player_2", (Player, []))]
def CS_27 : Network := [("Coordinator", (C1, [])), ("GameServer", (GameServer, [])), ("Player_1", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"])), ("Player_2", (Player, []))]
def CS_28 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))]
def CS_29 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_30 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_31 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_32 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_33 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_34 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_35 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_36 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_37 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_38 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_39 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_40 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_41 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_42 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_43 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_44 : Network := [("Coordinator", (C7, [QueueMessage.msg "GameServer" "GameOver" "unit"])), ("GameServer", (SessionType.tEnd, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_45 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (SessionType.tEnd, []))]
def CS_46 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_47 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_48 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_49 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_50 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_51 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_52 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_53 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_54 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_55 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_56 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_57 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_58 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"]))]
def CS_59 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (SessionType.tEnd, []))]
def CS_60 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_61 : Network := [("Coordinator", (C7, [])), ("GameServer", (GSOver, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"]))]
def CS_62 : Network := [("Coordinator", (C7, [])), ("GameServer", (GT2S, [])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))]
def CS_63 : Network := [("Coordinator", (C7, [])), ("GameServer", (GT2S, [])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_64 : Network := [("Coordinator", (C7, [])), ("GameServer", (GWin, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, []))]
def CS_65 : Network := [("Coordinator", (C7, [])), ("GameServer", (GWin, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_66 : Network := [("Coordinator", (C7, [])), ("GameServer", (GWin, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, []))]
def CS_67 : Network := [("Coordinator", (C7, [])), ("GameServer", (GWin, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_68 : Network := [("Coordinator", (C7, [])), ("GameServer", (GWin, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PRec, []))]
def CS_69 : Network := [("Coordinator", (C7, [])), ("GameServer", (GWin, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouWon" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_70 : Network := [("Coordinator", (C7, [])), ("GameServer", (GLose, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PRec, []))]
def CS_71 : Network := [("Coordinator", (C7, [])), ("GameServer", (GLose, [])), ("Player_1", (SessionType.tEnd, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_72 : Network := [("Coordinator", (C7, [])), ("GameServer", (GLose, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, []))]
def CS_73 : Network := [("Coordinator", (C7, [])), ("GameServer", (GLose, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_74 : Network := [("Coordinator", (C7, [])), ("GameServer", (GLose, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PRec, []))]
def CS_75 : Network := [("Coordinator", (C7, [])), ("GameServer", (GLose, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "YouLost" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_76 : Network := [("Coordinator", (C7, [])), ("GameServer", (GRec, [])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))]
def CS_77 : Network := [("Coordinator", (C7, [])), ("GameServer", (GRec, [])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_78 : Network := [("Coordinator", (C7, [])), ("GameServer", (GRec, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PRec, []))]
def CS_79 : Network := [("Coordinator", (C7, [])), ("GameServer", (GRec, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_80 : Network := [("Coordinator", (C7, [])), ("GameServer", (GameServer, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))]
def CS_81 : Network := [("Coordinator", (C7, [])), ("GameServer", (GameServer, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_82 : Network := [("Coordinator", (C7, [])), ("GameServer", (GameServer, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PRec, []))]
def CS_83 : Network := [("Coordinator", (C7, [])), ("GameServer", (GameServer, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_84 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTA1S, [QueueMessage.msg "Player_1" "TakeAction" "unit"])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))]
def CS_85 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTA1S, [QueueMessage.msg "Player_1" "TakeAction" "unit"])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_86 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_1", (PTAS, [])), ("Player_2", (PRec, []))]
def CS_87 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_1", (PTAS, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_88 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("Player_2", (PRec, []))]
def CS_89 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_1", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_90 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("Player_2", (PRec, []))]
def CS_91 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTA1S, [])), ("Player_1", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "TurnStart" "unit"])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit"]))]
def CS_92 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTAS, [QueueMessage.msg "Player_2" "TakeAction" "unit"])), ("Player_1", (PRec, [])), ("Player_2", (PRec, []))]
def CS_93 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTAS, [])), ("Player_1", (PRec, [])), ("Player_2", (PTAS, []))]
def CS_94 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTAS, [])), ("Player_1", (PRec, [])), ("Player_2", (PRec, [QueueMessage.msg "GameServer" "TurnStart" "unit"]))]
def CS_95 : Network := [("Coordinator", (C7, [])), ("GameServer", (GTAS, [])), ("Player_1", (PRec, [])), ("Player_2", (PG, [QueueMessage.msg "Coordinator" "GameFound" "unit", QueueMessage.msg "GameServer" "TurnStart" "unit"]))]
def CS_96 : Network := [("Coordinator", (C2, [QueueMessage.msg "Player_1" "LookForGame" "unit", QueueMessage.msg "Player_2" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PG, []))]
def CS_97 : Network := [("Coordinator", (C2, [QueueMessage.msg "Player_1" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PL, []))]
def CS_98 : Network := [("Coordinator", (C2, [QueueMessage.msg "Player_1" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"]))]
def CS_99 : Network := [("Coordinator", (C2, [QueueMessage.msg "Player_2" "LookForGame" "unit", QueueMessage.msg "Player_1" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PG, []))]
def CS_100 : Network := [("Coordinator", (C2, [QueueMessage.msg "Player_2" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PL, [])), ("Player_2", (PG, []))]
def CS_101 : Network := [("Coordinator", (C2, [QueueMessage.msg "Player_2" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"])), ("Player_2", (PG, []))]
def CS_102 : Network := [("Coordinator", (C2, [])), ("GameServer", (GameServer, [])), ("Player_1", (PL, [])), ("Player_2", (PL, []))]
def CS_103 : Network := [("Coordinator", (C2, [])), ("GameServer", (GameServer, [])), ("Player_1", (PL, [])), ("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"]))]
def CS_104 : Network := [("Coordinator", (C2, [])), ("GameServer", (GameServer, [])), ("Player_1", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"])), ("Player_2", (PL, []))]
def CS_105 : Network := [("Coordinator", (C2, [])), ("GameServer", (GameServer, [])), ("Player_1", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"])), ("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"]))]
def CS_106 : Network := [("Coordinator", (C3, [QueueMessage.msg "Player_2" "LookForGame" "unit"])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PG, []))]
def CS_107 : Network := [("Coordinator", (C3, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (PL, []))]
def CS_108 : Network := [("Coordinator", (C3, [])), ("GameServer", (GameServer, [])), ("Player_1", (PG, [])), ("Player_2", (Player, [QueueMessage.msg "Coordinator" "Init" "unit"]))]

def Cs : List Network := [CS_0, CS_1, CS_2, CS_3, CS_4, CS_5, CS_6, CS_7, CS_8, CS_9, CS_10, CS_11, CS_12, CS_13, CS_14, CS_15, CS_16, CS_17, CS_18, CS_19, CS_20, CS_21, CS_22, CS_23, CS_24, CS_25, CS_26, CS_27, CS_28, CS_29, CS_30, CS_31, CS_32, CS_33, CS_34, CS_35, CS_36, CS_37, CS_38, CS_39, CS_40, CS_41, CS_42, CS_43, CS_44, CS_45, CS_46, CS_47, CS_48, CS_49, CS_50, CS_51, CS_52, CS_53, CS_54, CS_55, CS_56, CS_57, CS_58, CS_59, CS_60, CS_61, CS_62, CS_63, CS_64, CS_65, CS_66, CS_67, CS_68, CS_69, CS_70, CS_71, CS_72, CS_73, CS_74, CS_75, CS_76, CS_77, CS_78, CS_79, CS_80, CS_81, CS_82, CS_83, CS_84, CS_85, CS_86, CS_87, CS_88, CS_89, CS_90, CS_91, CS_92, CS_93, CS_94, CS_95, CS_96, CS_97, CS_98, CS_99, CS_100, CS_101, CS_102, CS_103, CS_104, CS_105, CS_106, CS_107, CS_108]

theorem gameHbase : ∃ C ∈ Cs, Network.Reordered Net C := by
  exact ⟨CS_22, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm Net CS_22 from by decide)⟩

theorem CS_0_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_0 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_0, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_0, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_1_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_1 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_1, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_0, by unfold Cs; exact List.mem_cons.mpr (Or.inl rfl), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_1, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_2_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_2 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_2, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_0, by unfold Cs; exact List.mem_cons.mpr (Or.inl rfl), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_2, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_3_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_3 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_3, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_1, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_3, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_4_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_4 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_4, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_2, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_4, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_5_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_5 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_5, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_0, by unfold Cs; exact List.mem_cons.mpr (Or.inl rfl), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_5, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_6_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_6 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_6, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_2, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_5, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_6, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_7_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_7 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_7, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_4, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_6, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_7, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_8_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_8 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_8, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_0, by unfold Cs; exact List.mem_cons.mpr (Or.inl rfl), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_8, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_9_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_9 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_9, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_1, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_8, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_9, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_10_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_10 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_10, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_3, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_9, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_10, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_11_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_11 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_11, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_5, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_11, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_12_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_12 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_12, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_6, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_11, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_12, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_13_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_13 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_13, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_7, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_12, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_13, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_14_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_14 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_14, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_8, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_14, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_15_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_15 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_15, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_9, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_14, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_15, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_16_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_16 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_16, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_10, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_15, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_16, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_17_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_17 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_17, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_17, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_80, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_18_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_18 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_18, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_17, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_18, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_81, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_19_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_19 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_19, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_17, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_19, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_82, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_20_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_20 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_20, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_18, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_19, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_20, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_83, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C6_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_21_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_21 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_21, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_21, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C4_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C4_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_24, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C4_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_22_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_22 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_22, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_22, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := Coordinator_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := Coordinator_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_27, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := Coordinator_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_23_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_23 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_23, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_23, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C5_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C5_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C5_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_18, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_24_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_24 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_24, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_23, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_24, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C5_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C5_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C5_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_20, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_25_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_25 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_25, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        exact absurd hST (fun h => C1_no_inp h)
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_25, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_98, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_26_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_26 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_26, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_26, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_103, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_25, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_27_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_27 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_27, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := Player_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_26, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_27, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := C1_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_105, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_28_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_28 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_28, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_0, by unfold Cs; exact List.mem_cons.mpr (Or.inl rfl), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_28, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_29_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_29 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_29, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_1, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_28, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_29, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_30_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_30 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_30, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_2, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_28, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_30, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_31_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_31 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_31, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_3, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_29, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_31, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_32_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_32 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_32, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_4, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_30, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_32, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_33_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_33 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_33, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_5, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_28, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_33, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_34_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_34 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_34, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_6, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_30, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_33, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_34, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_35_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_35 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_35, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_7, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_32, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_34, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_35, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_36_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_36 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_36, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_8, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_28, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_36, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_37_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_37 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_37, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_9, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_29, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_36, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_37, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_38_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_38 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_38, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_10, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_31, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_37, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_38, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_39_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_39 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_39, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_11, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_33, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_39, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_40_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_40 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_40, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_12, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_34, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_39, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_40, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_41_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_41 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_41, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_13, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_35, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_40, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_41, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_42_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_42 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_42, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_14, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_36, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_42, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_43_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_43 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_43, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_15, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_37, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_42, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_43, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_44_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_44 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_44, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C7_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_16, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_38, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_43, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_44, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_45_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_45 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_45, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_45, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_28, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_46_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_46 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_46, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_45, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_46, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_29, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_47_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_47 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_47, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_45, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_47, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_30, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_48_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_48 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_48, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_46, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_48, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_31, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_49_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_49 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_49, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_47, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_49, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_32, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_50_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_50 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_50, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_45, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_50, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_33, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_51_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_51 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_51, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_47, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_50, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_51, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_34, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_52_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_52 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_52, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_49, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_51, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_52, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_35, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_53_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_53 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_53, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_45, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_53, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_36, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_54_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_54 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_54, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_46, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_53, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_54, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_37, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_55_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_55 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_55, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_48, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_54, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_55, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_38, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_56_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_56 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_56, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_50, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_56, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_39, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_57_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_57 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_57, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_51, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_56, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_57, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_40, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_58_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_58 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_58, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_52, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_57, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_58, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_41, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_59_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_59 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_59, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_53, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_59, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_42, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_60_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_60 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_60, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_54, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_59, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_60, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_43, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_61_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_61 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_61, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_55, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_60, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_61, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_44, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GSOver_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_62_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_62 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_62, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_62, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GT2S_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GT2S_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GT2S_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_94, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_63_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_63 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_63, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_62, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_63, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GT2S_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GT2S_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GT2S_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_95, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_64_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_64 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_64, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_64, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_46, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_65_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_65 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_65, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_64, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_65, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_48, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_66_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_66 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_66, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_64, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_66, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_54, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_67_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_67 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_67, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ; exact ⟨CS_65, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_66, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_67, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_55, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_68_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_68 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_68, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_66, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_68, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_60, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_69_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_69 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_69, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_67, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_68, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_69, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GWin_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_61, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_70_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_70 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_70, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_70, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_47, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_71_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_71 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_71, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_70, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_71, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_49, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => tEnd_no_out_game h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_72_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_72 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_72, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_70, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_72, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_51, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_73_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_73 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_73, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ
        · cases hQ
        · cases hQ; exact ⟨CS_71, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_72, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_73, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_52, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_74_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_74 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_74, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_72, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_74, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_57, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_75_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_75 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_75, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_73, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_74, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_75, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GLose_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_58, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_76_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_76 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_76, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_76, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact ⟨CS_88, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
          · exact ⟨CS_66, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
          · exact ⟨CS_72, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_77_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_77 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_77, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_76, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_77, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact ⟨CS_89, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
          · exact ⟨CS_67, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
          · exact ⟨CS_73, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_78_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_78 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_78, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_76, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_78, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact ⟨CS_90, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
          · exact ⟨CS_68, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
          · exact ⟨CS_74, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_79_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_79 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_79, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_77, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_78, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_79, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact ⟨CS_91, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
          · exact ⟨CS_69, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
          · exact ⟨CS_75, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := GRec_out_iff hST
          rcases ho with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
          · exact absurd h1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_80_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_80 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_80, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := GameServer_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_76, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_80, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_81_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_81 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_81, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := GameServer_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_77, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_80, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_81, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_82_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_82 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_82, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := GameServer_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_78, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_80, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_82, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_83_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_83 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_83, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := GameServer_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_79, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_81, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_82, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_83, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_84_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_84 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_84, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := GTA1S_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_62, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_84, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_85_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_85 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_85, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := GTA1S_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_63, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_84, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_85, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_86_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_86 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_86, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_86, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_84, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_87_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_87 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_87, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_86, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_87, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_85, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_88_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_88 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_88, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ; exact ⟨CS_86, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_88, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_89_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_89 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_89, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ; exact ⟨CS_87, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
        · cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_88, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_89, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_90_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_90 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_90, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_88, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_90, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_91_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_91 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_91, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_89, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_90, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_91, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTA1S_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_92_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_92 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_92, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := GTAS_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_76, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_92, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_93_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_93 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_93, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_93, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_92, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PTAS_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_94_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_94 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_94, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PRec_inp_iff hST
        rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · cases hQ; exact ⟨CS_93, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
        · cases hQ
        · cases hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_94, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_95_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_95 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_95, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := PG_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_94, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_95, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C7_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GTAS_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PRec_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_96_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_96 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_96, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_106, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_96, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_97_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_97 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_97, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_107, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_97, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_96, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_98_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_98 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_98, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_108, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := Player_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_97, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_98, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_99_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_99 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_99, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_106, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_99, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_100_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_100 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_100, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_100, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_99, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_101_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_101 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_101, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C2_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := Player_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_100, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_101, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_102_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_102 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_102, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_102, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_97, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_100, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_103_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_103 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_103, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := Player_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_102, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_103, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_98, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_104_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_104 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_104, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := Player_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_102, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_104, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_101, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_105_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_105 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_105, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := Player_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_103, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := Player_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_104, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_105, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C2_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_106_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_106 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_106, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := C3_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_21, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_106, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_107_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_107 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_107, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_107, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          obtain ⟨-, rfl, rfl, rfl⟩ := ho
          exact ⟨CS_106, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST =>
        cases h_recv with
        | recv =>
          have ho := PL_out_iff hST
          exact absurd ho.1 (by decide)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem CS_108_step : ∀ (δ : net_label) (N' : Network),
    net_trans CS_108 δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro δ N' hTr hInt
  cases hTr with
  | io_send h hmem => simp [is_internal_net_label] at hInt
  | io_recv h hmem => simp [is_internal_net_label] at hInt
  | dequeue hSQ hmem =>
    simp only [CS_108, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        simp [Queue.dequeue, Queue.dequeue.go] at hQ
    · cases hSQ with
      | dequeue hST hQ =>
        have hi := Player_inp_iff hST
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hi
        cases hQ
        exact ⟨CS_107, by unfold Cs; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (show List.Perm _ _ from by decide)⟩
  | comm hne h_send h_recv hmem_p hmem_q =>
    simp only [CS_108, List.mem_cons, List.mem_nil_iff, or_false] at hmem_p hmem_q
    rcases hmem_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hmem_q with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => C3_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => GameServer_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne
    · cases h_send with
      | send hST => exact absurd hST (fun h => PG_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd hST (fun h => Player_no_out h)
    · cases h_send with
      | send hST => exact absurd rfl hne

theorem gameHstep : ∀ C ∈ Cs, ∀ (δ : net_label) (N' : Network),
    net_trans C δ N' → is_internal_net_label δ →
    ∃ C' ∈ Cs, Network.Reordered N' C' := by
  intro C hC δ N' hTr hInt
  simp only [Cs, List.mem_cons, List.mem_nil_iff, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CS_0_step _ _ hTr hInt
  · exact CS_1_step _ _ hTr hInt
  · exact CS_2_step _ _ hTr hInt
  · exact CS_3_step _ _ hTr hInt
  · exact CS_4_step _ _ hTr hInt
  · exact CS_5_step _ _ hTr hInt
  · exact CS_6_step _ _ hTr hInt
  · exact CS_7_step _ _ hTr hInt
  · exact CS_8_step _ _ hTr hInt
  · exact CS_9_step _ _ hTr hInt
  · exact CS_10_step _ _ hTr hInt
  · exact CS_11_step _ _ hTr hInt
  · exact CS_12_step _ _ hTr hInt
  · exact CS_13_step _ _ hTr hInt
  · exact CS_14_step _ _ hTr hInt
  · exact CS_15_step _ _ hTr hInt
  · exact CS_16_step _ _ hTr hInt
  · exact CS_17_step _ _ hTr hInt
  · exact CS_18_step _ _ hTr hInt
  · exact CS_19_step _ _ hTr hInt
  · exact CS_20_step _ _ hTr hInt
  · exact CS_21_step _ _ hTr hInt
  · exact CS_22_step _ _ hTr hInt
  · exact CS_23_step _ _ hTr hInt
  · exact CS_24_step _ _ hTr hInt
  · exact CS_25_step _ _ hTr hInt
  · exact CS_26_step _ _ hTr hInt
  · exact CS_27_step _ _ hTr hInt
  · exact CS_28_step _ _ hTr hInt
  · exact CS_29_step _ _ hTr hInt
  · exact CS_30_step _ _ hTr hInt
  · exact CS_31_step _ _ hTr hInt
  · exact CS_32_step _ _ hTr hInt
  · exact CS_33_step _ _ hTr hInt
  · exact CS_34_step _ _ hTr hInt
  · exact CS_35_step _ _ hTr hInt
  · exact CS_36_step _ _ hTr hInt
  · exact CS_37_step _ _ hTr hInt
  · exact CS_38_step _ _ hTr hInt
  · exact CS_39_step _ _ hTr hInt
  · exact CS_40_step _ _ hTr hInt
  · exact CS_41_step _ _ hTr hInt
  · exact CS_42_step _ _ hTr hInt
  · exact CS_43_step _ _ hTr hInt
  · exact CS_44_step _ _ hTr hInt
  · exact CS_45_step _ _ hTr hInt
  · exact CS_46_step _ _ hTr hInt
  · exact CS_47_step _ _ hTr hInt
  · exact CS_48_step _ _ hTr hInt
  · exact CS_49_step _ _ hTr hInt
  · exact CS_50_step _ _ hTr hInt
  · exact CS_51_step _ _ hTr hInt
  · exact CS_52_step _ _ hTr hInt
  · exact CS_53_step _ _ hTr hInt
  · exact CS_54_step _ _ hTr hInt
  · exact CS_55_step _ _ hTr hInt
  · exact CS_56_step _ _ hTr hInt
  · exact CS_57_step _ _ hTr hInt
  · exact CS_58_step _ _ hTr hInt
  · exact CS_59_step _ _ hTr hInt
  · exact CS_60_step _ _ hTr hInt
  · exact CS_61_step _ _ hTr hInt
  · exact CS_62_step _ _ hTr hInt
  · exact CS_63_step _ _ hTr hInt
  · exact CS_64_step _ _ hTr hInt
  · exact CS_65_step _ _ hTr hInt
  · exact CS_66_step _ _ hTr hInt
  · exact CS_67_step _ _ hTr hInt
  · exact CS_68_step _ _ hTr hInt
  · exact CS_69_step _ _ hTr hInt
  · exact CS_70_step _ _ hTr hInt
  · exact CS_71_step _ _ hTr hInt
  · exact CS_72_step _ _ hTr hInt
  · exact CS_73_step _ _ hTr hInt
  · exact CS_74_step _ _ hTr hInt
  · exact CS_75_step _ _ hTr hInt
  · exact CS_76_step _ _ hTr hInt
  · exact CS_77_step _ _ hTr hInt
  · exact CS_78_step _ _ hTr hInt
  · exact CS_79_step _ _ hTr hInt
  · exact CS_80_step _ _ hTr hInt
  · exact CS_81_step _ _ hTr hInt
  · exact CS_82_step _ _ hTr hInt
  · exact CS_83_step _ _ hTr hInt
  · exact CS_84_step _ _ hTr hInt
  · exact CS_85_step _ _ hTr hInt
  · exact CS_86_step _ _ hTr hInt
  · exact CS_87_step _ _ hTr hInt
  · exact CS_88_step _ _ hTr hInt
  · exact CS_89_step _ _ hTr hInt
  · exact CS_90_step _ _ hTr hInt
  · exact CS_91_step _ _ hTr hInt
  · exact CS_92_step _ _ hTr hInt
  · exact CS_93_step _ _ hTr hInt
  · exact CS_94_step _ _ hTr hInt
  · exact CS_95_step _ _ hTr hInt
  · exact CS_96_step _ _ hTr hInt
  · exact CS_97_step _ _ hTr hInt
  · exact CS_98_step _ _ hTr hInt
  · exact CS_99_step _ _ hTr hInt
  · exact CS_100_step _ _ hTr hInt
  · exact CS_101_step _ _ hTr hInt
  · exact CS_102_step _ _ hTr hInt
  · exact CS_103_step _ _ hTr hInt
  · exact CS_104_step _ _ hTr hInt
  · exact CS_105_step _ _ hTr hInt
  · exact CS_106_step _ _ hTr hInt
  · exact CS_107_step _ _ hTr hInt
  · exact CS_108_step _ _ hTr hInt

theorem gameCover (N' : Network) (hStar : net_trans_star Net N') :
    ∃ C ∈ Cs, Network.Reordered N' C :=
  canon_cover_of_star gameHbase gameHstep N' hStar

end Game
