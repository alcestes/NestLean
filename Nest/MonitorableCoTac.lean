import Nest.MonitorableCoFin

open Cslib
open Cslib.LTS
open Lean Elab Tactic Meta

  syntax "fmon_close" : tactic
macro_rules
  | `(tactic| fmon_close) => `(tactic|(
    first
    | rfl
    | exact List.mem_cons_self
    | exact List.mem_cons_of_mem _ List.mem_cons_self
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
    ))

/-- Rename to fresh plain Name (for mkIdent in evalTactic). -/
def renameFresh (fvarId : FVarId) (base : Name) : TacticM Name := do
  let mvarId ← getMainGoal
  let fresh ← mkFreshUserName base
  let mvarId' ← mvarId.withContext (mvarId.rename fvarId fresh)
  replaceMainGoal [mvarId']
  pure fresh

/-- simpa-using into new hyp; return it. -/
def simpaNormalizeSubst (h : FVarId) : TacticM FVarId := do
  let mvarId ← getMainGoal
  let before : LocalContext ← mvarId.withContext (pure (← getLCtx))
  let hn ← renameFresh h `hsub
  evalTactic (← `(tactic| have hnorm := by simpa only [substSessionType, go_int_eq_map, go_ext_eq_map, List.map_cons, List.map_nil] using $(mkIdent hn)))
  let mvarId1 ← getMainGoal
  let hnorm ← mvarId1.withContext (do
    let after ← getLCtx
    let mut found : Option FVarId := none
    for decl in after do
      if decl.isImplementationDetail then continue
      if (before.find? decl.fvarId).isNone then
        found := some decl.fvarId
    match found with
    | some f => pure f
    | none => throwError "no hnorm")
  let hn2 ← renameFresh hnorm `hnorm
  evalTactic (← `(tactic| have hnorm2 := by simpa using $(mkIdent hn2)))
  let mvarId2 ← getMainGoal
  mvarId2.withContext do
    let after2 ← getLCtx
    let mut found : Option FVarId := none
    for decl in after2 do
      if decl.isImplementationDetail then continue
      if (before.find? decl.fvarId).isNone && decl.fvarId != hnorm then
        found := some decl.fvarId
    match found with
    | some f => pure f
    | none => throwError "no normalized hyp"

/-- Extract List literal elements; none if not a literal. -/
partial def asListLit : Expr → MetaM (Option (List Expr)) := fun e => do
  let e ← whnf e
  match e with
  | .app (.const ``List.nil _) _ => pure (some [])
  | .app (.app (.app (.const ``List.cons _) _) h) t => do
    match ← asListLit t with
    | some tl => pure (some (h :: tl))
    | none => pure none
  | _ => pure none

/-- Extract components of a nested Prod tuple. -/
partial def asTupleLit : Expr → MetaM (List Expr) := fun e => do
  let e ← whnf e
  match e with
  | .app (.app (.const ``Prod.mk _) a) b => do
    let rest ← asTupleLit b
    pure (a :: rest)
  | _ => pure [e]

/-- Extract (isInt, branches) from a concrete choice type. -/
def destructureChoice (V : Expr) : MetaM (Option (Bool × List Expr)) := do
  let V ← whnf V
  match V with
  | .app (.app (.const ``SessionType.internalChoice _) bs) _ => do
    match ← asListLit bs with
    | some l => pure (some (true, l))
    | none => pure none
  | .app (.app (.app (.const ``SessionType.externalChoice _) _) bs) _ => do
    match ← asListLit bs with
    | some l => pure (some (false, l))
    | none => pure none
  | _ => pure none

/-- Em-split on `Ex T0 g`; returns (posGoal, posHyp, negGoal, negHyp).
    Uses `MVarId.note` + `cases` (no syntax). -/
def emSplitEx (T0 g : Expr) : TacticM (MVarId × FVarId × MVarId × FVarId) := do
  let mvarId ← getMainGoal
  let exProp := mkApp (mkApp (mkConst ``Ex) T0) g
  let emProof := mkApp (mkConst ``Classical.em) exProp
  let emType := mkApp (mkApp (mkConst ``Or) exProp) (mkApp (mkConst ``Not) exProp)
  let nm ← mkFreshUserName `hem
  let (hem, mvarId1) ← mvarId.withContext (Lean.MVarId.note mvarId nm emProof (some emType))
  let subgoals ← mvarId1.withContext (mvarId1.cases hem)
  match subgoals.toList with
  | [sgPos, sgNeg] =>
    -- determine which is pos (has Ex hyp) vs neg; assume order? Check by type.
    -- Or.inl is first? For Or, inl comes first. Assume sgPos=inl (Ex), sgNeg=inr (¬Ex).
    -- Verify by finding hyp types.
    let hPos ← sgPos.mvarId.withContext (do
      let lctx ← getLCtx
      let mut found : Option FVarId := none
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let ty ← whnf (← inferType decl.toExpr)
        if ty.getAppFn.constName? == some ``Ex then
          found := some decl.fvarId
          break
      match found with
      | some f => pure f
      | none => throwError "no Ex hyp")
    let hNeg ← sgNeg.mvarId.withContext (do
      let lctx ← getLCtx
      let mut found : Option FVarId := none
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let ty ← whnf (← inferType decl.toExpr)
        if ty.getAppFn.constName? == some ``Not then
          found := some decl.fvarId
          break
      match found with
      | some f => pure f
      | none => throwError "no ¬Ex hyp")
    pure (sgPos.mvarId, hPos, sgNeg.mvarId, hNeg)
  | _ => throwError "em did not split in two"

mutual
/-- Unfold loop helper (in mutual block for recursion). -/
partial def fmonStepLoop (depth : Nat) : TacticM Unit := do
  if depth = 0 then throwError "unfold depth exceeded"
  else
    let mvarId2 ← getMainGoal
    let (h1, hrest, hsub) ← mvarId2.withContext (do
      let lctx ← getLCtx
      let mut h1O : Option FVarId := none
      let mut hrestO : Option FVarId := none
      let mut hsubO : Option FVarId := none
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let ty ← whnf (← inferType decl.toExpr)
        match ty.getAppFn.constName? with
        | some ``Unfold1 => h1O := some decl.fvarId
        | some ``UnfoldStar => hrestO := some decl.fvarId
        | some ``fmon => hsubO := some decl.fvarId
        | _ => pure ()
      match h1O, hrestO, hsubO with
      | some a, some b, some c => pure (a, b, c)
      | _, _, _ => throwError "step loop: hyps not found")
    let mvarIdU ← getMainGoal
    let subU ← mvarIdU.withContext (mvarIdU.cases h1)
    if subU.size = 0 then pure ()  -- vacuous close (Unfold1 impossible)
    else
      for sgU in subU do
        setGoals [sgU.mvarId]
      let mvarIdN ← getMainGoal
      let hrest2 ← mvarIdN.withContext (do
        let lctx ← getLCtx
        let mut found : Option FVarId := none
        for decl in lctx do
          if decl.isImplementationDetail then continue
          let ty ← whnf (← inferType decl.toExpr)
          if ty.getAppFn.constName? == some ``UnfoldStar then
            found := some decl.fvarId
            break
        match found with
        | some f => pure f
        | none => throwError "no UnfoldStar hyp in loop")
      let mvarIdS ← getMainGoal
      let hsub2 ← mvarIdS.withContext (do
        let lctx ← getLCtx
        let mut found : Option FVarId := none
        for decl in lctx do
          if decl.isImplementationDetail then continue
          let ty ← whnf (← inferType decl.toExpr)
          if ty.getAppFn.constName? == some ``fmon then
            found := some decl.fvarId
            break
        match found with
        | some f => pure f
        | none => throwError "no fmon hyp in loop")
      let hrestN ← simpaNormalizeSubst hrest2
      let nm ← renameFresh hsub2 `hsub
      evalTactic (← `(tactic| revert $(mkIdent nm)))
      let mvarId3 ← getMainGoal
      let sub2 ← mvarId3.withContext (mvarId3.cases hrestN)
      for sg2 in sub2 do
        setGoals [sg2.mvarId]
        if sg2.ctorName == some ``UnfoldStar.refl then
          evalTactic (← `(tactic| intro _))
          let mvarId4 ← getMainGoal
          mvarId4.withContext do
            let lctx ← getLCtx
            let mut found : Option FVarId := none
            for decl in lctx do
              if decl.isImplementationDetail then continue
              let ty ← whnf (← inferType decl.toExpr)
              if ty.getAppFn.constName? == some ``fmon then
                found := some decl.fvarId
                break
            match found with
            | some hf => fmonInvMain hf
            | none => throwError "no fmon hyp in loop"
        else if sg2.ctorName == some ``UnfoldStar.step then
          evalTactic (← `(tactic| intro _ _))
          fmonStepLoop (depth - 1)
        else throwError "unhandled loop UnfoldStar"
      pure ()
/-- Main inversion driver. Extracts V from hfmon for pfx branch extraction. -/
partial def fmonInvMain (hf : FVarId) : TacticM Unit :=
  fmonInvMainAux hf true
/-- Aux with rec-skip flag (avoids loop on UnfoldStar.refl). -/
partial def fmonInvMainAux (hf : FVarId) (allowRec : Bool) : TacticM Unit := do
  let mvarId ← getMainGoal
  -- extract V (source type, arg 1) for pfx branch analysis
  let V ← mvarId.withContext (do
    let ty ← inferType (.fvar hf)
    let tyw ← whnf ty
    let args := tyw.getAppArgs
    -- fmon G V g W → V is args[1]
    if h : args.size > 1 then pure args[1]!
    else throwError "fmonInvMain: bad fmon type")
  let subgoals ← mvarId.withContext (mvarId.cases hf)
  for sg in subgoals do
    setGoals [sg.mvarId]
    if sg.ctorName == some ``fmon.fm_base then
      let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
      match fs.getLast? with
      | some hbase => fmonBaseTac hbase
      | none => throwError "fm_base without hyp"
    else if sg.ctorName == some ``fmon.fm_rec then
      if !allowRec then throwError "rec loop (refl): manual handling needed"
      else
        let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
        if fs.length < 3 then throwError "fm_rec fields"
        else fmonRecTac fs[fs.length - 3]! fs[fs.length - 2]! fs[fs.length - 1]!
    else if sg.ctorName == some ``fmon.fm_pfxInt then
      let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
      let got ← sg.mvarId.withContext (do
        let mut hallO : Option FVarId := none
        let mut hndO : Option FVarId := none
        let mut hcovO : Option FVarId := none
        let mut hkeyO : Option FVarId := none
        let mut hkeO : Option FVarId := none
        for f in fs do
          let ty ← inferType (.fvar f)
          let body := stripForalls ty
          if hasConstIn ty ``fchild then hallO := some f
          else if body.getAppFn.constName? == some ``List.Nodup then hndO := some f
          else if hasConstIn ty ``Ex then
            if hasConstIn body ``And then hkeyO := some f else hcovO := some f
          else if body.getAppFn.constName? == some ``Ne then
            -- hke (kept≠[]) has fvar (kept) + nil; hne (bs≠[]) concrete (no fvar); hneq (q≠p) fvar but no nil.
            if hasFVar body && hasConstIn body ``List.nil then hkeO := some f
            else pure ()
          else pure ()
        match hallO, hndO, hcovO, hkeyO, hkeO with
        | some a, some b, some c, some d, some e => pure (a, b, c, d, e)
        | _, _, _, _, _ => throwError "pfxInt: hyps not found by type")
      let (hallF, hndF, hcovF, hkeyF, hkeF) := got
      fmonPfxIntDisp V hallF hndF hkeyF hcovF hkeF
    else if sg.ctorName == some ``fmon.fm_pfxExt then
      let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
      -- find hall (mentions fchild), hnd (Nodup), hcov/hkey by position after filtering?
      -- For now, assume last 8 are the hyps (first 4 are kept,q,lab,S vars); take hall,hnd,hkey,hcov by type.
      let got ← sg.mvarId.withContext (do
        let mut hallO : Option FVarId := none
        let mut hndO : Option FVarId := none
        let mut hcovO : Option FVarId := none
        let mut hkeyO : Option FVarId := none
        let mut hkeO : Option FVarId := none
        for f in fs do
          let ty ← inferType (.fvar f)
          let body := stripForalls ty
          if hasConstIn ty ``fchild then hallO := some f
          else if body.getAppFn.constName? == some ``List.Nodup then hndO := some f
          else if hasConstIn ty ``Ex then
            if hasConstIn body ``And then hkeyO := some f else hcovO := some f
          else if body.getAppFn.constName? == some ``Ne then
            -- hke (kept≠[]) has fvar (kept) + nil; hneq (q≠p) fvar but no nil.
            if hasFVar body && hasConstIn body ``List.nil then hkeO := some f
            else pure ()
          else pure ()
        match hallO, hndO, hcovO, hkeyO, hkeO with
        | some a, some b, some c, some d, some e => pure (a, b, c, d, e)
        | _, _, _, _, _ => throwError "pfxExt: hyps not found (hall={hallO.isSome} hnd={hndO.isSome} hcov={hcovO.isSome} hkey={hkeyO.isSome} hke={hkeO.isSome})")
      let (hallF, hndF, hcovF, hkeyF, hkeF) := got
      fmonPfxExtDisp V hallF hndF hkeyF hcovF hkeF
    else throwError "unhandled fmon case"
  pure ()

/-- Base inversion. Fully closes or throws (no pfx here). -/
partial def fmonBaseTac (hbase : FVarId) : TacticM Unit := do
  let mvarId ← getMainGoal
  let subgoals ← mvarId.withContext (mvarId.cases hbase)
  for sg in subgoals do
    setGoals [sg.mvarId]
    if sg.ctorName == some ``mon_tr_yes_base.intC || sg.ctorName == some ``mon_tr_yes_base.extC then
      let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
      match fs.getLast? with
      | some hmem => fmonMemTac hmem
      | none => throwError "base without membership"
    else if sg.ctorName == some ``mon_tr_yes_base.tRec then
      let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
      match fs.getLast? with
      | some hsub =>
        let hsub2 ← simpaNormalizeSubst hsub
        fmonBaseTac hsub2
      | none => throwError "tRec without subderiv"
    else throwError "unhandled base case"
  pure ()

/-- Membership split: head→close, tail→recurse. Fully closes or throws. -/
partial def fmonMemTac (hmem : FVarId) : TacticM Unit := do
  let hmemName ← renameFresh hmem `hmem
  let hStx := mkIdent hmemName
  let mvarId ← getMainGoal
  let hmemcur ← mvarId.withContext (do
    let lctx ← getLCtx
    let some d := lctx.findFromUserName? hmemName | throwError "no hmem"
    pure d.fvarId)
  let subgoals ← mvarId.withContext (do
    try mvarId.cases hmemcur
    catch _ => do
      -- `cases` fails on concrete-mismatched Mem (impossible head):
      -- simplify membership to equalities and close.
      (try evalTactic (← `(tactic| simp at $hStx:ident)) catch _ => pure ())
      let gs ← getGoals
      if gs.isEmpty then pure #[]
      else do
        (try evalTactic (← `(tactic| contradiction)) catch _ => pure ())
        let gs2 ← getGoals
        if gs2.isEmpty then pure #[]
        else do
          (try evalTactic (← `(tactic|
            (subst_vars; fmon_close))) catch _ => pure ())
          let gs3 ← getGoals
          if gs3.isEmpty then pure #[]
          else do
            let mvarNew ← getMainGoal
            mvarNew.withContext do
              let lctx ← getLCtx
              let some d := lctx.findFromUserName? hmemName
                | throwError "no hmem after simp"
              mvarNew.cases d.fvarId)
  for sg in subgoals do
    setGoals [sg.mvarId]
    if sg.ctorName == some ``List.Mem.head then
      evalTactic (← `(tactic| fmon_close))
    else if sg.ctorName == some ``List.Mem.tail then
      let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
      match fs.getLast? with
      | some hmem2 => fmonMemTac hmem2
      | none => throwError "tail without membership"
    else throwError "unhandled Mem case"
  pure ()

/-- Check if Expr contains a const with given name (for hyp identification). -/
partial def hasConstIn : Expr → Name → Bool
  | .const n _, m => n == m
  | .app f a, m => hasConstIn f m || hasConstIn a m
  | .forallE _ d b _, m => hasConstIn d m || hasConstIn b m
  | .lam _ d b _, m => hasConstIn d m || hasConstIn b m
  | _, _ => false
/-- Check if Expr contains an fvar (for hyp identification). -/
partial def hasFVar : Expr → Bool
  | .fvar _ => true
  | .app f a => hasFVar f || hasFVar a
  | .forallE _ d b _ => hasFVar d || hasFVar b
  | .lam _ d b _ => hasFVar d || hasFVar b
  | .letE _ _ v b _ => hasFVar v || hasFVar b
  | .proj _ _ e => hasFVar e
  | .mdata _ e => hasFVar e
  | _ => false
/-- Check if Expr contains a bound variable (must skip: isDefEq panics). -/
partial def hasBVar : Expr → Bool
  | .bvar _ => true
  | .app f a => hasBVar f || hasBVar a
  | .forallE _ d b _ => hasBVar d || hasBVar b
  | .lam _ d b _ => hasBVar d || hasBVar b
  | .letE _ _ v b _ => hasBVar v || hasBVar b
  | .proj _ _ e => hasBVar e
  | .mdata _ e => hasBVar e
  | _ => false
/-- Strip foralls to get body. -/
partial def stripForalls : Expr → Expr
  | .forallE _ _ b _ => stripForalls b
  | e => e
partial def extractGamma (hcov : FVarId) : TacticM Expr := do
  let mvarId ← getMainGoal
  mvarId.withContext (do
    let ty ← inferType (.fvar hcov)
    -- traverse type to find Ex app; Ex has 2 args (T, γ), return arg 1
    let rec find : Expr → Option Expr
      | .app (.app (.const ``Ex _) _) gam => some gam
      | .app f a => match find f with | some g => some g | none => find a
      | .forallE _ d b _ => match find d with | some g => some g | none => find b
      | .lam _ d b _ => match find d with | some g => some g | none => find b
      | _ => none
    match find ty with
    | some g => pure g
    | none => throwError "extractGamma: no Ex found")
/-- Strip metadata wrappers (pretty-printer/elaborator annotations). -/
partial def unwrapMData : Expr → Expr
  | .mdata _ e => unwrapMData e
  | e => e

/-- Rough Expr size (node count) for guarding expensive steps. -/
partial def exprSize : Expr → Nat
  | .app f a => exprSize f + exprSize a + 1
  | .lam _ d b _ => exprSize d + exprSize b + 1
  | .forallE _ d b _ => exprSize d + exprSize b + 1
  | .letE _ _ v b _ => exprSize v + exprSize b + 1
  | .proj _ _ e => exprSize e + 1
  | .mdata _ e => exprSize e + 1
  | _ => 1

/-- Find a stuck `beq`/`Eq` in `e` with exactly one free-fvar side,
    skipping ones already decided in `lctx`. Returns the equality to split. -/
partial def findStuckEq (e : Expr) (lctx : LocalContext) :
    MetaM (Option (Expr × Expr)) := do
  -- skip if an identical (up to defeq) equation -- or its negation -- is assumed
  let alreadyDecided : Expr → Expr → MetaM Bool := fun a b => do
    if hasBVar a || hasBVar b then pure false
    else
      let mut decided := false
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let ty ← whnf (← inferType decl.toExpr)
        if hasBVar ty then pure ()
        else
          let isEqPair : Expr → Expr → MetaM Bool := fun a' b' => do
            if hasBVar a' || hasBVar b' then pure false
            else pure (((← isDefEq a' a) && (← isDefEq b' b)) ||
              ((← isDefEq a' b) && (← isDefEq b' a)))
          match ty with
          | .app (.app (.const ``Eq _) a') b' =>
            if ← isEqPair a' b' then decided := true
          | .app (.app (.app (.const ``Ne _) _) a') b' =>
            if ← isEqPair a' b' then decided := true
          | .app (.const ``Not _) (.app (.app (.const ``Eq _) a') b') =>
            if ← isEqPair a' b' then decided := true
          | .forallE _ (.app (.app (.const ``Eq _) a') b')
              (.const ``False _) _ =>
            if ← isEqPair a' b' then decided := true
          | _ => pure ()
      pure decided
  -- strip metadata wrappers (pretty-printer/elaborator annotations)
  -- collect candidate equalities (exactly one side a local free fvar,
  -- neither side mentions bound variables; use last two app args to skip
  -- implicit type/instance arguments)
  let rec go : Expr → MetaM (List (Expr × Expr))
    | e@(.app _ _) => do
      let rest ← (do
        match e with
        | .app f a => pure ((← go f) ++ (← go a))
        | _ => pure [])
      match e.getAppFn.constName? with
      | some n =>
        if n != ``BEq.beq && n != ``Eq then pure rest
        else
          let args := e.getAppArgs
          if args.size < 2 then pure rest
          else
            let a := unwrapMData args[args.size - 2]!
            let b := unwrapMData args[args.size - 1]!
            let fa := a.isFVar
            let fb := b.isFVar
            if fa != fb && !hasBVar a && !hasBVar b then
              match (if fa then a else b) with
              | .fvar f =>
                if (lctx.find? f).isNone then pure rest
                else if ← alreadyDecided a b then pure rest
                else pure ((a, b) :: rest)
              | _ => pure rest
            else pure rest
      | none => pure rest
    | .lam _ d b _ => do pure ((← go d) ++ (← go b))
    | .forallE _ d b _ => do pure ((← go d) ++ (← go b))
    | .letE _ _ v b _ => do pure ((← go v) ++ (← go b))
    | .mdata _ e => go e
    | .proj _ _ e => go e
    | _ => pure []
  match ← go e with
  | [] => pure none
  | c :: _ => pure (some c)

/-- Collect head constants in `e` (for unfolding user definitions). -/
partial def headConsts : Expr → List Name
  | .const n _ => [n]
  | .app f a => headConsts f ++ headConsts a
  | .lam _ d b _ => headConsts d ++ headConsts b
  | .forallE _ d b _ => headConsts d ++ headConsts b
  | .letE _ _ v b _ => headConsts v ++ headConsts b
  | .proj _ _ e => headConsts e
  | .mdata _ e => headConsts e
  | _ => []

/-- True for constants handled elsewhere (never unfolded as head constants). -/
partial def skipHeadConst (n : Name) : Bool :=
  n == ``eligibleFuel || n == ``syntaxNodes ||
    n == ``internalNodes || n == ``externalNodes ||
    n == ``substSessionType || n == ``eligibility ||
    n == ``FmonCompute.observe || n == ``FmonCompute.outgoing ||
    n == ``FmonCompute.alphabet ||
    n.toString.startsWith "Cslib" || n.toString.startsWith "List" ||
    n.toString.startsWith "BEq" || n.toString.startsWith "Bool" ||
    n.toString.startsWith "ite" || n.toString.startsWith "inst" ||
    n.toString.startsWith "Nat" || n.toString.startsWith "String" ||
    n.toString.startsWith "Lean" || n.toString.startsWith "Eq"

/-- Collect closed `syntaxNodes V` subterms in `e` (candidates for decide-grounding). -/
partial def findClosedSyntaxNodes : Expr → List Expr
  | e@(.app (.const ``syntaxNodes _) v) =>
    (findClosedSyntaxNodes v) ++
      (if !hasFVar v && !hasBVar e then [e] else [])
  | .app f a => findClosedSyntaxNodes f ++ findClosedSyntaxNodes a
  | .lam _ d b _ => findClosedSyntaxNodes d ++ findClosedSyntaxNodes b
  | .forallE _ d b _ => findClosedSyntaxNodes d ++ findClosedSyntaxNodes b
  | .letE _ _ v b _ => findClosedSyntaxNodes v ++ findClosedSyntaxNodes b
  | .proj _ _ e => findClosedSyntaxNodes e
  | .mdata _ e => findClosedSyntaxNodes e
  | _ => []

/-- Collect `eligibleFuel` fuel arguments in `e` (for succ-exposure). -/
partial def findFuelArgs : Expr → List Expr
  | e@(.app f a) =>
    let rest := findFuelArgs f ++ findFuelArgs a
    match e.getAppFn.constName? with
    | some ``eligibleFuel =>
      let args := e.getAppArgs
      if args.size == 3 then args[0]! :: rest else rest
    | _ => rest
  | .lam _ d b _ => findFuelArgs d ++ findFuelArgs b
  | .forallE _ d b _ => findFuelArgs d ++ findFuelArgs b
  | .letE _ _ v b _ => findFuelArgs v ++ findFuelArgs b
  | .proj _ _ e => findFuelArgs e
  | .mdata _ e => findFuelArgs e
  | _ => []

/-- Collect closed `Eq`/`BEq.beq` propositions in `e` (no fvars/bvars,
    small enough for kernel evaluation). Only fully applied occurrences. -/
partial def findClosedDecidables : Expr → List Expr
  | e@(.app _ _) => do
    let rest := match e with
      | .app f a => findClosedDecidables f ++ findClosedDecidables a
      | _ => []
    match e.getAppFn.constName? with
    | some n =>
      let need := if n == ``BEq.beq then 4 else 3
      if n != ``Eq && n != ``BEq.beq && n != ``Ne then rest
      else if e.getAppArgs.size != need then rest
      else if hasFVar e || hasBVar e then rest
      else if exprSize e > 200 then rest
      else e :: rest
    | none => rest
  | .lam _ d b _ => findClosedDecidables d ++ findClosedDecidables b
  | .forallE _ d b _ => findClosedDecidables d ++ findClosedDecidables b
  | .letE _ _ v b _ => findClosedDecidables v ++ findClosedDecidables b
  | .mdata _ e => findClosedDecidables e
  | .proj _ _ e => findClosedDecidables e
  | _ => []

/-- Evaluate a closed Prop/Bool via kernel `decide` (whnf pre-check avoids
    false-proof log pollution). Returns `some true/false` or `none`. -/
partial def decideClosed (d : Expr) : MetaM (Option Bool) := do
  try
    let dec ← Lean.Meta.mkDecide d
    let b ← whnf dec
    match b with
    | .const ``Bool.true _ => pure (some true)
    | .const ``Bool.false _ => pure (some false)
    | _ => pure none
  catch _ => pure none

/-- Assert `eqTy` (proved by `prf`) under a fresh name, intro it, and rewrite
    `heName` with it. Returns true on success. -/
partial def assertIntroRw (heName : Name) (eqTy prf : Expr) (tag : Name) :
    TacticM Bool := do
  let hStx := mkIdent heName
  let nm ← mkFreshUserName tag
  let hRw : Term := mkIdent nm
  try
    let mvarId ← getMainGoal
    let mvarIdA ← mvarId.assert nm eqTy prf
    replaceMainGoal [mvarIdA]
    let nmStx := mkIdent nm
    evalTactic (← `(tactic| intro $nmStx:ident))
    evalTactic (← `(tactic| rw [$hRw:term] at $hStx:ident))
    pure true
  catch _ => pure false

/-- Ground all free variables in `he` (an `eligibility` equation) by
    unfolding (single-step rewrites only, no fixpoint simp) and splitting on
    stuck beqs. Leaves concrete hypotheses; closes contradictory goals.
    Rotates through all goals so no branch starves. -/
partial def groundGamma (heName : Name) : TacticM Unit := do
  for _ in [:256] do
    let gs ← getGoals
    if gs.isEmpty then return ()
    -- global done check: every goal's `he` grounded or gone
    let mut pending := false
    for g in gs do
      let p ← g.withContext (do
        let lctx ← getLCtx
        match lctx.findFromUserName? heName with
        | none => pure false
        | some d => do
          let t ← inferType (.fvar d.fvarId)
          pure (hasFVar t))
      if p then pending := true; break
    if !pending then return ()
    let mvarId ← getMainGoal
    -- if main goal already grounded, rotate to back so siblings progress
    let mainPending ← mvarId.withContext (do
      let lctx ← getLCtx
      match lctx.findFromUserName? heName with
      | none => pure false
      | some d => do
        let t ← inferType (.fvar d.fvarId)
        pure (hasFVar t))
    if !mainPending then
      match gs with
      | _ :: rest =>
        let h := gs[0]!
        setGoals (rest ++ [h])
      | [] => pure ()
      continue
    let done ← mvarId.withContext (do
      -- resolve he by name (FVarId changes across rewrites)
      let lctx ← getLCtx
      let some heDecl := lctx.findFromUserName? heName | return true
      let he := heDecl.fvarId
      let hty ← inferType (.fvar he)
      -- stop if he has no free variables left
      if !hasFVar hty then return true
      let hStx := mkIdent heName
      let hSize := exprSize hty
      -- 0. use ground negations to simplify he (clears != / == using h).
      -- Runs every iteration so newly exposed mismatches simplify promptly.
      -- Skipped on enormous hypotheses (avoid uncatchable simp timeouts).
      if hSize < 10000 then
        let lctx0 ← getLCtx
        let mut negNames : List Name := []
        for decl in lctx0 do
          if decl.isImplementationDetail then continue
          if decl.userName.toString.startsWith "hgroundNeg" then
            negNames := decl.userName :: negNames
        for nm in negNames do
          let hN : Term := mkIdent nm
          let okN ← (do
            try
              evalTactic (← `(tactic|
                simp only [$hN:term, beq_iff_eq, beq_self_eq_true, bne_iff_ne, Ne,
                  Bool.true_and, Bool.false_and, Bool.and_self] at $hStx:ident))
              pure true
            catch _ => pure false)
          if okN then return false
      -- 1. trivial `if` reduction (cheap, always runs)
      let iteF ← (do
        try
          evalTactic (← `(tactic| simp only [ite_true, ite_false] at $hStx:ident))
          pure true
        catch _ => pure false)
      if iteF then return false
      -- 2. safe simp (BEq/Bool/List only; terminates, no WF defs).
      -- Skipped on huge hypotheses (avoids maxRecDepth log pollution).
      let closedF ← (do
        if hSize > 10000 then pure false
        else
          try
            evalTactic (← `(tactic|
              simp only [beq_iff_eq, beq_self_eq_true, Bool.true_and,
                Bool.false_and, Bool.and_self, Bool.or_self, Bool.or_eq_true,
                Bool.and_eq_true, List.any_cons, List.any_nil, List.all_cons,
                List.all_nil, List.map_cons, List.map_nil,
                ite_true, ite_false, Bool.not_true,
                Bool.not_false, Bool.true_or, Bool.false_or, Bool.or_false,
                Bool.and_false, Bool.not_and, Bool.not_or,
                Bool.false_eq_true, Bool.true_eq_false,
                false_or, true_and, and_true, or_true, and_false, or_false,
                not_false_eq_true, not_true_eq_false]
                at $hStx:ident))
            pure true
          catch _ => pure false)
      if closedF then
        let gs2 ← getGoals
        if gs2.isEmpty then return true
        else pure ()
      -- if simp closed our goal, stop this iteration (loop picks new main)
      if ← mvarId.isAssigned then return false
      -- 3. single-step unfold of eligibility
      let unfolded1 ← (do
        try
          evalTactic (← `(tactic| rw [eligibility] at $hStx:ident))
          pure true
        catch _ => pure false)
      if unfolded1 then return false
      -- 4. ground a closed `syntaxNodes V` to a literal via assert + rw
      let ty3 ← inferType (.fvar he)
      for sn in findClosedSyntaxNodes ty3 do
        for n in [:32] do
          let lit := Lean.mkNatLit n
          if ← isDefEq sn lit then
            let eqTy ← Lean.Meta.mkEq sn lit
            let prf ← Lean.Meta.mkEqRefl lit
            if ← assertIntroRw heName eqTy prf `hsn then return false
      -- 5. rewrite a literal fuel to succ form (expose succ for match)
      let tyF ← inferType (.fvar he)
      for fuelV in (findFuelArgs tyF).eraseDups do
        if hasBVar fuelV then pure ()
        else match fuelV.nat? with
        | some k =>
          if k == 0 then pure ()
          else
            let predE := Lean.mkNatLit (k - 1)
            let succE := Lean.mkApp (.const ``Nat.succ []) predE
            if ← isDefEq fuelV succE then
              let eqTy ← Lean.Meta.mkEq fuelV succE
              let prf ← Lean.Meta.mkEqRefl succE
              if ← assertIntroRw heName eqTy prf `hfuel then return false
        | none => pure ()
      -- 5b. collapse closed decidable props/bools via `decide`.
      -- (e.g. `if "Outgoing" = "Incoming"` conditions; no unfolding needed.
      -- whnf pre-check selects the true disjunct so `decide` never fails.)
      let tyC ← inferType (.fvar he)
      for d in (findClosedDecidables tyC).eraseDups do
        match ← decideClosed d with
        | none => pure ()
        | some b =>
          let dTy ← inferType d
          let isProp ← isDefEq dTy (Lean.mkSort Lean.levelZero)
          let dStx ← Lean.Elab.Term.exprToSyntax d
          let nmD ← mkFreshUserName `hdec
          let hD : Term := mkIdent nmD
          let ok ← (do
            try
              if isProp then
                if b then
                  evalTactic (← `(tactic| have $(mkIdent nmD) : $dStx:term := by decide))
                else
                  evalTactic (← `(tactic| have $(mkIdent nmD) : ¬$dStx:term := by decide))
              else if b then
                evalTactic (← `(tactic| have $(mkIdent nmD) : $dStx:term = true := by decide))
              else
                evalTactic (← `(tactic| have $(mkIdent nmD) : $dStx:term = false := by decide))
              evalTactic (← `(tactic| simp only [$hD:term] at $hStx:ident))
              pure true
            catch _ => pure false)
          if ok then return false
      -- 6. dsimp for iota/beta (before eq-lemmas so exposed matches reduce
      -- before new ones are exposed; exposes constructors for unfold)
      let simpD ← (do
        try
          evalTactic (← `(tactic| dsimp only at $hStx:ident))
          pure true
        catch _ => pure false)
      if simpD then return false
      -- 7. unfold one equation lemma at a time (first success wins;
      -- eligibleFuel last so fuel gets grounded first)
      let unfolded2 ← (do
        try
          evalTactic (← `(tactic| first
            | rw [syntaxNodes.eq_def] at $hStx:ident
            | rw [internalNodes.eq_def] at $hStx:ident
            | rw [externalNodes.eq_def] at $hStx:ident
            | rw [substSessionType.eq_def] at $hStx:ident
            | rw [go_int_eq_map] at $hStx:ident
            | rw [go_ext_eq_map] at $hStx:ident
            | rw [eligibleFuel.eq_def] at $hStx:ident))
          pure true
        catch _ => pure false)
      if unfolded2 then return false
      -- 8. byCases on a stuck beq/eq with a free var side (before unfold
      -- so splits close branches promptly instead of unfolding forever)
      let lctx ← getLCtx
      let ty ← inferType (.fvar he)
      let found ← findStuckEq ty lctx
      let didSplit ← match found with
      | some (a, b) => do
        let allGs ← getGoals
        let rest := allGs.filter (· != mvarId)
        let eqP ← Lean.Meta.mkEq a b
        let (mT, mF) ← mvarId.byCases eqP
        -- True branch: ground the var via rw+clear (atomic; unlike
        -- `subst`, never leaves partial revert/intro state on failure).
        setGoals [mT.mvarId]
        (try
          let hT := mT.fvarId
          let nmT ← renameFresh hT `hground
          let hT2 : Term := mkIdent nmT
          let isLhsVar ← mT.mvarId.withContext (do
            let ty ← whnf (← inferType (.fvar hT))
            let args := ty.getAppArgs
            if h : args.size > 1 then pure args[1]!.isFVar
            else pure false)
          if isLhsVar then
            evalTactic (← `(tactic| rw [$hT2:term] at *))
          else
            evalTactic (← `(tactic| rw [← $hT2:term] at *))
          (try evalTactic (← `(tactic| clear $(mkIdent nmT))) catch _ => pure ())
        catch _ => pure ())
        (try evalTactic (← `(tactic| contradiction)) catch _ => pure ())
        let gsT ← getGoals
        -- False branch: targeted simp with the negation, then close if
        -- contradictory. (No simp_all: it rewrites goal shape.)
        setGoals [mF.mvarId]
        (try
          let hF := mF.fvarId
          let nmF ← renameFresh hF `hgroundNeg
          let hN : Term := mkIdent nmF
          evalTactic (← `(tactic|
            simp only [$hN:term, beq_iff_eq, beq_self_eq_true, bne_iff_ne,
              Bool.true_and, Bool.false_and, Bool.and_self] at $hStx:ident))
        catch _ => pure ())
        (try evalTactic (← `(tactic| contradiction)) catch _ => pure ())
        let gsF ← getGoals
        setGoals (gsT ++ gsF ++ rest)
        pure true
      | none => pure false
      -- 9. unfold one head Firewall definition via unfold; last resort.
      -- Gated by DEFINITION body size (small defs only) to prevent bloat:
      -- unfolding a huge branch list without immediate reduction explodes he.
      let ty5 ← inferType (.fvar he)
      let allConsts := (headConsts ty5).eraseDups
      let consts := allConsts.filter
        (fun n => n.toString.contains "Fw")
      for c in consts do
        let cInfo ← Lean.getConstInfo c
        match cInfo.value? with
        | none => pure ()
        | some val =>
          if exprSize val > 300 then pure ()
          else
            let cStx := mkIdent c
            let ok5 ← (do
              try
                evalTactic (← `(tactic| unfold $cStx:ident at $hStx:ident))
                pure true
              catch _ => pure false)
            if ok5 then return false
      pure false)
    if done then continue
  return ()

/-- 1-branch pfx handler (concrete bs, abstract gamma via by_cases). -/
partial def fmonPfx1 (V : Expr) (hall hnd hkey hcov hke : FVarId) (isInt : Bool) : TacticM Unit := do
  -- first, try contradiction (prunes impossible pfx, e.g. hneq : q≠q is False)
  let mvarId0 ← getMainGoal
  let closed ← mvarId0.withContext (do
    try
      evalTactic (← `(tactic| contradiction))
      pure true
    catch _ => pure false)
  if closed then pure ()
  else if isInt then fmonPfx1Int V hall hnd hkey hcov hke
  else
    let gam ← extractGamma hcov
    let mvarId ← getMainGoal
    -- V = externalChoice p bs; get bs (arg 1)
    let bs ← mvarId.withContext (do
      let ty ← whnf V
      let args := ty.getAppArgs
      if h : args.size > 1 then pure args[1]!
      else throwError "fmonPfx1: bad ext")
    -- bs must be cons b nil; get b (robust to implicit args)
    let b ← match bs with
      | .app h2 t =>
        if h2.getAppFn.constName? == some ``List.cons &&
            t.getAppFn.constName? == some ``List.nil then
          -- h2 = cons α b; get b as second explicit arg (args[1])
          let h2args := h2.getAppArgs
          if h : h2args.size > 0 then pure h2args[h2args.size - 1]!
          else throwError "fmonPfx1: cons args"
        else throwError "fmonPfx1: bs not singleton"
      | _ => throwError "fmonPfx1: bs not list"
    -- b = (l, s, T0); T0 is third component via projections
    let t0 : Expr ← mvarId.withContext (do
      pure (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b)))
    -- by_cases Ex T0 γ (whnf T0 to literal first for clean hEx)
    let t0W ← mvarId.withContext (whnf t0)
    let exProp := mkAppN (.const ``Ex []) #[t0W, gam]
    let mvarIdB ← getMainGoal
    let (mTrue, mFalse) ← mvarIdB.byCases exProp
    -- False branch: ¬Ex → kept=[] (via hkey), contradiction with hke.
    -- (byCases already intro'd the ¬Ex hyp; no intro needed)
    setGoals [mFalse.mvarId]
    let nmKey ← renameFresh hkey `hkey
    let nmKe ← renameFresh hke `hke
    -- find kept (fvar in hke type) and rename for use
    let mvarF0 ← getMainGoal
    let keptF ← mvarF0.withContext (do
      let ty ← inferType (.fvar hke)
      let rec findF : Expr → Option FVarId
        | .fvar f => some f
        | .app f a => match findF f with | some g => some g | none => findF a
        | .forallE _ d b _ => match findF d with | some g => some g | none => findF b
        | .lam _ d b _ => match findF d with | some g => some g | none => findF b
        | _ => none
      match findF ty with
      | some f => pure f
      | none => throwError "no kept fvar")
    let nmKept ← renameFresh keptF `kept
    let mvarF ← getMainGoal
    let closedF ← mvarF.withContext (do
      try
        evalTactic (← `(tactic|
          (have hempty : $(mkIdent nmKept) = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            rintro ⟨l, s, T1⟩ hx
            obtain ⟨T0, hmemBs, hEx⟩ := $(mkIdent nmKey) l s T1 hx
            -- hmemBs : (l,s,T0) ∈ [singleton]; simp to equality, congrArg+subst to concrete
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
            have h1 : _ = _ := congrArg Prod.fst hmemBs
            have h2 : _ = _ := congrArg (Prod.fst ∘ Prod.snd) hmemBs
            have h3 : _ = _ := congrArg (Prod.snd ∘ Prod.snd) hmemBs
            simp only at h1 h2 h3
            subst h1; subst h2; subst h3
            exact absurd hEx (by assumption)
           (first | contradiction | simp_all))))
        pure true
      catch _ => pure false)
    if !closedF then throwError "fmonPfx1 ext False: not closed"
    -- True branch (Ex holds): hcov fires, hall gives fchild, invert, pin, close.
    -- (byCases already intro'd the Ex hyp)
    setGoals [mTrue.mvarId]
    let mvarT ← getMainGoal
    -- find hEx (type head is Ex, not just contains Ex)
    let hEx ← mvarT.withContext (do
      let lctx ← getLCtx
      let mut found : Option FVarId := none
      for decl in lctx do
        if decl.isImplementationDetail then continue
        let ty ← inferType decl.toExpr
        if (stripForalls ty).getAppFn.constName? == some ``Ex then
          found := some decl.fvarId
          break
      match found with
      | some f => pure f
      | none => throwError "no Ex hyp in True branch")
    -- extract l,s (projections of b), whnf to literals, convert to syntax
    -- b = (l, s, T0) = Prod.mk l (Prod.mk s T0); l=b.1, s=b.2.1, T0=b.2.2
    let (lStx, sStx, t0Stx, bsStx) ← mvarT.withContext (do
      let lPw := Expr.proj ``Prod 0 b
      let sPw := Expr.proj ``Prod 0 (Expr.proj ``Prod 1 b)
      let lW ← whnf lPw
      let sW ← whnf sPw
      let t0W ← whnf t0
      let bsW ← whnf bs
      let lS ← Lean.Elab.Term.exprToSyntax lW
      let sS ← Lean.Elab.Term.exprToSyntax sW
      let t0S ← Lean.Elab.Term.exprToSyntax t0W
      let bsS ← Lean.Elab.Term.exprToSyntax bsW
      pure (lS, sS, t0S, bsS))
    let nmCov ← renameFresh hcov `hcov
    let nmHall ← renameFresh hall `hall
    let nmEx ← renameFresh hEx `hEx
    evalTactic (← `(tactic|
      (have hmemBs : ($lStx, $sStx, $t0Stx) ∈ $bsStx := List.mem_cons_self
       obtain ⟨T1, hmemK⟩ := $(mkIdent nmCov) $lStx $sStx $t0Stx hmemBs $(mkIdent nmEx)
       have hfc := $(mkIdent nmHall) $t0Stx T1 $lStx $sStx hmemBs hmemK)))
    -- invert fchild (hfc from the have above; hygienic name, find by prefix)
    let mvarC ← getMainGoal
    let hfcF ← mvarC.withContext (do
      let lctx ← getLCtx
      let mut found : Option FVarId := none
      for decl in lctx do
        if decl.isImplementationDetail then continue
        if decl.userName.toString.startsWith "hfc." || decl.userName.toString == "hfc" then
          found := some decl.fvarId
          break
      match found with
      | some f => pure f
      | none => throwError "no hfc hyp")
    let subC ← mvarC.withContext (mvarC.cases hfcF)
    for sgC in subC do
      setGoals [sgC.mvarId]
      if sgC.ctorName == some ``fchild.fc_fold then
        -- fold: find membership premise ((T,u) ∈ G) among fields; cases closes if G empty
        let fsC := (sgC.fields.filterMap (fun e => e.fvarId?)).toList
        let mvarM ← getMainGoal
        let hmem ← mvarM.withContext (do
          let mut found : Option FVarId := none
          for f in fsC do
            let ty ← inferType (.fvar f)
            if hasConstIn ty ``Membership.mem || hasConstIn ty ``List.Mem then
              found := some f
              break
          match found with
          | some h => pure h
          | none => throwError "no mem in fold")
        let subM ← mvarM.withContext (mvarM.cases hmem)
        if subM.size = 0 then pure ()
        else throwError "fchild fold non-empty G: manual"
      else if sgC.ctorName == some ``fchild.fc_go then
        -- go: fmon hyp in fields; recurse (assigns T1), then pin kept + close.
        let fsG := (sgC.fields.filterMap (fun e => e.fvarId?)).toList
        let mvarG ← getMainGoal
        let hfmon ← mvarG.withContext (do
          let mut found : Option FVarId := none
          for f in fsG do
            let ty ← inferType (.fvar f)
            if (stripForalls ty).getAppFn.constName? == some ``fmon then
              found := some f
              break
          match found with
          | some h => pure h
          | none => throwError "no fmon in go")
        -- try recurse (ignore closer failure; T1 gets assigned)
        let _ ← recurseFmon hfmon
        -- pin kept = [(l,s,T1)] (T1 now concrete) via hke/hkey/hnd/hmemK, then closer
        -- find hmemK (... ∈ keptF) and keptF (already have nmKept name; get FVar via ... actually keptF in scope)
        -- skip pin if recursion already closed the goal
        let gs ← getGoals
        if gs.isEmpty then return ()
        let hmemK ← findMemKept keptF
        -- find T1 fvar in hmemK (fvar ≠ keptF)
        let mvarQ ← getMainGoal
        let t1F ← mvarQ.withContext (do
          let ty ← inferType (.fvar hmemK)
          let rec findT : Expr → Option FVarId
            | .fvar f => if f == keptF then none else some f
            | .app f a => match findT f with | some g => some g | none => findT a
            | .forallE _ d b _ => match findT d with | some g => some g | none => findT b
            | .lam _ d b _ => match findT d with | some g => some g | none => findT b
            | _ => none
          match findT ty with
          | some f => pure f
          | none => throwError "no T1")
        let nmT1 ← renameFresh t1F `T1
        let nmKept ← renameFresh keptF `kept
        let nmKey2 ← renameFresh hkey `hkey
        let nmNd ← renameFresh hnd `hnd
        let nmKe2 ← renameFresh hke `hke
        let nmMemK ← renameFresh hmemK `hmemK
        -- pin: kept = [(l,s,T1)] via kept_ext_singleton, then rw + close
        evalTactic (← `(tactic|
          (have hallk : ∀ x ∈ $(mkIdent nmKept), (x.1, x.2.1) = ($lStx, $sStx) := by
            intro x hx
            obtain ⟨T0, hmemBs, hEx⟩ := $(mkIdent nmKey2) x.1 x.2.1 x.2.2 hx
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
            have h1 : _ = _ := congrArg Prod.fst hmemBs
            have h2 : _ = _ :=
              congrArg (fun t : Lab × DataSort × SessionType => t.2.1) hmemBs
            simp only at h1 h2
            rw [h1, h2]
           have hpin : $(mkIdent nmKept) =
              [($lStx, $sStx, $(mkIdent nmT1))] := kept_ext_singleton
                (b := ($lStx, $sStx, $t0Stx)) $(mkIdent nmKe2) $(mkIdent nmNd)
                $(mkIdent nmMemK) hallk
           rw [hpin]
           fmon_close)))
      else throwError "unhandled fchild case"
    pure ()

/-- 1-branch int pfx handler: mirror of the ext case with 4-tuples
    `(r, l, s, T)`, `int_key`, and `kept_int_singleton`. -/
partial def fmonPfx1Int (V : Expr) (hall hnd hkey hcov hke : FVarId) :
    TacticM Unit := do
  let gam ← extractGamma hcov
  let mvarId ← getMainGoal
  -- V = internalChoice bs; get bs (last arg)
  let bs ← mvarId.withContext (do
    let ty ← whnf V
    let args := ty.getAppArgs
    if h : args.size > 0 then pure args[args.size - 1]!
    else throwError "fmonPfx1Int: bad int")
  -- bs must be cons b nil; get b (robust to implicit args)
  let b ← match bs with
    | .app h2 t =>
      if h2.getAppFn.constName? == some ``List.cons &&
          t.getAppFn.constName? == some ``List.nil then
        let h2args := h2.getAppArgs
        if h : h2args.size > 0 then pure h2args[h2args.size - 1]!
        else throwError "fmonPfx1Int: cons args"
      else throwError "fmonPfx1Int: bs not singleton"
    | _ => throwError "fmonPfx1Int: bs not list"
  -- b = (r, l, s, T0); T0 is fourth component via projections
  let t0 : Expr ← mvarId.withContext (do
    pure (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b))))
  -- by_cases Ex T0 γ (whnf T0 to literal first for clean hEx)
  let t0W ← mvarId.withContext (whnf t0)
  let exProp := mkAppN (.const ``Ex []) #[t0W, gam]
  let mvarIdB ← getMainGoal
  let (mTrue, mFalse) ← mvarIdB.byCases exProp
  -- False branch: ¬Ex → kept=[] (via hkey), contradiction with hke.
  setGoals [mFalse.mvarId]
  let nmKey ← renameFresh hkey `hkey
  let nmKe ← renameFresh hke `hke
  let mvarF0 ← getMainGoal
  let keptF ← mvarF0.withContext (do
    let ty ← inferType (.fvar hke)
    let rec findF : Expr → Option FVarId
      | .fvar f => some f
      | .app f a => match findF f with | some g => some g | none => findF a
      | .forallE _ d b _ => match findF d with | some g => some g | none => findF b
      | .lam _ d b _ => match findF d with | some g => some g | none => findF b
      | _ => none
    match findF ty with
    | some f => pure f
    | none => throwError "no kept fvar")
  let nmKept ← renameFresh keptF `kept
  let mvarF ← getMainGoal
  let closedF ← mvarF.withContext (do
    try
      evalTactic (← `(tactic|
        (have hempty : $(mkIdent nmKept) = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          rintro ⟨r, l, s, T1⟩ hx
          obtain ⟨T0, hmemBs, hEx⟩ := $(mkIdent nmKey) r l s T1 hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
          have h1 : _ = _ := congrArg Prod.fst hmemBs
          have h2 : _ = _ :=
            congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.1)
              hmemBs
          have h3 : _ = _ :=
            congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.1)
              hmemBs
          have h4 : _ = _ :=
            congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.2)
              hmemBs
          simp only at h1 h2 h3 h4
          subst h1; subst h2; subst h3; subst h4
          exact absurd hEx (by assumption)
         (first | contradiction | simp_all))))
      pure true
    catch _ => pure false)
  if !closedF then throwError "fmonPfx1Int False: not closed"
  -- True branch (Ex holds): hcov fires, hall gives fchild, invert, pin, close.
  setGoals [mTrue.mvarId]
  let mvarT ← getMainGoal
  let hEx ← mvarT.withContext (do
    let lctx ← getLCtx
    let mut found : Option FVarId := none
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let ty ← inferType decl.toExpr
      if (stripForalls ty).getAppFn.constName? == some ``Ex then
        found := some decl.fvarId
        break
    match found with
    | some f => pure f
    | none => throwError "no Ex hyp in True branch")
  -- extract r,l,s (projections of b), whnf to literals, convert to syntax
  let (rStx, lStx, sStx, t0Stx, bsStx) ← mvarT.withContext (do
    let rPw := Expr.proj ``Prod 0 b
    let lPw := Expr.proj ``Prod 0 (Expr.proj ``Prod 1 b)
    let sPw := Expr.proj ``Prod 0 (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b))
    let rW ← whnf rPw
    let lW ← whnf lPw
    let sW ← whnf sPw
    let t0W ← whnf t0
    let bsW ← whnf bs
    let rS ← Lean.Elab.Term.exprToSyntax rW
    let lS ← Lean.Elab.Term.exprToSyntax lW
    let sS ← Lean.Elab.Term.exprToSyntax sW
    let t0S ← Lean.Elab.Term.exprToSyntax t0W
    let bsS ← Lean.Elab.Term.exprToSyntax bsW
    pure (rS, lS, sS, t0S, bsS))
  let nmCov ← renameFresh hcov `hcov
  let nmHall ← renameFresh hall `hall
  let nmEx ← renameFresh hEx `hEx
  evalTactic (← `(tactic|
    (have hmemBs : ($rStx, $lStx, $sStx, $t0Stx) ∈ $bsStx :=
      List.mem_cons_self
     obtain ⟨T1, hmemK⟩ := $(mkIdent nmCov) $rStx $lStx $sStx $t0Stx
       hmemBs $(mkIdent nmEx)
     have hfc := $(mkIdent nmHall) $t0Stx T1 $rStx $lStx $sStx
       hmemBs hmemK)))
  let mvarC ← getMainGoal
  let hfcF ← mvarC.withContext (do
    let lctx ← getLCtx
    let mut found : Option FVarId := none
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if decl.userName.toString.startsWith "hfc." ||
          decl.userName.toString == "hfc" then
        found := some decl.fvarId
        break
    match found with
    | some f => pure f
    | none => throwError "no hfc hyp")
  let subC ← mvarC.withContext (mvarC.cases hfcF)
  for sgC in subC do
    setGoals [sgC.mvarId]
    if sgC.ctorName == some ``fchild.fc_fold then
      let fsC := (sgC.fields.filterMap (fun e => e.fvarId?)).toList
      let mvarM ← getMainGoal
      let hmem ← mvarM.withContext (do
        let mut found : Option FVarId := none
        for f in fsC do
          let ty ← inferType (.fvar f)
          if hasConstIn ty ``Membership.mem || hasConstIn ty ``List.Mem then
            found := some f
            break
        match found with
        | some h => pure h
        | none => throwError "no mem in fold")
      let subM ← mvarM.withContext (mvarM.cases hmem)
      if subM.size = 0 then pure ()
      else throwError "fchild fold non-empty G: manual"
    else if sgC.ctorName == some ``fchild.fc_go then
      let fsG := (sgC.fields.filterMap (fun e => e.fvarId?)).toList
      let mvarG ← getMainGoal
      let hfmon ← mvarG.withContext (do
        let mut found : Option FVarId := none
        for f in fsG do
          let ty ← inferType (.fvar f)
          if (stripForalls ty).getAppFn.constName? == some ``fmon then
            found := some f
            break
        match found with
        | some h => pure h
        | none => throwError "no fmon in go")
      let _ ← recurseFmon hfmon
      let gs ← getGoals
      if gs.isEmpty then return ()
      let hmemK ← findMemKept keptF
      let mvarQ ← getMainGoal
      let t1F ← mvarQ.withContext (do
        let ty ← inferType (.fvar hmemK)
        let rec findT : Expr → Option FVarId
          | .fvar f => if f == keptF then none else some f
          | .app f a => match findT f with | some g => some g | none => findT a
          | .forallE _ d b _ => match findT d with | some g => some g | none => findT b
          | .lam _ d b _ => match findT d with | some g => some g | none => findT b
          | _ => none
        match findT ty with
        | some f => pure f
        | none => throwError "no T1")
      let nmT1 ← renameFresh t1F `T1
      let nmKept ← renameFresh keptF `kept
      let nmKey2 ← renameFresh hkey `hkey
      let nmNd ← renameFresh hnd `hnd
      let nmKe2 ← renameFresh hke `hke
      let nmMemK ← renameFresh hmemK `hmemK
      evalTactic (← `(tactic|
        (have hallk : ∀ x ∈ $(mkIdent nmKept),
            (x.1, x.2.1, x.2.2.1) = ($rStx, $lStx, $sStx) := by
          intro x hx
          obtain ⟨T0, hmemBs, hEx⟩ := $(mkIdent nmKey2) x.1 x.2.1
            x.2.2.1 x.2.2.2 hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
          have h1 : _ = _ := congrArg Prod.fst hmemBs
          have h2 : _ = _ :=
            congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.1)
              hmemBs
          have h3 : _ = _ :=
            congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.1)
              hmemBs
          simp only at h1 h2 h3
          rw [h1, h2, h3]
         have hpin : $(mkIdent nmKept) =
            [($rStx, $lStx, $sStx, $(mkIdent nmT1))] := kept_int_singleton
              (b := ($rStx, $lStx, $sStx, $t0Stx)) $(mkIdent nmKe2)
              $(mkIdent nmNd) $(mkIdent nmMemK) hallk
         rw [hpin]
         fmon_close)))
    else throwError "unhandled fchild case"
  pure ()

/-- Find the `kept` list variable from the shape of `hke : kept ≠ []`. -/
partial def findKeptF (hke : FVarId) : TacticM FVarId := do
  let mvarF0 ← getMainGoal
  mvarF0.withContext (do
    let ty ← inferType (.fvar hke)
    let rec findF : Expr → Option FVarId
      | .fvar f => some f
      | .app f a => match findF f with | some g => some g | none => findF a
      | .forallE _ d b _ => match findF d with | some g => some g | none => findF b
      | .lam _ d b _ => match findF d with | some g => some g | none => findF b
      | _ => none
    match findF ty with
    | some f => pure f
    | none => throwError "no kept fvar")

/-- Container of a `Mem` hyp holds `keptF`: check last and second-to-last
    explicit args (covers both `Membership.mem` and `List.Mem` shapes). -/
partial def memContainerIs (ty : Expr) (keptF : FVarId) : Bool :=
  let args := ty.getAppArgs
  let isKept : Expr → Bool
    | .fvar f => f == keptF
    | _ => false
  let okBack : Bool := match args.back? with
    | some e => isKept e
    | _ => false
  let okPrev : Bool := match args.toList.reverse with
    | _ :: prev :: _ => isKept prev
    | _ => false
  okBack || okPrev

partial def findMemKept (keptF : FVarId) : TacticM FVarId := do
  let mvarId ← getMainGoal
  mvarId.withContext (do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let ty ← inferType decl.toExpr
      if ty.isForall then continue
      if !(hasConstIn ty ``Membership.mem || hasConstIn ty ``List.Mem) then
        continue
      if !memContainerIs ty keptF then continue
      return decl.fvarId
    throwError "no hmemK")

/-- Find a hypothesis by its user name, ignoring macro scopes
    (evalTactic-introduced names carry hygiene scopes). -/
partial def findNamed (n : Name) : TacticM FVarId := do
  let mvarId ← getMainGoal
  mvarId.withContext (do
    let lctx ← getLCtx
    let mut acc : List FVarId := []
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if decl.userName.eraseMacroScopes == n then
        acc := decl.fvarId :: acc
    match acc with
    | [f] => pure f
    | [] => throwError "hyp {n} not found"
    | _ =>
      let mut msg := m!"hyp {n} ambiguous:"
      for f in acc do
        msg := msg ++ m!"\n  {← inferType (.fvar f)}"
      throwError msg)

/-- Single eligible ext branch against a 2-branch list: fire `hcov`/`hall`,
    invert the `fchild`, recurse, pin `kept` to `[(l,s,T1)]` (the other
    branch is discharged by the ambient `¬Ex` hypothesis via `assumption`),
    and close. `(ol, os, ot)` are the other branch literals; `thisIsLeft`
    says whether this branch is the head of `bs`. -/
partial def closeSingleExtBranch (lStx sStx t0Stx bsStx ol os ot : Lean.Term)
    (thisIsLeft : Bool) (hcov hall hEx hkey hnd hke keptF : FVarId) :
    TacticM Unit := do
  let nmCov ← renameFresh hcov `hcov
  let nmHall ← renameFresh hall `hall
  let nmEx ← renameFresh hEx `hEx
  let memPf : Lean.Term ← if thisIsLeft then `(List.mem_cons_self)
    else `(List.mem_cons_of_mem _ List.mem_cons_self)
  evalTactic (← `(tactic|
    (have hmemBs : ($lStx, $sStx, $t0Stx) ∈ $bsStx := $memPf
     obtain ⟨T1, hmemK⟩ := $(mkIdent nmCov) $lStx $sStx $t0Stx hmemBs
       $(mkIdent nmEx)
     have hfc := $(mkIdent nmHall) $t0Stx T1 $lStx $sStx hmemBs hmemK)))
  let mvarC ← getMainGoal
  let hfcF ← mvarC.withContext (do
    let lctx ← getLCtx
    let mut found : Option FVarId := none
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if decl.userName.toString.startsWith "hfc." ||
          decl.userName.toString == "hfc" then
        found := some decl.fvarId
        break
    match found with
    | some f => pure f
    | none => throwError "no hfc hyp")
  let subC ← mvarC.withContext (mvarC.cases hfcF)
  for sgC in subC do
    setGoals [sgC.mvarId]
    if sgC.ctorName == some ``fchild.fc_fold then
      let fsC := (sgC.fields.filterMap (fun e => e.fvarId?)).toList
      let mvarM ← getMainGoal
      let hmem ← mvarM.withContext (do
        let mut found : Option FVarId := none
        for f in fsC do
          let ty ← inferType (.fvar f)
          if hasConstIn ty ``Membership.mem || hasConstIn ty ``List.Mem then
            found := some f
            break
        match found with
        | some h => pure h
        | none => throwError "no mem in fold")
      let subM ← mvarM.withContext (mvarM.cases hmem)
      if subM.size = 0 then pure ()
      else throwError "fchild fold non-empty G: manual"
    else if sgC.ctorName == some ``fchild.fc_go then
      let fsG := (sgC.fields.filterMap (fun e => e.fvarId?)).toList
      let mvarG ← getMainGoal
      let hfmon ← mvarG.withContext (do
        let mut found : Option FVarId := none
        for f in fsG do
          let ty ← inferType (.fvar f)
          if (stripForalls ty).getAppFn.constName? == some ``fmon then
            found := some f
            break
        match found with
        | some h => pure h
        | none => throwError "no fmon in go")
      let _ ← recurseFmon hfmon
      let gs ← getGoals
      if gs.isEmpty then return ()
      let hmemK ← findMemKept keptF
      let mvarQ ← getMainGoal
      let t1F ← mvarQ.withContext (do
        let ty ← inferType (.fvar hmemK)
        let rec findT : Expr → Option FVarId
          | .fvar f => if f == keptF then none else some f
          | .app f a => match findT f with | some g => some g | none => findT a
          | .forallE _ d b _ => match findT d with | some g => some g | none => findT b
          | .lam _ d b _ => match findT d with | some g => some g | none => findT b
          | _ => none
        match findT ty with
        | some f => pure f
        | none => throwError "no T1")
      -- skip pin if recursion already closed the goal
      let gs ← getGoals
      if gs.isEmpty then return ()
      let nmT1 ← renameFresh t1F `T1
      let nmKept ← renameFresh keptF `kept
      let nmKey2 ← renameFresh hkey `hkey
      let nmNd ← renameFresh hnd `hnd
      let nmKe2 ← renameFresh hke `hke
      let nmMemK ← renameFresh hmemK `hmemK
      let pinB ← `(tacticSeq|
        have h1 : _ = _ := congrArg Prod.fst h
        have h2 : _ = _ :=
          congrArg (fun t : Lab × DataSort × SessionType => t.2.1) h
        simp only at h1 h2
        rw [h1, h2])
      let contraB ← `(tacticSeq|
        have e : _ = _ :=
          congrArg (fun t : Lab × DataSort × SessionType => t.2.2) h
        simp only at e
        rw [e] at hEx
        exact absurd hEx (by assumption))
      let (firstB, secondB) :=
        if thisIsLeft then (pinB, contraB) else (contraB, pinB)
      evalTactic (← `(tactic|
        (have hallk : ∀ x ∈ $(mkIdent nmKept), (x.1, x.2.1) = ($lStx, $sStx) := by
          intro x hx
          obtain ⟨T0, hmemBs, hEx⟩ := $(mkIdent nmKey2) x.1 x.2.1 x.2.2 hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
          rcases hmemBs with h | h
          · $firstB
          · $secondB
         have hpin : $(mkIdent nmKept) =
            [($lStx, $sStx, $(mkIdent nmT1))] := kept_ext_singleton
              (b := ($lStx, $sStx, $t0Stx)) $(mkIdent nmKe2) $(mkIdent nmNd)
              $(mkIdent nmMemK) hallk
         rw [hpin]
         fmon_close)))
    else throwError "unhandled fchild case"
  pure ()

/-- Recurse into an `fmon` payload, preserving the outer goal list:
    nested inversions replace the goal list via `setGoals`, so snapshot it
    beforehand and restore afterwards (nested work cannot close outer
    goals, which live in disjoint subgoals). -/
partial def recurseFmon (hfmon : FVarId) : TacticM Bool := do
  let saved ← getGoals
  let mcur ← getMainGoal
  let ok ← mcur.withContext (do
    try
      fmonInvMain hfmon
      pure true
    catch e =>
      logInfo m!"[recurseFmon] nested failure: {e.toMessageData}"
      pure false)
  let live ← saved.filterM (fun m => do pure !(← m.isAssigned))
  setGoals live
  pure ok

/-- Invert one `fchild` and recurse into its `fmon` payload. Skips silently
    when a previous inversion already closed the goal (shared-goal
    sequential inversion). -/
partial def invertRecurseFchild (hfcF : FVarId) : TacticM Unit := do
  let gs ← getGoals
  if gs.isEmpty then return ()
  let mcur ← getMainGoal
  let sub ← mcur.withContext (mcur.cases hfcF)
  for sg in sub do
    setGoals [sg.mvarId]
    if sg.ctorName == some ``fchild.fc_fold then
      let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
      let mm ← getMainGoal
      let hmem ← mm.withContext (do
        let mut found : Option FVarId := none
        for f in fs do
          let ty ← inferType (.fvar f)
          if hasConstIn ty ``Membership.mem || hasConstIn ty ``List.Mem then
            found := some f
            break
        match found with
        | some h => pure h
        | none => throwError "no mem in fold")
      let subM ← mm.withContext (mm.cases hmem)
      if subM.size = 0 then pure ()
      else throwError "fchild fold non-empty G: manual"
    else if sg.ctorName == some ``fchild.fc_go then
      let fs := (sg.fields.filterMap (fun e => e.fvarId?)).toList
      let mg ← getMainGoal
      let hfmon ← mg.withContext (do
        let mut found : Option FVarId := none
        for f in fs do
          let ty ← inferType (.fvar f)
          if (stripForalls ty).getAppFn.constName? == some ``fmon then
            found := some f
            break
        match found with
        | some h => pure h
        | none => throwError "no fmon in go")
      let _ ← recurseFmon hfmon
      pure ()
    else throwError "unhandled fchild case"
  pure ()

/-- 2-pin `kept` via `kept_ext_two_ee_disj` and close. Skips silently when a
    previous inversion already closed the goal. -/
partial def pinTwoExt (l1 s1 t01S l2 s2 t02S : Lean.Term)
    (hkey hke hnd keptF : FVarId) : TacticM Unit := do
  let gs ← getGoals
  if gs.isEmpty then return ()
  -- hmemK1/hmemK2 were introduced by the creation block's obtains
  -- (branch1 then branch2); look up by name for order safety.
  let hmemK1 ← findNamed `hmemK1
  let hmemK2 ← findNamed `hmemK2
  let nmM1 ← renameFresh hmemK1 `hmemK1
  let nmM2 ← renameFresh hmemK2 `hmemK2
  let nmKept ← renameFresh keptF `kept
  let nmKey ← renameFresh hkey `hkey
  let nmKe ← renameFresh hke `hke
  let nmNd ← renameFresh hnd `hnd
  evalTactic (← `(tactic|
    (have hallk2 : ∀ x ∈ $(mkIdent nmKept), x.1 = $l1 ∨ x.1 = $l2 := by
      intro x hx
      obtain ⟨T0, hmemBs, hExT0⟩ := $(mkIdent nmKey) x.1 x.2.1 x.2.2 hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
      rcases hmemBs with h | h
      · left
        have hh : _ = _ := congrArg Prod.fst h
        simpa using hh
      · right
        have hh : _ = _ := congrArg Prod.fst h
        simpa using hh
     have hne12 : ($l1 : Lab) ≠ $l2 := by decide
     have hpin := kept_ext_two_ee_disj (b1 := ($l1, $s1, $t01S))
       (b2 := ($l2, $s2, $t02S)) $(mkIdent nmKe) $(mkIdent nmNd)
       $(mkIdent nmM1) $(mkIdent nmM2) hallk2 hne12
     rcases hpin with hpin | hpin <;> rw [hpin] <;> fmon_close)))
  pure ()

/-- 2-branch ext pfx handler: split `Ex`-status of both branches; neither
    eligible closes by `kept=[]`, exactly one eligible pins a singleton via
    `kept_ext_singleton`, both pin the pair via
    `kept_ext_two_ee_disj`. -/
partial def fmonPfx2Ext (V : Expr) (hall hnd hkey hcov hke : FVarId) :
    TacticM Unit := do
  let mvarId0 ← getMainGoal
  let closed ← mvarId0.withContext (do
    try
      evalTactic (← `(tactic| contradiction))
      pure true
    catch _ => pure false)
  if closed then pure ()
  else
    let gam ← extractGamma hcov
    let mvarId ← getMainGoal
    let (b1, b2) ← mvarId.withContext (do
      let ty ← whnf V
      let args := ty.getAppArgs
      if h : args.size > 1 then
        match args[1]! with
        | .app h2 t =>
          match t with
          | .app h3 t2 =>
            if h2.getAppFn.constName? == some ``List.cons &&
                h3.getAppFn.constName? == some ``List.cons &&
                t2.getAppFn.constName? == some ``List.nil then
              let a1 := h2.getAppArgs
              let a2 := h3.getAppArgs
              if h1 : a1.size > 0 then
                if h2 : a2.size > 0 then
                  pure (a1[a1.size - 1]!, a2[a2.size - 1]!)
                else throwError "fmonPfx2Ext: cons args"
              else throwError "fmonPfx2Ext: cons args"
            else throwError "fmonPfx2Ext: bs not 2-branch"
          | _ => throwError "fmonPfx2Ext: bs not 2-branch"
        | _ => throwError "fmonPfx2Ext: bs not list"
      else throwError "fmonPfx2Ext: bad ext")
    let t01 : Expr ← mvarId.withContext
      (pure (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b1)))
    let t02 : Expr ← mvarId.withContext
      (pure (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b2)))
    let t01W ← mvarId.withContext (whnf t01)
    let t02W ← mvarId.withContext (whnf t02)
    -- literal label/sort syntax for both branches
    let (l1, s1, t01S, l2, s2, t02S, bsS) ← mvarId.withContext (do
      let ty ← whnf V
      let bsE := ty.getAppArgs[1]!
      let l1W ← whnf (Expr.proj ``Prod 0 b1)
      let s1W ← whnf (Expr.proj ``Prod 0 (Expr.proj ``Prod 1 b1))
      let l2W ← whnf (Expr.proj ``Prod 0 b2)
      let s2W ← whnf (Expr.proj ``Prod 0 (Expr.proj ``Prod 1 b2))
      let bsW ← whnf bsE
      pure (← Lean.Elab.Term.exprToSyntax l1W, ← Lean.Elab.Term.exprToSyntax s1W,
        ← Lean.Elab.Term.exprToSyntax t01W, ← Lean.Elab.Term.exprToSyntax l2W,
        ← Lean.Elab.Term.exprToSyntax s2W, ← Lean.Elab.Term.exprToSyntax t02W,
        ← Lean.Elab.Term.exprToSyntax bsW))
    -- split branch1 status, then branch2 status in each subgoal.
    -- `byCases` returns each introduced hyp directly (`fvarId`).
    let exProp1 := mkAppN (.const ``Ex []) #[t01W, gam]
    let (m1T, m1F) ← mvarId.byCases exProp1
    let exProp2 := mkAppN (.const ``Ex []) #[t02W, gam]
    setGoals [m1T.mvarId]
    let hEx1 := m1T.fvarId
    let nmEx1 ← renameFresh hEx1 `hEx1
    let mvarT ← getMainGoal
    let (mTT, mTF) ← mvarT.byCases exProp2
    -- (T,T): both eligible; fire hcov/hall twice, recurse both, 2-pin.
    setGoals [mTT.mvarId]
    let hEx2TT := mTT.fvarId
    let nmEx2TT ← renameFresh hEx2TT `hEx2
    let nmCov ← renameFresh hcov `hcov
    let nmHall ← renameFresh hall `hall
    let keptF ← findKeptF hke
    evalTactic (← `(tactic|
      (have hmemBs1 : ($l1, $s1, $t01S) ∈ $bsS := List.mem_cons_self
       have hmemBs2 : ($l2, $s2, $t02S) ∈ $bsS :=
         List.mem_cons_of_mem _ List.mem_cons_self
       obtain ⟨T1, hmemK1⟩ :=
         $(mkIdent nmCov) $l1 $s1 $t01S hmemBs1 $(mkIdent nmEx1)
       obtain ⟨T2, hmemK2⟩ :=
         $(mkIdent nmCov) $l2 $s2 $t02S hmemBs2 $(mkIdent nmEx2TT)
       have hfc1 := $(mkIdent nmHall) $t01S T1 $l1 $s1 hmemBs1 hmemK1
       have hfc2 := $(mkIdent nmHall) $t02S T2 $l2 $s2 hmemBs2 hmemK2)))
    -- invert + recurse both fchildren (grounds T1/T2 at base leaves)
    let mvarC ← getMainGoal
    let hfcs ← mvarC.withContext (do
      let lctx ← getLCtx
      let mut acc : List FVarId := []
      for decl in lctx do
        if decl.isImplementationDetail then continue
        if decl.userName.toString.startsWith "hfc" then
          acc := decl.fvarId :: acc
      match acc with
      | [_, _] => pure acc
      | _ => throwError "expected two hfc hyps")
    for hfcF in hfcs do
      invertRecurseFchild hfcF
    -- 2-pin kept and close (skips silently if already closed)
    pinTwoExt l1 s1 t01S l2 s2 t02S hkey hke hnd keptF
    -- (T,F): only branch1 eligible; singleton pin (other branch is b2).
    setGoals [mTF.mvarId]
    let hEx1TF := m1T.fvarId
    closeSingleExtBranch l1 s1 t01S bsS l2 s2 t02S true hcov hall hEx1TF
      hkey hnd hke keptF
    -- branch1 False subtree: split branch2; (F,T) singleton, (F,F) empty.
    setGoals [m1F.mvarId]
    let mvarF ← getMainGoal
    let (mFT, mFF) ← mvarF.byCases exProp2
    setGoals [mFT.mvarId]
    let hEx2FT := mFT.fvarId
    closeSingleExtBranch l2 s2 t02S bsS l1 s1 t01S false hcov hall hEx2FT
      hkey hnd hke keptF
    setGoals [mFF.mvarId]
    let nmKeyF ← renameFresh hkey `hkey
    let nmKeF ← renameFresh hke `hke
    let keptFF ← findKeptF hke
    let nmKeptF ← renameFresh keptFF `kept
    let mvarFF ← getMainGoal
    let closedFF ← mvarFF.withContext (do
      try
        evalTactic (← `(tactic|
          (have hempty : $(mkIdent nmKeptF) = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            rintro ⟨l, s, T1⟩ hx
            obtain ⟨T0, hmemBs, hEx⟩ := $(mkIdent nmKeyF) l s T1 hx
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
            rcases hmemBs with h | h
            · have h1 : _ = _ := congrArg Prod.fst h
              have h2 : _ = _ :=
                congrArg (fun t : Lab × DataSort × SessionType => t.2.1) h
              have h3 : _ = _ :=
                congrArg (fun t : Lab × DataSort × SessionType => t.2.2) h
              simp only at h1 h2 h3
              subst h1; subst h2; subst h3
              exact absurd hEx (by assumption)
            · have h1 : _ = _ := congrArg Prod.fst h
              have h2 : _ = _ :=
                congrArg (fun t : Lab × DataSort × SessionType => t.2.1) h
              have h3 : _ = _ :=
                congrArg (fun t : Lab × DataSort × SessionType => t.2.2) h
              simp only at h1 h2 h3
              subst h1; subst h2; subst h3
              exact absurd hEx (by assumption)
           (first | contradiction | simp_all))))
        pure true
      catch _ => pure false)
    if !closedFF then throwError "fmonPfx2Ext (F,F): not closed"
    pure ()

/-- Ext pfx dispatcher: route 1-branch to `fmonPfx1`, 2-branch to
    `fmonPfx2Ext` based on the concrete branch-list shape. -/
partial def fmonPfxExtDisp (V : Expr) (hall hnd hkey hcov hke : FVarId) :
    TacticM Unit := do
  let mvarId ← getMainGoal
  let n ← mvarId.withContext (do
    let ty ← whnf V
    let args := ty.getAppArgs
    if _ : args.size > 1 then
      match args[1]! with
      | .app h2 t =>
        if h2.getAppFn.constName? != some ``List.cons then pure 0
        else if t.getAppFn.constName? == some ``List.nil then pure 1
        else
          match t with
          | .app h3 t2 =>
            if h3.getAppFn.constName? == some ``List.cons &&
                t2.getAppFn.constName? == some ``List.nil then pure 2
            else pure 0
          | _ => pure 0
      | _ => pure 0
    else pure 0)
  if n == 1 then fmonPfx1 V hall hnd hkey hcov hke false
  else if n == 2 then fmonPfx2Ext V hall hnd hkey hcov hke
  else throwError "fmonPfxExt: bs not 1-or-2-branch"

/-- Single eligible int branch against a 2-branch list: mirror of
    `closeSingleExtBranch` with 4-tuples, `int_key`, and
    `kept_int_singleton`. -/
partial def closeSingleIntBranch
    (rStx lStx sStx t0Stx bsStx or2 ol2 os2 ot2 : Lean.Term)
    (thisIsLeft : Bool)
    (hcov hall hEx hkey hnd hke keptF : FVarId) : TacticM Unit := do
  let nmCov ← renameFresh hcov `hcov
  let nmHall ← renameFresh hall `hall
  let nmEx ← renameFresh hEx `hEx
  let memPf : Lean.Term ← if thisIsLeft then `(List.mem_cons_self)
    else `(List.mem_cons_of_mem _ List.mem_cons_self)
  evalTactic (← `(tactic|
    (have hmemBs : ($rStx, $lStx, $sStx, $t0Stx) ∈ $bsStx := $memPf
     obtain ⟨T1, hmemK⟩ :=
       $(mkIdent nmCov) $rStx $lStx $sStx $t0Stx hmemBs $(mkIdent nmEx)
     have hfc :=
       $(mkIdent nmHall) $t0Stx T1 $rStx $lStx $sStx hmemBs hmemK)))
  let mvarC ← getMainGoal
  let hfcF ← mvarC.withContext (do
    let lctx ← getLCtx
    let mut found : Option FVarId := none
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if decl.userName.toString.startsWith "hfc" then
        found := some decl.fvarId
        break
    match found with
    | some f => pure f
    | none => throwError "no hfc hyp")
  let subC ← mvarC.withContext (mvarC.cases hfcF)
  for sgC in subC do
    setGoals [sgC.mvarId]
    if sgC.ctorName == some ``fchild.fc_fold then
      let fsC := (sgC.fields.filterMap (fun e => e.fvarId?)).toList
      let mvarM ← getMainGoal
      let hmem ← mvarM.withContext (do
        let mut found : Option FVarId := none
        for f in fsC do
          let ty ← inferType (.fvar f)
          if hasConstIn ty ``Membership.mem || hasConstIn ty ``List.Mem then
            found := some f
            break
        match found with
        | some h => pure h
        | none => throwError "no mem in fold")
      let subM ← mvarM.withContext (mvarM.cases hmem)
      if subM.size = 0 then pure ()
      else throwError "fchild fold non-empty G: manual"
    else if sgC.ctorName == some ``fchild.fc_go then
      let fsG := (sgC.fields.filterMap (fun e => e.fvarId?)).toList
      let mvarG ← getMainGoal
      let hfmon ← mvarG.withContext (do
        let mut found : Option FVarId := none
        for f in fsG do
          let ty ← inferType (.fvar f)
          if (stripForalls ty).getAppFn.constName? == some ``fmon then
            found := some f
            break
        match found with
        | some h => pure h
        | none => throwError "no fmon in go")
      let _ ← recurseFmon hfmon
      let gs ← getGoals
      if gs.isEmpty then return ()
      let hmemK ← findMemKept keptF
      let mvarQ ← getMainGoal
      let t1F ← mvarQ.withContext (do
        let ty ← inferType (.fvar hmemK)
        let rec findT : Expr → Option FVarId
          | .fvar f => if f == keptF then none else some f
          | .app f a => match findT f with | some g => some g | none => findT a
          | .forallE _ d b _ => match findT d with | some g => some g | none => findT b
          | .lam _ d b _ => match findT d with | some g => some g | none => findT b
          | _ => none
        match findT ty with
        | some f => pure f
        | none => throwError "no T1")
      let nmT1 ← renameFresh t1F `T1
      let nmKept ← renameFresh keptF `kept
      let nmKey2 ← renameFresh hkey `hkey
      let nmNd ← renameFresh hnd `hnd
      let nmKe2 ← renameFresh hke `hke
      let nmMemK ← renameFresh hmemK `hmemK
      let pinB ← `(tacticSeq|
        have h1 : _ = _ := congrArg Prod.fst h
        have h2 : _ = _ :=
          congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.1) h
        have h3 : _ = _ :=
          congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.1) h
        simp only at h1 h2 h3
        rw [h1, h2, h3])
      let contraB ← `(tacticSeq|
        have e : _ = _ :=
          congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.2) h
        simp only at e
        rw [e] at hEx
        exact absurd hEx (by assumption))
      let (firstB, secondB) :=
        if thisIsLeft then (pinB, contraB) else (contraB, pinB)
      evalTactic (← `(tactic|
        (have hallk : ∀ x ∈ $(mkIdent nmKept),
            (x.1, x.2.1, x.2.2.1) = ($rStx, $lStx, $sStx) := by
          intro x hx
          obtain ⟨T0, hmemBs, hEx⟩ := $(mkIdent nmKey2) x.1 x.2.1
            x.2.2.1 x.2.2.2 hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
          rcases hmemBs with h | h
          · $firstB
          · $secondB
         have hpin : $(mkIdent nmKept) =
            [($rStx, $lStx, $sStx, $(mkIdent nmT1))] := kept_int_singleton
              (b := ($rStx, $lStx, $sStx, $t0Stx)) $(mkIdent nmKe2)
              $(mkIdent nmNd) $(mkIdent nmMemK) hallk
         rw [hpin]
         fmon_close)))
    else throwError "unhandled fchild case"
  pure ()

/-- 2-pin int `kept` via `kept_int_two_ee_disj` and close. -/
partial def pinTwoInt (r1 l1 s1 t01S r2 l2 s2 t02S : Lean.Term)
    (hkey hke hnd keptF : FVarId) : TacticM Unit := do
  let gs ← getGoals
  if gs.isEmpty then return ()
  -- hmemK1/hmemK2 were introduced by the creation block's obtains
  -- (branch1 then branch2); look up by name for order safety.
  let hmemK1 ← findNamed `hmemK1
  let hmemK2 ← findNamed `hmemK2
  let nmM1 ← renameFresh hmemK1 `hmemK1
  let nmM2 ← renameFresh hmemK2 `hmemK2
  let nmKept ← renameFresh keptF `kept
  let nmKey ← renameFresh hkey `hkey
  let nmKe ← renameFresh hke `hke
  let nmNd ← renameFresh hnd `hnd
  evalTactic (← `(tactic|
    (have hallk2 : ∀ x ∈ $(mkIdent nmKept),
        (x.1, x.2.1) = ($r1, $l1) ∨ (x.1, x.2.1) = ($r2, $l2) := by
      intro x hx
      obtain ⟨T0, hmemBs, hExT0⟩ := $(mkIdent nmKey) x.1 x.2.1
        x.2.2.1 x.2.2.2 hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
      rcases hmemBs with h | h
      · left
        have h1 : _ = _ := congrArg Prod.fst h
        have h2 : _ = _ :=
          congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.1) h
        simp only at h1 h2
        have hh : (x.1, x.2.1) = ($r1, $l1) := by rw [h1, h2]
        exact hh
      · right
        have h1 : _ = _ := congrArg Prod.fst h
        have h2 : _ = _ :=
          congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.1) h
        simp only at h1 h2
        have hh : (x.1, x.2.1) = ($r2, $l2) := by rw [h1, h2]
        exact hh
     have hne12 : (($r1, $l1) : Role × Lab) ≠ ($r2, $l2) := by decide
     have hpin := kept_int_two_ee_disj (b1 := ($r1, $l1, $s1, $t01S))
       (b2 := ($r2, $l2, $s2, $t02S)) $(mkIdent nmKe) $(mkIdent nmNd)
       $(mkIdent nmM1) $(mkIdent nmM2) hallk2 hne12
     rcases hpin with hpin | hpin <;> rw [hpin] <;> fmon_close)))

/-- 2-branch int pfx handler: mirror of `fmonPfx2Ext` with 4-tuples. -/
partial def fmonPfx2Int (V : Expr) (hall hnd hkey hcov hke : FVarId) :
    TacticM Unit := do
  let mvarId0 ← getMainGoal
  let closed ← mvarId0.withContext (do
    try
      evalTactic (← `(tactic| contradiction))
      pure true
    catch _ => pure false)
  if closed then pure ()
  else
    let gam ← extractGamma hcov
    let mvarId ← getMainGoal
    let (b1, b2) ← mvarId.withContext (do
      let ty ← whnf V
      let args := ty.getAppArgs
      if h : args.size > 0 then
        match args[args.size - 1]! with
        | .app h2 t =>
          match t with
          | .app h3 t2 =>
            if h2.getAppFn.constName? == some ``List.cons &&
                h3.getAppFn.constName? == some ``List.cons &&
                t2.getAppFn.constName? == some ``List.nil then
              let a1 := h2.getAppArgs
              let a2 := h3.getAppArgs
              if h1 : a1.size > 0 then
                if h2 : a2.size > 0 then
                  pure (a1[a1.size - 1]!, a2[a2.size - 1]!)
                else throwError "fmonPfx2Int: cons args"
              else throwError "fmonPfx2Int: cons args"
            else throwError "fmonPfx2Int: bs not 2-branch"
          | _ => throwError "fmonPfx2Int: bs not 2-branch"
        | _ => throwError "fmonPfx2Int: bs not list"
      else throwError "fmonPfx2Int: bad int")
    let t01 : Expr ← mvarId.withContext (do
      pure (Expr.proj ``Prod 1
        (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b1))))
    let t02 : Expr ← mvarId.withContext (do
      pure (Expr.proj ``Prod 1
        (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b2))))
    let t01W ← mvarId.withContext (whnf t01)
    let t02W ← mvarId.withContext (whnf t02)
    let (r1, l1, s1, t01S, r2, l2, s2, t02S, bsS) ← mvarId.withContext (do
      let ty ← whnf V
      let bsE := ty.getAppArgs[ty.getAppArgs.size - 1]!
      let r1W ← whnf (Expr.proj ``Prod 0 b1)
      let l1W ← whnf (Expr.proj ``Prod 0 (Expr.proj ``Prod 1 b1))
      let s1W ← whnf (Expr.proj ``Prod 0
        (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b1)))
      let r2W ← whnf (Expr.proj ``Prod 0 b2)
      let l2W ← whnf (Expr.proj ``Prod 0 (Expr.proj ``Prod 1 b2))
      let s2W ← whnf (Expr.proj ``Prod 0
        (Expr.proj ``Prod 1 (Expr.proj ``Prod 1 b2)))
      let bsW ← whnf bsE
      pure (← Lean.Elab.Term.exprToSyntax r1W,
        ← Lean.Elab.Term.exprToSyntax l1W,
        ← Lean.Elab.Term.exprToSyntax s1W,
        ← Lean.Elab.Term.exprToSyntax t01W,
        ← Lean.Elab.Term.exprToSyntax r2W,
        ← Lean.Elab.Term.exprToSyntax l2W,
        ← Lean.Elab.Term.exprToSyntax s2W,
        ← Lean.Elab.Term.exprToSyntax t02W,
        ← Lean.Elab.Term.exprToSyntax bsW))
    let exProp1 := mkAppN (.const ``Ex []) #[t01W, gam]
    let (m1T, m1F) ← mvarId.byCases exProp1
    let exProp2 := mkAppN (.const ``Ex []) #[t02W, gam]
    setGoals [m1T.mvarId]
    let hEx1 := m1T.fvarId
    let nmEx1 ← renameFresh hEx1 `hEx1
    let mvarT ← getMainGoal
    let (mTT, mTF) ← mvarT.byCases exProp2
    -- (T,T): both eligible; fire hcov/hall twice, recurse both, 2-pin.
    setGoals [mTT.mvarId]
    let hEx2TT := mTT.fvarId
    let nmEx2TT ← renameFresh hEx2TT `hEx2
    let nmCov ← renameFresh hcov `hcov
    let nmHall ← renameFresh hall `hall
    let keptF ← findKeptF hke
    evalTactic (← `(tactic|
      (have hmemBs1 : ($r1, $l1, $s1, $t01S) ∈ $bsS :=
        List.mem_cons_self
       have hmemBs2 : ($r2, $l2, $s2, $t02S) ∈ $bsS :=
         List.mem_cons_of_mem _ List.mem_cons_self
       obtain ⟨T1, hmemK1⟩ :=
         $(mkIdent nmCov) $r1 $l1 $s1 $t01S hmemBs1 $(mkIdent nmEx1)
       obtain ⟨T2, hmemK2⟩ :=
         $(mkIdent nmCov) $r2 $l2 $s2 $t02S hmemBs2 $(mkIdent nmEx2TT)
       have hfc1 :=
         $(mkIdent nmHall) $t01S T1 $r1 $l1 $s1 hmemBs1 hmemK1
       have hfc2 :=
         $(mkIdent nmHall) $t02S T2 $r2 $l2 $s2 hmemBs2 hmemK2)))
    let mvarC ← getMainGoal
    let hfcs ← mvarC.withContext (do
      let lctx ← getLCtx
      let mut acc : List FVarId := []
      for decl in lctx do
        if decl.isImplementationDetail then continue
        if decl.userName.toString.startsWith "hfc" then
          acc := decl.fvarId :: acc
      match acc with
      | [_, _] => pure acc
      | _ => throwError "expected two hfc hyps")
    for hfcF in hfcs do
      invertRecurseFchild hfcF
    pinTwoInt r1 l1 s1 t01S r2 l2 s2 t02S hkey hke hnd keptF
    -- (T,F): only branch1 eligible; singleton pin (other branch is b2).
    setGoals [mTF.mvarId]
    let hEx1TF := m1T.fvarId
    closeSingleIntBranch r1 l1 s1 t01S bsS r2 l2 s2 t02S true hcov hall
      hEx1TF hkey hnd hke keptF
    -- branch1 False subtree: split branch2; (F,T) singleton, (F,F) empty.
    setGoals [m1F.mvarId]
    let mvarF ← getMainGoal
    let (mFT, mFF) ← mvarF.byCases exProp2
    setGoals [mFT.mvarId]
    let hEx2FT := mFT.fvarId
    closeSingleIntBranch r2 l2 s2 t02S bsS r1 l1 s1 t01S false hcov hall
      hEx2FT hkey hnd hke keptF
    setGoals [mFF.mvarId]
    let nmKeyF ← renameFresh hkey `hkey
    let nmKeF ← renameFresh hke `hke
    let keptFF ← findKeptF hke
    let nmKeptF ← renameFresh keptFF `kept
    let mvarFF ← getMainGoal
    let closedFF ← mvarFF.withContext (do
      try
        evalTactic (← `(tactic|
          (have hempty : $(mkIdent nmKeptF) = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            rintro ⟨r, l, s, T1⟩ hx
            obtain ⟨T0, hmemBs, hEx⟩ := $(mkIdent nmKeyF) r l s T1 hx
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmemBs
            rcases hmemBs with h | h
            · have h1 : _ = _ := congrArg Prod.fst h
              have h2 : _ = _ :=
                congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.1)
                  h
              have h3 : _ = _ :=
                congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.1)
                  h
              have h4 : _ = _ :=
                congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.2)
                  h
              simp only at h1 h2 h3 h4
              subst h1; subst h2; subst h3; subst h4
              exact absurd hEx (by assumption)
            · have h1 : _ = _ := congrArg Prod.fst h
              have h2 : _ = _ :=
                congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.1)
                  h
              have h3 : _ = _ :=
                congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.1)
                  h
              have h4 : _ = _ :=
                congrArg (fun t : Role × Lab × DataSort × SessionType => t.2.2.2)
                  h
              simp only at h1 h2 h3 h4
              subst h1; subst h2; subst h3; subst h4
              exact absurd hEx (by assumption)
           (first | contradiction | simp_all))))
        pure true
      catch _ => pure false)
    if !closedFF then throwError "fmonPfx2Int (F,F): not closed"
    pure ()

/-- Int pfx dispatcher: route 1-branch to `fmonPfx1Int`, 2-branch to
    `fmonPfx2Int` based on the concrete branch-list shape. -/
partial def fmonPfxIntDisp (V : Expr) (hall hnd hkey hcov hke : FVarId) :
    TacticM Unit := do
  let mvarId ← getMainGoal
  let n ← mvarId.withContext (do
    let ty ← whnf V
    let args := ty.getAppArgs
    if _ : args.size > 0 then
      match args[args.size - 1]! with
      | .app h2 t =>
        if h2.getAppFn.constName? != some ``List.cons then pure 0
        else if t.getAppFn.constName? == some ``List.nil then pure 1
        else
          match t with
          | .app h3 t2 =>
            if h3.getAppFn.constName? == some ``List.cons &&
                t2.getAppFn.constName? == some ``List.nil then pure 2
            else pure 0
          | _ => pure 0
      | _ => pure 0
    else pure 0)
  if n == 1 then fmonPfx1Int V hall hnd hkey hcov hke
  else if n == 2 then fmonPfx2Int V hall hnd hkey hcov hke
  else throwError "fmonPfxInt: bs not 1-or-2-branch"

/-- Recursor: revert dependents, UnfoldStar invert, normalize, recurse. -/
partial def fmonRecTac (hS hNF hsub : FVarId) : TacticM Unit := do
  let nmNF ← renameFresh hNF `hNF
  evalTactic (← `(tactic| revert $(mkIdent nmNF)))
  let nmSub ← renameFresh hsub `hsub
  evalTactic (← `(tactic| revert $(mkIdent nmSub)))
  let mvarId ← getMainGoal
  let hS' ← mvarId.withContext (do
    let lctx ← getLCtx
    let mut found : Option FVarId := none
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let ty ← whnf (← inferType decl.toExpr)
      if ty.getAppFn.constName? == some ``UnfoldStar then
        found := some decl.fvarId
        break
    match found with
    | some f => pure f
    | none => throwError "no UnfoldStar hyp")
  let subgoals ← mvarId.withContext (mvarId.cases hS')
  for sg in subgoals do
    setGoals [sg.mvarId]
    let gm ← getMainGoal
    if sg.ctorName == some ``UnfoldStar.refl then
      evalTactic (← `(tactic| intro _ _))
      let mvarId2 ← getMainGoal
      -- if T is tRec, hNF : False → contradiction closes (refl impossible).
      -- else (headNF) recurse noRec (fm_rec prunes, base/pfx handle).
      let closed ← mvarId2.withContext (do
        try
          evalTactic (← `(tactic| contradiction))
          pure true
        catch _ => pure false)
      if !closed then
        mvarId2.withContext do
          let lctx ← getLCtx
          let mut found : Option FVarId := none
          for decl in lctx do
            if decl.isImplementationDetail then continue
            let ty ← whnf (← inferType decl.toExpr)
            if ty.getAppFn.constName? == some ``fmon then
              found := some decl.fvarId
              break
          match found with
          | some hf => fmonInvMainAux hf false
          | none => throwError "no fmon hyp after UnfoldStar"
    else if sg.ctorName == some ``UnfoldStar.step then
      -- intro reverted hyps; find h1 (Unfold1), hrest (UnfoldStar), hsub (fmon)
      evalTactic (← `(tactic| intro _ _))
      let mvarId2 ← getMainGoal
      let (h1, hrest, hsub) ← mvarId2.withContext (do
        let lctx ← getLCtx
        let mut h1O : Option FVarId := none
        let mut hrestO : Option FVarId := none
        let mut hsubO : Option FVarId := none
        for decl in lctx do
          if decl.isImplementationDetail then continue
          let ty ← whnf (← inferType decl.toExpr)
          match ty.getAppFn.constName? with
          | some ``Unfold1 => h1O := some decl.fvarId
          | some ``UnfoldStar => hrestO := some decl.fvarId
          | some ``fmon => hsubO := some decl.fvarId
          | _ => pure ()
        match h1O, hrestO, hsubO with
        | some a, some b, some c => pure (a, b, c)
        | _, _, _ => throwError "rec step: hyps not found")
      -- invert h1 (Unfold1, single ctor) to determine U, then normalize
      let mvarIdU ← getMainGoal
      let subU ← mvarIdU.withContext (mvarIdU.cases h1)
      for sgU in subU do
        setGoals [sgU.mvarId]
      -- re-find hrest (FVar may have changed) and normalize U via simpa
      let mvarIdN ← getMainGoal
      let mvarIdN ← getMainGoal
      let hrest2 ← mvarIdN.withContext (do
        let lctx ← getLCtx
        let mut found : Option FVarId := none
        for decl in lctx do
          if decl.isImplementationDetail then continue
          let ty ← whnf (← inferType decl.toExpr)
          if ty.getAppFn.constName? == some ``UnfoldStar then
            found := some decl.fvarId
            break
        match found with
        | some f => pure f
        | none => throwError "no UnfoldStar hyp after Unfold1")
      -- re-find hsub similarly
      let mvarIdS ← getMainGoal
      let hsub2 ← mvarIdS.withContext (do
        let lctx ← getLCtx
        let mut found : Option FVarId := none
        for decl in lctx do
          if decl.isImplementationDetail then continue
          let ty ← whnf (← inferType decl.toExpr)
          if ty.getAppFn.constName? == some ``fmon then
            found := some decl.fvarId
            break
        match found with
        | some f => pure f
        | none => throwError "no fmon hyp after Unfold1")
      let hrestN ← simpaNormalizeSubst hrest2
      -- revert hsub (stale H), cases normalized hrest, intro, recurse
      let nm ← renameFresh hsub2 `hsub
      evalTactic (← `(tactic| revert $(mkIdent nm)))
      let mvarId3 ← getMainGoal
      let sub2 ← mvarId3.withContext (mvarId3.cases hrestN)
      for sg2 in sub2 do
        setGoals [sg2.mvarId]
        if sg2.ctorName == some ``UnfoldStar.refl then
          evalTactic (← `(tactic| intro _))
          let mvarId4 ← getMainGoal
          mvarId4.withContext do
            let lctx ← getLCtx
            let mut found : Option FVarId := none
            for decl in lctx do
              if decl.isImplementationDetail then continue
              let ty ← whnf (← inferType decl.toExpr)
              if ty.getAppFn.constName? == some ``fmon then
                found := some decl.fvarId
                break
            match found with
            | some hf => fmonInvMain hf
            | none => throwError "no fmon hyp after UnfoldStar"
        else if sg2.ctorName == some ``UnfoldStar.step then
          -- nested unfold: intro reverted hsub and loop
          evalTactic (← `(tactic| intro _))
          fmonStepLoop 5
        else throwError "unhandled nested UnfoldStar"
    else throwError "unhandled UnfoldStar case"
  pure ()
end

elab "fmon_inv_auto" hf:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? hf.getId | throwError "hyp not found"
    fmonInvMain decl.fvarId

elab "ground_gamma" he:ident : tactic => do
  groundGamma he.getId
