import Nest.SessionUtils

/-!
# PruneFunctions: fuel-free prune functions.

Fuel-free session-type prune functions: existence checks (`pruneFirstInputHas`,
`pruneHasInt/Ext`), the pruning transformation (`pruneFirstInputGo`,
`pruneGoInt/Ext`), and the entry point `pruneFirstInput`. Used by the NoRec
drain/prune chain; the fuelled `prune*Deep*` variants live in `Nest.NetworkLTS`.
-/

mutual
/-- Existence check for `pruneFirstInput`: is there an `externalChoice p`
    offering `(lab, S)` reachable by traversing only choices not involving
    `p` (internal branches with sender `≠ p`, external choices with owner
    `≠ p`; `tRec` bodies traversed structurally, `tEnd`/`tVar` contribute
    nothing)? -/
def pruneFirstInputHas (p : Role) (lab : Lab) (S : DataSort) :
    SessionType → Bool
  | .tEnd => false
  | .tVar _ => false
  | .tRec _ B => pruneFirstInputHas p lab S B
  | .internalChoice branches => pruneHasInt p lab S branches
  | .externalChoice q branches =>
    if q == p then
      branches.any (fun b => match b with
        | (l, S', _) => l == lab && S' == S)
    else pruneHasExt p lab S branches

/-- List traversal for `pruneFirstInputHas` over internal branches
    (skipping `p`-sender branches). -/
def pruneHasInt (p : Role) (lab : Lab) (S : DataSort) :
    List (Role × Lab × DataSort × SessionType) → Bool
  | [] => false
  | (q, _, _, T') :: rest =>
    ((q != p && pruneFirstInputHas p lab S T') || pruneHasInt p lab S rest)

/-- List traversal for `pruneFirstInputHas` over non-`p` external
    branch targets. -/
def pruneHasExt (p : Role) (lab : Lab) (S : DataSort) :
    List (Lab × DataSort × SessionType) → Bool
  | [] => false
  | (_, _, T') :: rest =>
    (pruneFirstInputHas p lab S T' || pruneHasExt p lab S rest)
end
mutual
/-- Transformation for `pruneFirstInput`: resolve every reachable
    `externalChoice p` (reachability as in `pruneFirstInputHas`) to its
    `(lab, S)` continuation if present, else `tEnd`. Replacements are
    inserted as-is (no recursion into them); everything unreachable
    (including `p`-involving branches) is kept unchanged. -/
def pruneFirstInputGo (p : Role) (lab : Lab) (S : DataSort) :
    SessionType → SessionType
  | .tEnd => .tEnd
  | .tVar X => .tVar X
  | .tRec X B => .tRec X (pruneFirstInputGo p lab S B)
  | .internalChoice branches => .internalChoice (pruneGoInt p lab S branches)
  | .externalChoice q branches =>
    if q == p then
      match branches.find? (fun b => match b with
          | (l, S', _) => l == lab && S' == S) with
      | some (_, _, T') => T'
      | none => .tEnd
    else .externalChoice q (pruneGoExt p lab S branches)

/-- List traversal for `pruneFirstInputGo` over internal branches
    (leaving `p`-sender branches unchanged). -/
def pruneGoInt (p : Role) (lab : Lab) (S : DataSort) :
    List (Role × Lab × DataSort × SessionType) →
      List (Role × Lab × DataSort × SessionType)
  | [] => []
  | (q, l, S', T') :: rest =>
    ((if q == p then (q, l, S', T')
      else (q, l, S', pruneFirstInputGo p lab S T')) :: pruneGoInt p lab S rest)

/-- List traversal for `pruneFirstInputGo` over non-`p` external
    branch targets. -/
def pruneGoExt (p : Role) (lab : Lab) (S : DataSort) :
    List (Lab × DataSort × SessionType) →
      List (Lab × DataSort × SessionType)
  | [] => []
  | (l, S', T') :: rest =>
    ((l, S', pruneFirstInputGo p lab S T') :: pruneGoExt p lab S rest)
end

/-- Prune the first input `msg = (p, lab, S)` from a session type `T`
    (no well-formedness needed): defined (as `some T'`) iff some
    `externalChoice p` reachable by traversing only choices not involving
    `p` offers the `(lab, S)` branch; in that case every such reachable
    `externalChoice p` is replaced by its `(lab, S)` continuation if
    present, else by `tEnd`. -/
def pruneFirstInput (T : SessionType) (msg : QueueMessage) :
    Option SessionType :=
  match msg with
  | QueueMessage.msg p lab S =>
    if pruneFirstInputHas p lab S T then
      some (pruneFirstInputGo p lab S T)
    else none
