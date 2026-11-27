module

public import QppKernel.Sparse
public meta import QppKernel.Sparse
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Offset

/-!
# The tactic `qeq`: an identity of counts by reflection

`qeq` closes a goal `lhs = rhs` between polynomial expressions in counts. It reads both sides as `CExpr` (the
subterms that are not sums, products, powers by a numeral, successors or numerals become variables) and chooses the
check (`chooseCheck`): at points (`CExpr.check`, radices the least powers of `2` above both sides at each point)
when the dense size `Π (deg_i + 1)` is small, by sparse normal forms (`CExpr.scheck`) otherwise; `qeq dense` and
`qeq sparse` force one. It proves the goal by `CExpr.eq_of_verify` applied to `Eq.refl true`: the kernel runs the
check, in binary.
The tactic evaluates the check first only to report a failure, with the monomials where the two sides differ; the
proof is checked by the kernel alone, with no `native_decide`; its axioms are those of `CExpr.eq_of_check`
(`propext`, `Classical.choice`, `Quot.sound`).
-/

public section

namespace Qpp.Qeq

open Lean Meta Elab Tactic

/-- A subterm read as a variable: its index among the atoms, added if it is new. -/
meta def atom (e : Expr) : StateT (Array Expr) MetaM Nat := do
  let atoms ← get
  for h : i in [:atoms.size] do
    if ← isDefEq atoms[i] e then return i
  set (atoms.push e)
  return atoms.size

/-- The expression of the counts that `e` denotes, its variables indices into the atoms. -/
meta partial def reify (e : Expr) : StateT (Array Expr) MetaM CExpr := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← reify a) (← reify b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← reify a) (← reify b)
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
    match (← instantiateMVars k).nat? with
    | some k => return .pow (← reify a) k
    | none => return .var (← atom e)
  | (``Count.succ, #[a]) => return .succ (← reify a)
  | (``Count.one, #[]) => return .one
  | (``Count.ofNatSucc, #[k]) =>
    match ← (evalNat (← instantiateMVars k)).run with
    | some k => return .num k
    | none => return .var (← atom e)
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some (k + 1) => return .num k
    | _ => return .var (← atom e)
  | _ => return .var (← atom e)

/-- The term of type `CExpr` for a value of `CExpr`. -/
meta def toTerm : CExpr → Expr
  | .var i => mkApp (mkConst ``CExpr.var) (mkRawNatLit i)
  | .one => mkConst ``CExpr.one
  | .num n => mkApp (mkConst ``CExpr.num) (mkRawNatLit n)
  | .succ a => mkApp (mkConst ``CExpr.succ) (toTerm a)
  | .add a b => mkApp2 (mkConst ``CExpr.add) (toTerm a) (toTerm b)
  | .mul a b => mkApp2 (mkConst ``CExpr.mul) (toTerm a) (toTerm b)
  | .pow a k => mkApp2 (mkConst ``CExpr.pow) (toTerm a) (mkRawNatLit k)

/-- The radices of the check: `R_i` the least power of `2` above both sides at `π_i`, as exponents of `2`. -/
meta def radices (n : Nat) (a b : CExpr) : List Nat := Id.run do
  let mut ks : Array Nat := #[]
  for i in [:n] do
    let R : Nat → Nat := fun k => 2 ^ ks.getD k 0
    let v := max (a.evalNat (point R i)) (b.evalNat (point R i))
    ks := ks.push (v.log2 + 1)
  return ks.toList

/-- The degree in the variable `i`. -/
meta def degIn (i : Nat) : CExpr → Nat
  | .var j => if i == j then 1 else 0
  | .one | .num _ => 0
  | .succ a => degIn i a
  | .add a b => max (degIn i a) (degIn i b)
  | .mul a b => degIn i a + degIn i b
  | .pow a k => k * degIn i a

/-- The dense size `Π (deg_i + 1)` of two expressions in `n` variables, or `cap + 1` if it is above `cap`. -/
meta def denseSize (n cap : Nat) (a b : CExpr) : Nat := Id.run do
  let mut s := 1
  for i in [:n] do
    s := s * (max (degIn i a) (degIn i b) + 1)
    if s > cap then return cap + 1
  return s

/-- The largest dense size checked at points (by timings: at `10^7` the two checks cost about the same). -/
meta def denseCap : Nat := 65536

/-- The term of a list of numerals `2 ^ k`. -/
meta def powersTerm (ks : List Nat) : Expr :=
  (ks.map fun k => mkApp2 (mkConst ``Nat.pow) (mkRawNatLit 2) (mkRawNatLit k)).foldr
    (fun k acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) k acc) (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))

/-- The check of `a = b` in `n` variables and its term: at points when the dense size is at most `denseCap`, by
normal forms otherwise; `mode` (`dense`, `sparse`) forces one. `none` when the check fails. -/
meta def chooseCheck (mode : Option Name) (n : Nat) (a b : CExpr) : Option (CheckBy × Expr) :=
  let dense := match mode with
    | some `dense => true
    | some _ => false
    | none => denseSize n denseCap a b ≤ denseCap
  let m : CheckBy × Expr :=
    if dense then
      let ks := radices n a b
      (.points (ks.map (2 ^ ·)), mkApp (mkConst ``CheckBy.points) (powersTerm ks))
    else
      let W := max a.deg b.deg + 1
      (.normal W n, mkApp2 (mkConst ``CheckBy.normal) (mkRawNatLit W) (mkRawNatLit n))
  if CExpr.verify m.1 a b then some m else none

/-! The monomials where two expressions differ, for the message of a failure (not part of the proof). -/

meta def monMul (m n : List Nat) : List Nat :=
  (List.range (max m.length n.length)).map fun i => m.getD i 0 + n.getD i 0

meta def collect (p : List (List Nat × Int)) : List (List Nat × Int) :=
  let rec ins (t : List Nat × Int) : List (List Nat × Int) → List (List Nat × Int)
    | [] => [t]
    | s :: q => if s.1 == t.1 then (s.1, s.2 + t.2) :: q else s :: ins t q
  (p.foldl (fun acc t => ins t acc) []).filter (·.2 != 0)

meta def polyMul (p q : List (List Nat × Int)) : List (List Nat × Int) :=
  collect (p.flatMap fun (m, c) => q.map fun (n, d) => (monMul m n, c * d))

meta def polyOf : CExpr → List (List Nat × Int)
  | .var i => [((List.replicate i 0) ++ [1], 1)]
  | .one => [([], 1)]
  | .num n => [([], n + 1)]
  | .succ a => collect (polyOf a ++ [([], 1)])
  | .add a b => collect (polyOf a ++ polyOf b)
  | .mul a b => polyMul (polyOf a) (polyOf b)
  | .pow a k => (List.range k).foldl (fun acc _ => polyMul acc (polyOf a)) [([], 1)]

meta def showDiff (a b : CExpr) : String :=
  let d := collect (polyOf a ++ (polyOf b).map fun (m, c) => (m, -c))
  let terms := d.take 8 |>.map fun (m, c) =>
    let xs := String.join ((m.zipIdx.filter (·.1 != 0)).map fun (e, v) => s!" x{v}^{e}")
    s!"{c}{xs}"
  ", ".intercalate terms ++ (if d.length > 8 then s!", ... ({d.length} monomials)" else "")

/-- The Braun tree of the entries `xs` (`Tree`), of type `ty`. -/
meta partial def treeOf (ty : Expr) (xs : Array Expr) : Expr :=
  if h : 0 < xs.size then
    let odds := (List.range xs.size).filter (· % 2 == 1) |>.map (xs[·]!)
    let evens := (List.range xs.size).filter (fun i => i % 2 == 0 && i != 0) |>.map (xs[·]!)
    mkApp4 (mkConst ``Tree.node) ty (treeOf ty odds.toArray) xs[0] (treeOf ty evens.toArray)
  else mkApp (mkConst ``Tree.nil) ty

/-- The values of the variables, `Tree.get 1 t` with the atoms in the Braun tree `t`, for `CExpr.eval`. -/
meta def envOf (atoms : Array Expr) : MetaM Expr := do
  let ty := mkConst ``Count
  return mkApp3 (mkConst ``Tree.get) ty (mkConst ``Count.one) (treeOf ty atoms)

/-- Close `lhs = rhs` (counts) by the check that `chooseCheck` picks, evaluated by the kernel. -/
meta def qeq (mode : Option Name) (g : MVarId) : MetaM Unit := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some (ty, lhs, rhs) := t.eq? | throwError "qeq: the goal is not an equation{indentExpr t}"
  unless ← isDefEq ty (mkConst ``Count) do throwError "qeq: the goal is not an equation of counts{indentExpr t}"
  let ((a, b), atoms) ← (do return (← reify lhs, ← reify rhs)).run #[]
  let some (_, m) := chooseCheck mode atoms.size a b |
    throwError "qeq: the two sides differ; left minus right, by monomials in the atoms x0 ... :{indentD (showDiff a b)}"
  let ρ ← envOf atoms
  let rfl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  g.assign (mkApp5 (mkConst ``CExpr.eq_of_verify) m ρ (toTerm a) (toTerm b) rfl)

/-- `qeq` closes an identity of polynomial expressions in counts; the kernel checks it at a few points or by
sparse normal forms. `qeq dense` and `qeq sparse` force the check. -/
syntax (name := qeqTac) "qeq" (ppSpace (&"dense" <|> &"sparse"))? : tactic

/-- The mode of a `qeq` call: `dense`, `sparse`, or none (the tactic chooses). -/
meta def modeOf (stx : Syntax) : Option Name :=
  match stx[1].getOptional? with
  | some m => some (Name.mkSimple m.getAtomVal)
  | none => none

elab_rules : tactic
  | `(tactic| qeq%$tk $[$_]?) => do
    let mode := modeOf (← getRef)
    let _ := tk
    liftMetaFinishingTactic fun g => do
      let t := (← instantiateMVars (← g.getType)).consumeMData
      match t.eq? with
      | some (ty, _, _) => unless ← isDefEq ty (mkConst ``Count) do throwUnsupportedSyntax
      | none => pure ()
      qeq mode g

end Qpp.Qeq
