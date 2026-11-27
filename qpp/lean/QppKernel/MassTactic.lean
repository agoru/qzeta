module

public import QppKernel.Mass
public meta import QppKernel.Mass
public meta import QppKernel.Tactic

/-!
# The tactic `qeq` on masses

On a goal `lhs = rhs` between expressions in masses (sum, product, division, inverse, powers by numerals, numerals;
other subterms are variables), `qeq` proves the goal by `MExpr.eq_of_check`: the kernel checks the identity of
counts `num lhs * den rhs = num rhs * den lhs` at a few points, as for counts. The atoms are written over one
common denominator (`MExpr.exists_common`), so `n` atoms give `n + 1` count variables.
-/

public section

namespace Qpp.Qeq

open Lean Meta Elab Tactic

/-- The expression of the masses that `e` denotes, its variables indices into the atoms. -/
meta partial def reifyMass (e : Expr) : StateT (Array Expr) MetaM MExpr := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← reifyMass a) (← reifyMass b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← reifyMass a) (← reifyMass b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => return .div (← reifyMass a) (← reifyMass b)
  | (``Inv.inv, #[_, _, a]) => return .inv (← reifyMass a)
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
    match (← instantiateMVars k).nat? with
    | some k => return .pow (← reifyMass a) k
    | none => return .var (← atom e)
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some (k + 1) => return .num k
    | _ => return .var (← atom e)
  | _ => return .var (← atom e)

meta def toMTerm : MExpr → Expr
  | .var i => mkApp (mkConst ``MExpr.var) (mkRawNatLit i)
  | .one => mkConst ``MExpr.one
  | .num n => mkApp (mkConst ``MExpr.num) (mkRawNatLit n)
  | .add a b => mkApp2 (mkConst ``MExpr.add) (toMTerm a) (toMTerm b)
  | .mul a b => mkApp2 (mkConst ``MExpr.mul) (toMTerm a) (toMTerm b)
  | .div a b => mkApp2 (mkConst ``MExpr.div) (toMTerm a) (toMTerm b)
  | .inv a => mkApp (mkConst ``MExpr.inv) (toMTerm a)
  | .pow a k => mkApp2 (mkConst ``MExpr.pow) (toMTerm a) (mkRawNatLit k)

/-- Close `lhs = rhs` (masses) by the identity of counts of its cross products, checked by the kernel. -/
meta def qeqMass (mode : Option Name) (g : MVarId) (lhs rhs : Expr) : MetaM Unit := g.withContext do
  let ((a, b), atoms) ← (do return (← reifyMass lhs, ← reifyMass rhs)).run #[]
  let (l, r) := MExpr.cross a b
  let some (_, m) := chooseCheck mode (atoms.size + 1) l r |
    throwError "qeq: the two sides differ; num(left) den(right) minus num(right) den(left), by monomials in the \
      common denominator x0 and the numerators x(i+1) of the atoms:{indentD (showDiff l r)}"
  let σ ← mkListLit (mkConst ``Mass) atoms.toList
  let rfl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  g.assign (mkApp5 (mkConst ``MExpr.eq_of_check) m σ (toMTerm a) (toMTerm b) rfl)

elab_rules : tactic
  | `(tactic| qeq%$tk $[$_]?) => do
    let mode := modeOf (← getRef)
    let _ := tk
    liftMetaFinishingTactic fun g => do
      let t := (← instantiateMVars (← g.getType)).consumeMData
      let some (ty, lhs, rhs) := t.eq? | throwUnsupportedSyntax
      unless ← isDefEq ty (mkConst ``Mass) do throwUnsupportedSyntax
      qeqMass mode g lhs rhs

end Qpp.Qeq
