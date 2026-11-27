module

public import QppKernel.Farkas
public meta import QppKernel.Farkas
public meta import QppKernel.MassTactic
public meta import Std.Data.HashMap
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `farkas`

`farkas [h₁, c₂ • h₂, ...]` closes `L < R` or `L ≤ R` between counts or between masses from hypotheses `aⱼ < bⱼ`,
`aⱼ ≤ bⱼ` or `aⱼ = bⱼ`, each taken `cⱼ` times (once with no coefficient); `farkas` alone uses no hypothesis. It
forms `A = Σ cⱼ aⱼ` and `B = Σ cⱼ bⱼ` with the proof of `A ≤ B` (or `A < B`), and computes the slack
`s = (R + A) - (L + B)` as a polynomial in the atoms; on masses, in the numerators of the atoms over a common
denominator, `s = num (R + A) * den (L + B) - num (L + B) * den (R + A)`. A negative monomial of the slack is an error, which
lists them. The proof is `CExpr.lt_of_check`, `MExpr.lt_of_check` or a variant with no slack, checked by the
kernel as `qeq` is; the polynomial arithmetic here only finds `s`.
-/

public section

namespace Qpp.Qeq

open Lean Meta Elab Tactic

/-- Polynomials with integer coefficients; a monomial is its array of exponents, with no trailing zero. -/
abbrev Poly := Std.HashMap (Array Nat) Int

meta def Poly.addTerm (p : Poly) (m : Array Nat) (c : Int) : Poly :=
  let c' := p.getD m 0 + c
  if c' == 0 then p.erase m else p.insert m c'

meta def Poly.add (p q : Poly) : Poly := q.fold (fun acc m c => acc.addTerm m c) p

meta def Poly.neg (p : Poly) : Poly := p.fold (fun acc m c => acc.insert m (-c)) {}

meta def monMulA (m n : Array Nat) : Array Nat :=
  (Array.range (max m.size n.size)).map fun i => m.getD i 0 + n.getD i 0

meta def Poly.mul (p q : Poly) : Poly :=
  p.fold (fun acc m c => q.fold (fun acc n d => acc.addTerm (monMulA m n) (c * d)) acc) {}

meta def Poly.const (c : Int) : Poly := ({} : Poly).addTerm #[] c

meta def Poly.ofCExpr : CExpr → Poly
  | .var i => ({} : Poly).insert ((Array.replicate i 0).push 1) 1
  | .one => Poly.const 1
  | .num n => Poly.const (n + 1)
  | .succ a => (Poly.ofCExpr a).addTerm #[] 1
  | .add a b => (Poly.ofCExpr a).add (Poly.ofCExpr b)
  | .mul a b => (Poly.ofCExpr a).mul (Poly.ofCExpr b)
  | .pow a k => (List.range k).foldl (fun acc _ => acc.mul (Poly.ofCExpr a)) (Poly.const 1)

/-- A monomial with a positive coefficient, as an expression. -/
meta def termOf (m : Array Nat) (c : Nat) : CExpr :=
  let vars := (m.zipIdx.filter (·.1 != 0)).toList.map fun (e, i) => if e == 1 then CExpr.var i else .pow (.var i) e
  match vars with
  | [] => .num (c - 1)
  | v :: vs =>
    let mon := vs.foldl .mul v
    if c == 1 then mon else .mul (.num (c - 1)) mon

/-- The sum of a nonempty array of expressions, as a balanced tree. -/
meta partial def sumOf (xs : Array CExpr) (lo hi : Nat) (dflt : CExpr := .one) : CExpr :=
  if hi ≤ lo + 1 then xs.getD lo dflt
  else .add (sumOf xs lo ((lo + hi) / 2) dflt) (sumOf xs ((lo + hi) / 2) hi dflt)

/-- A hypothesis `lhs < rhs` (strict) or `lhs ≤ rhs`, with its proof. -/
structure Hyp where
  lhs : Expr
  rhs : Expr
  strict : Bool
  proof : Expr

/-- `a < b`, `a ≤ b` or `a = b` (also `>` and `≥`) as `(a, b, kind)`, kind 2 for `<`, 1 for `≤`, 0 for `=`. -/
meta def relOf (t : Expr) : Option (Expr × Expr × Expr × Nat) :=
  match t.consumeMData.getAppFnArgs with
  | (``LT.lt, #[T, _, a, b]) => some (T, a, b, 2)
  | (``GT.gt, #[T, _, a, b]) => some (T, b, a, 2)
  | (``LE.le, #[T, _, a, b]) => some (T, a, b, 1)
  | (``GE.ge, #[T, _, a, b]) => some (T, b, a, 1)
  | (``Eq, #[T, a, b]) => some (T, a, b, 0)
  | _ => none

meta def hypOf (ns : Name) (T : Expr) (c? : Option Expr) (p : Expr) : MetaM Hyp := do
  let t ← instantiateMVars (← inferType p)
  let some (T', a, b, k) := relOf t | throwError "farkas: not an inequality{indentExpr t}"
  unless ← isDefEq T T' do throwError "farkas: an inequality of another type{indentExpr t}"
  let h : Hyp ← match k with
    | 2 => pure ⟨a, b, true, p⟩
    | 1 => pure ⟨a, b, false, p⟩
    | _ => pure ⟨a, b, false, ← mkAppM (ns ++ `le_of_eq) #[p]⟩
  let some c := c? | return h
  let lhs ← mkAppM ``HMul.hMul #[c, h.lhs]
  let rhs ← mkAppM ``HMul.hMul #[c, h.rhs]
  let proof ← mkAppM (ns ++ if h.strict then `mul_lt_mul_left else `mul_le_mul_left) #[c, h.proof]
  return ⟨lhs, rhs, h.strict, proof⟩

meta def Hyp.combine (ns : Name) (h g : Hyp) : MetaM Hyp := do
  let lhs ← mkAppM ``HAdd.hAdd #[h.lhs, g.lhs]
  let rhs ← mkAppM ``HAdd.hAdd #[h.rhs, g.rhs]
  let proof ← match h.strict, g.strict with
    | true, true => mkAppM (ns ++ `add_lt_of_lt_le) #[h.proof, ← mkAppM (ns ++ `le_of_lt) #[g.proof]]
    | true, false => mkAppM (ns ++ `add_lt_of_lt_le) #[h.proof, g.proof]
    | false, true => mkAppM (ns ++ `add_lt_of_le_lt) #[h.proof, g.proof]
    | false, false => mkAppM (ns ++ `add_le_le) #[h.proof, g.proof]
  return ⟨lhs, rhs, h.strict || g.strict, proof⟩

/-- The negative monomials of a slack, for the message of a failure. -/
meta def showNeg (name : Nat → MessageData) (p : Poly) : MessageData := Id.run do
  let neg := p.toList.filter (·.2 < 0)
  let shown := neg.take 8 |>.map fun (m, c) =>
    m.zipIdx.foldl (fun acc (e, i) => if e == 0 then acc else acc ++ m!" * " ++ name i ++ (if e == 1 then m!"" else m!"^{e}")) m!"{c}"
  let mut out := MessageData.joinSep shown m!", "
  if neg.length > 8 then out := out ++ m!", ... ({neg.length} negative monomials)"
  return out

meta def farkasCore (g : MVarId) (args : Array (Option Term × Term)) : TacticM Unit := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some (T, L, R, k) := relOf t | throwError "farkas: the goal is not `<` or `≤`{indentExpr t}"
  if k == 0 then throwError "farkas: the goal is an equation; use qeq"
  let mass ← if ← isDefEq T (mkConst ``Mass) then pure true
    else if ← isDefEq T (mkConst ``Count) then pure false
    else throwError "farkas: not an inequality of counts or of masses{indentExpr t}"
  let ns := if mass then ``Mass else ``Count
  let mut hyps : Array Hyp := #[]
  for (c?, h) in args do
    let c ← c?.mapM fun c => do instantiateMVars (← elabTerm c (some T))
    let p ← instantiateMVars (← elabTerm h none)
    hyps := hyps.push (← hypOf ns T c p)
  let one ← mkAppOptM ``OfNat.ofNat #[T, mkRawNatLit 1, none]
  let mut H : Hyp := ⟨one, one, false, ← mkAppM (ns ++ `le_refl) #[one]⟩
  match hyps.toList with
  | [] => pure ()
  | h :: hs =>
    H := h
    for h in hs do H ← H.combine ns h
  let strictGoal := k == 2
  let rfl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let leOfLt (p : Expr) : MetaM Expr := mkAppM (ns ++ `le_of_lt) #[p]
  let proof ← if mass then do
    let ((l, r, a, b), atoms) ← (do
      return (← reifyMass L, ← reifyMass R, ← reifyMass H.lhs, ← reifyMass H.rhs)).run #[]
    let (c1, c2) := MExpr.cross (.add r a) (.add l b)
    let slack := (Poly.ofCExpr c1).add (Poly.ofCExpr c2).neg
    let name (i : Nat) : MessageData :=
      if i == 0 then m!"den" else m!"num({atoms.getD (i - 1) (mkConst ``Unit)})"
    let σ ← mkListLit (mkConst ``Mass) atoms.toList
    let n := atoms.size + 1
    finish slack name n c1 c2 σ (toMTerm l) (toMTerm r) (toMTerm a) (toMTerm b)
      ``MExpr.lt_of_check ``MExpr.lt_of_check_tie ``MExpr.le_of_check_tie strictGoal H leOfLt rfl
  else do
    let ((l, r, a, b), atoms) ← (do
      return (← reify L, ← reify R, ← reify H.lhs, ← reify H.rhs)).run #[]
    let lhs : CExpr := .add r a
    let rhs : CExpr := .add l b
    let slack := (Poly.ofCExpr lhs).add (Poly.ofCExpr rhs).neg
    let name (i : Nat) : MessageData := m!"({atoms.getD i (mkConst ``Unit)})"
    let ρ ← envOf atoms
    finish slack name atoms.size lhs rhs ρ (toTerm l) (toTerm r) (toTerm a) (toTerm b)
      ``CExpr.lt_of_check ``CExpr.lt_of_check_tie ``CExpr.le_of_check_tie strictGoal H leOfLt rfl
  g.assign proof
where
  /-- The check and the proof, from the two sides `c1 = c2 + s` of the identity of counts. -/
  finish (slack : Poly) (name : Nat → MessageData) (n : Nat) (c1 c2 : CExpr) (vals l r a b : Expr)
      (ltName tieName leName : Name) (strictGoal : Bool) (H : Hyp) (leOfLt : Expr → MetaM Expr) (rfl : Expr) :
      MetaM Expr := do
    if slack.toList.any (·.2 < 0) then
      throwError "farkas: the certificate leaves a negative slack; its negative monomials:{indentD (showNeg name slack)}"
    let checkOf (x y : CExpr) : MetaM Expr := do
      let some (_, m) := chooseCheck none n x y | throwError "farkas: internal error, the check fails"
      return m
    if slack.isEmpty then
      let me ← checkOf c1 c2
      if H.strict then
        let p := mkAppN (mkConst tieName) #[me, vals, l, r, a, b, H.proof, rfl]
        if strictGoal then return p else return ← leOfLt p
      else if strictGoal then
        throwError "farkas: no slack and no strict hypothesis: the certificate proves `≤`, not `<`"
      else
        return mkAppN (mkConst leName) #[me, vals, l, r, a, b, H.proof, rfl]
    let mons := slack.toArray.qsort (fun x y => x.1.toList.length < y.1.toList.length) |>.map
      fun (m, c) => termOf m c.toNat
    let s := sumOf mons 0 mons.size
    let rhs : CExpr := .add c2 s
    let me ← checkOf c1 rhs
    let hle ← if H.strict then leOfLt H.proof else pure H.proof
    let p := mkAppN (mkConst ltName) #[me, vals, l, r, a, b, toTerm s, hle, rfl]
    if strictGoal then return p else return ← leOfLt p

/-- One hypothesis of `farkas`, with an optional coefficient: `h` or `c • h`. -/
syntax farkasArg := (atomic(term:max " • "))? term

/-- The most equations whose orientations `qeq [...]` tries. -/
meta def orientMax : Nat := 6

/-- Close `L = R` from equations `hⱼ : aⱼ = bⱼ` with coefficients `cⱼ` (default `1`): with `A = Σ cⱼ aⱼ` and
`B = Σ cⱼ bⱼ`, the identity `L + B = R + A` is checked as by `qeq`, and `A = B` cancels (`Count.eq_of_comb`): `L - R`
is `Σ cⱼ (aⱼ - bⱼ)`, with no subtraction. Each equation is read either way round (`bⱼ = aⱼ`): with at most
`orientMax` equations every orientation is tried in the elaborator, and the kernel checks the one that closes the
goal. A name in `aⱼ` or `bⱼ` stays an atom: an alias is used through its defining equation and never unfolded. -/
meta def qeqComb (g : MVarId) (args : Array (Option Term × Term)) : TacticM Unit := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some (T, L, R) := t.eq? | throwError "qeq: the goal is not an equation{indentExpr t}"
  let mass ← if ← isDefEq T (mkConst ``Mass) then pure true
    else if ← isDefEq T (mkConst ``Count) then pure false
    else throwError "qeq: not an equation of counts or of masses{indentExpr t}"
  let mut hs : Array (Expr × Expr × Expr) := #[]
  for (c?, h) in args do
    let p ← instantiateMVars (← elabTerm h none)
    let ht ← instantiateMVars (← inferType p)
    let some (T', a, b) := ht.eq? | throwError "qeq: not an equation{indentExpr ht}"
    unless ← isDefEq T T' do throwError "qeq: an equation of another type{indentExpr ht}"
    let (a, b, p) ← match c? with
      | none => pure (a, b, p)
      | some c => do
        let c ← instantiateMVars (← elabTerm c (some T))
        pure (← mkAppM ``HMul.hMul #[c, a], ← mkAppM ``HMul.hMul #[c, b], ← mkAppM ``mul_eq_mul #[c, p])
    hs := hs.push (a, b, p)
  if hs.isEmpty then throwError "qeq: no equation given"
  -- the combination with the equations flipped where `mask` has a bit set
  let close (mask : Nat) : TacticM Unit := do
    let mut acc : Option (Expr × Expr × Expr) := none
    for h : j in [:hs.size] do
      let (a, b, p) := hs[j]
      let (a, b, p) ← if mask >>> j % 2 == 1 then pure (b, a, ← mkEqSymm p) else pure (a, b, p)
      acc ← match acc with
        | none => pure (some (a, b, p))
        | some (A, B, q) => pure (some (← mkAppM ``HAdd.hAdd #[A, a], ← mkAppM ``HAdd.hAdd #[B, b],
            ← mkAppM ``add_eq_add #[q, p]))
    let some (A, B, hAB) := acc | throwError "qeq: no equation given"
    let lhs ← mkAppM ``HAdd.hAdd #[L, B]
    let rhs ← mkAppM ``HAdd.hAdd #[R, A]
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs rhs)
    if mass then qeqMass none g'.mvarId! lhs rhs else qeq none g'.mvarId!
    g.assign (← mkAppM (if mass then ``Mass.eq_of_comb else ``Count.eq_of_comb) #[hAB, g'])
  if hs.size ≤ orientMax then
    for mask in [0:2 ^ hs.size] do
      let s ← saveState
      try
        close mask
        return
      catch _ => s.restore
  close 0

/-- `farkas [h₁, c₂ • h₂, ...]` closes `L < R` or `L ≤ R` (counts or masses) by the positive combination of the
hypotheses and a slack with no negative monomial. -/
syntax (name := farkasTac) "farkas" (" [" farkasArg,* "]")? : tactic

/-- `qeq [h₁, c₂ • h₂, ...]` closes `L = R` (counts or masses) from equations `hⱼ : aⱼ = bⱼ`: `L + Σ cⱼ bⱼ =
R + Σ cⱼ aⱼ` is an identity. With the defining equations of aliases as the `hⱼ`, the aliases stay atoms. -/
syntax (name := qeqCombTac) "qeq" " [" farkasArg,* "]" : tactic

elab_rules : tactic
  | `(tactic| qeq [$args,*]) => do
    let parsed ← args.getElems.mapM fun arg => match arg with
      | `(farkasArg| $c:term • $h:term) => pure (some c, h)
      | `(farkasArg| $h:term) => pure (none, h)
      | _ => throwUnsupportedSyntax
    let g ← getMainGoal
    qeqComb g parsed
    replaceMainGoal []

elab_rules : tactic
  | `(tactic| farkas $[[$args,*]]?) => do
    let args := (args.map (·.getElems)).getD #[]
    let parsed ← args.mapM fun arg => match arg with
      | `(farkasArg| $c:term • $h:term) => pure (some c, h)
      | `(farkasArg| $h:term) => pure (none, h)
      | _ => throwUnsupportedSyntax
    let g ← getMainGoal
    farkasCore g parsed
    replaceMainGoal []

end Qpp.Qeq
