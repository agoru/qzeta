module

public import QppKernel.Base
public import QppKernel.Tactic

/-!
# Masses

A mass is a pair of counts `(p, q)`, read `p / q`, up to the tie (`Base.lean`, where masses and their operations
are defined): `p / q` and `r / s` are the same mass when `p * s = r * q`. The quotient is what lets `=` mean the
tie; without it every function of masses would carry its congruence at each use.

An expression in masses is checked by the identity of counts between its numerators and denominators
(`MExpr.eq_of_check`): `a = b` when `num a * den b = num b * den a`, the masses written over one common
denominator, the count variable `0`, with the numerator of the mass variable `i` the count variable `i + 1`.
-/

@[expose] public section

namespace Qpp

namespace Mass

/-- Every mass is `p / q` for counts `p, q`. -/
theorem ind_mk {P : Mass → Prop} (h : ∀ p q, P (mk p q)) (x : Mass) : P x :=
  Quotient.ind (fun ⟨p, q⟩ => h p q) x

theorem one_def : (1 : Mass) = mk 1 1 := rfl

theorem add_mk (p q r s : Count) : mk p q + mk r s = mk (p * s + r * q) (q * s) := rfl
theorem div_mk (p q r s : Count) : mk p q / mk r s = mk (p * s) (q * r) := rfl

theorem mul_mk (p q r s : Count) : mk p q * mk r s = mk (p * r) (q * s) := by
  show mk p q / (mk 1 1 / mk r s) = _
  rw [div_mk, div_mk, mk_eq_mk]; qeq

theorem inv_mk (p q : Count) : (mk p q)⁻¹ = mk q p := by
  show mk 1 1 / mk p q = _
  rw [div_mk, mk_eq_mk]; qeq

theorem pow_mk (p q : Count) : ∀ k : Nat, mk p q ^ k = mk (p ^ k) (q ^ k)
  | 0 => rfl
  | k + 1 => by
    show Mass.npow (mk p q) k * mk p q = _
    rw [show Mass.npow (mk p q) k = mk p q ^ k from rfl, pow_mk p q k, mul_mk]; rfl

end Mass

/-! ## Identities of masses -/

/-- An expression in masses: variables, `1`, numerals, sum, product, division, inverse and powers by numerals. -/
inductive MExpr where
  | var (i : Nat)
  | one
  /-- the numeral `n + 1` -/
  | num (n : Nat)
  | add (a b : MExpr)
  | mul (a b : MExpr)
  | div (a b : MExpr)
  | inv (a : MExpr)
  | pow (a : MExpr) (k : Nat)

namespace MExpr

def eval (σ : List Mass) : MExpr → Mass
  | var i => σ.getD i 1
  | one => 1
  | num n => (OfNat.ofNat (n + 1) : Mass)
  | add a b => eval σ a + eval σ b
  | mul a b => eval σ a * eval σ b
  | div a b => eval σ a / eval σ b
  | inv a => (eval σ a)⁻¹
  | pow a k => eval σ a ^ k

/-- The numerator and the denominator of an expression over one denominator common to the variables: the mass
variable `i` is the count variable `i + 1` over the count variable `0`. -/
def numDen : MExpr → CExpr × CExpr
  | var i => (.var (i + 1), .var 0)
  | one => (.one, .one)
  | num n => (.num n, .one)
  | add a b =>
    let (p, q) := numDen a
    let (r, s) := numDen b
    (.add (.mul p s) (.mul r q), .mul q s)
  | mul a b =>
    let (p, q) := numDen a
    let (r, s) := numDen b
    (.mul p r, .mul q s)
  | div a b =>
    let (p, q) := numDen a
    let (r, s) := numDen b
    (.mul p s, .mul q r)
  | inv a => let (p, q) := numDen a; (q, p)
  | pow a k => let (p, q) := numDen a; (.pow p k, .pow q k)

/-- Masses have a common denominator: `σ[i] = ρ (i + 1) / ρ 0` for every `i` (past the end of `σ`, `1 = ρ 0 / ρ 0`). -/
theorem exists_common : ∀ σ : List Mass, ∃ ρ : Nat → Count, ∀ i, σ.getD i 1 = Mass.mk (ρ (i + 1)) (ρ 0)
  | [] => ⟨fun _ => 1, fun _ => rfl⟩
  | x :: σ => by
    obtain ⟨ρ, h⟩ := exists_common σ
    induction x using Mass.ind_mk with
    | h p r =>
      refine ⟨fun i => match i with | 0 => ρ 0 * r | 1 => p * ρ 0 | j + 2 => ρ (j + 1) * r, fun i => ?_⟩
      cases i with
      | zero => show Mass.mk p r = Mass.mk (p * ρ 0) (ρ 0 * r); rw [Mass.mk_eq_mk]; qeq
      | succ j =>
        show σ.getD j 1 = Mass.mk (ρ (j + 1) * r) (ρ 0 * r)
        rw [h j, Mass.mk_eq_mk]; qeq

theorem eval_common (σ : List Mass) (ρ : Nat → Count) (h : ∀ i, σ.getD i 1 = Mass.mk (ρ (i + 1)) (ρ 0)) :
    ∀ e : MExpr, eval σ e = Mass.mk ((numDen e).1.eval ρ) ((numDen e).2.eval ρ)
  | var i => h i
  | one => rfl
  | num n => rfl
  | add a b => by simp only [eval, numDen, eval_common σ ρ h a, eval_common σ ρ h b, Mass.add_mk]; rfl
  | mul a b => by simp only [eval, numDen, eval_common σ ρ h a, eval_common σ ρ h b, Mass.mul_mk]; rfl
  | div a b => by simp only [eval, numDen, eval_common σ ρ h a, eval_common σ ρ h b, Mass.div_mk]; rfl
  | inv a => by simp only [eval, numDen, eval_common σ ρ h a, Mass.inv_mk]
  | pow a k => by simp only [eval, numDen, eval_common σ ρ h a, Mass.pow_mk]; rfl

/-- The identity of counts that an identity of masses comes to: `num a * den b = num b * den a`. -/
def cross (a b : MExpr) : CExpr × CExpr :=
  (.mul (numDen a).1 (numDen b).2, .mul (numDen b).1 (numDen a).2)

/-- Soundness: two mass expressions whose cross identity passes the check are equal for all values. -/
theorem eq_of_check (m : CheckBy) (σ : List Mass) (a b : MExpr)
    (h : CExpr.verify m (cross a b).1 (cross a b).2 = true) : eval σ a = eval σ b := by
  obtain ⟨ρ, hρ⟩ := exists_common σ
  rw [eval_common σ ρ hρ a, eval_common σ ρ hρ b, Mass.mk_eq_mk]
  exact CExpr.eq_of_verify m ρ _ _ h

end MExpr

end Qpp
