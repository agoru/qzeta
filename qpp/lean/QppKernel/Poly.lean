module

public import QppKernel.Bal
public import QppKernel.Sum

/-!
# Finite supports: polynomials

The number of variables is a parameter, and a word has a fixed arity, so a polynomial is data: a finite list of
terms, each a monomial (the exponents of the variables `0, 1, ...`; trailing zeros do not count) with a mass as its
coefficient. The finitely supported map it stands for is `coeff`, with absent where there is no term; a polynomial
with no terms is absent too (no zero). Sum is concatenation and product is term by term; both are read through
`coeff` and through the value `eval`. A polynomial with coefficients of both kinds is a pair of these, tied when
its two sides have the same coefficients (`Poly.Tie`).
-/

@[expose] public section

namespace Qpp

theorem Mass.pow_succ (x : Mass) (k : Nat) : x ^ (k + 1) = x ^ k * x := rfl

theorem Mass.pow_add (x : Mass) (a : Nat) : ∀ b : Nat, x ^ (a + b) = x ^ a * x ^ b
  | 0 => by show x ^ a = x ^ a * 1; rw [Mass.mul_one]
  | b + 1 => by
    rw [← Nat.add_assoc, Mass.pow_succ, Mass.pow_succ, Mass.pow_add x a b]; qeq

/-- A monomial: the exponents of the variables `0, 1, ...`. -/
abbrev Mon := List Nat

/-- A polynomial: its terms, each a monomial with a mass as coefficient. -/
abbrev Poly := List (Mon × Mass)

/-- The product of two possibly absent terms; absent times anything is absent. -/
def omul {α : Type} [Mul α] : Option α → Option α → Option α
  | some x, some y => some (x * y)
  | _, _ => none

namespace Mon

/-- The exponents with no trailing zeros. -/
def trim (m : Mon) : Mon := (m.reverse.dropWhile (· == 0)).reverse

/-- The product of monomials: the exponents add. -/
def mul : Mon → Mon → Mon
  | [], n => n
  | m, [] => m
  | a :: m, b :: n => (a + b) :: mul m n

/-- The value at `x`, the variables counted from `i`. -/
def evalFrom (x : Nat → Mass) : Nat → Mon → Mass
  | _, [] => 1
  | i, e :: m => x i ^ e * evalFrom x (i + 1) m

/-- The value at `x`: `Π x_i ^ m_i`. -/
def eval (x : Nat → Mass) (m : Mon) : Mass := evalFrom x 0 m

/-- The total degree. -/
def deg (m : Mon) : Nat := m.foldr (· + ·) 0

theorem evalFrom_mul (x : Nat → Mass) : ∀ (i : Nat) (m n : Mon),
    evalFrom x i (mul m n) = evalFrom x i m * evalFrom x i n
  | i, [], n => by simp only [mul, evalFrom]; qeq
  | i, a :: m, [] => by simp only [mul, evalFrom]; qeq
  | i, a :: m, b :: n => by
    simp only [mul, evalFrom, evalFrom_mul x (i + 1) m n]
    rw [show x i ^ (a + b) = x i ^ a * x i ^ b from Mass.pow_add (x i) a b]
    qeq

theorem eval_mul (x : Nat → Mass) (m n : Mon) : eval x (mul m n) = eval x m * eval x n :=
  evalFrom_mul x 0 m n

end Mon

namespace Poly

/-- The variable `x_i`. -/
def var (i : Nat) : Poly := [(List.replicate i 0 ++ [1], 1)]

/-- The constant `c`. -/
def const (c : Mass) : Poly := [([], c)]

/-- The coefficient of the monomial `m`: the sum of the coefficients of its terms, absent if there are none. -/
def coeff (p : Poly) (m : Mon) : Option Mass := osum ((p.filter fun t => t.1.trim == m.trim).map (·.2))

/-- The support: the monomials with a term. -/
def support (p : Poly) : List Mon := (p.map (·.1.trim)).eraseDups

/-- The value at `x`: `Σ c x^m`, absent if there are no terms. -/
def eval (x : Nat → Mass) (p : Poly) : Option Mass := osum (p.map fun t => t.2 * t.1.eval x)

/-- The product, term by term. -/
def mul (p q : Poly) : Poly := p.flatMap fun s => q.map fun t => (Mon.mul s.1 t.1, s.2 * t.2)

/-- The total degree: the largest of its monomials. -/
def deg (p : Poly) : Nat := p.foldr (fun t d => max t.1.deg d) 0

/-- Two pairs of polynomials stand for the same polynomial: `a.l + b.r` and `b.l + a.r` have the same
coefficients. -/
def Tie (a b : Bal Poly) : Prop := ∀ m, coeff (a.l ++ b.r) m = coeff (b.l ++ a.r) m

theorem coeff_append (p q : Poly) (m : Mon) : coeff (p ++ q) m = oadd (coeff p m) (coeff q m) := by
  simp only [coeff, List.filter_append, List.map_append, Mass.osum_append]

theorem eval_append (x : Nat → Mass) (p q : Poly) : eval x (p ++ q) = oadd (eval x p) (eval x q) := by
  simp only [eval, List.map_append, Mass.osum_append]

theorem eval_const (x : Nat → Mass) (c : Mass) : eval x (const c) = some c := by
  show oadd (some (c * 1)) none = some c
  rw [Mass.mul_one]; rfl

theorem osum_map_mul (c : Mass) (f : Mon × Mass → Mass) :
    ∀ q : Poly, osum (q.map fun t => c * f t) = omul (some c) (osum (q.map f))
  | [] => rfl
  | t :: q => by
    simp only [List.map_cons, osum, osum_map_mul c f q]
    cases osum (q.map f) <;> simp only [oadd, omul, Mass.mul_add]

theorem omul_oadd (a : Mass) (P Q : Option Mass) :
    omul (oadd (some a) P) Q = oadd (omul (some a) Q) (omul P Q) := by
  cases P <;> cases Q <;> simp only [oadd, omul, Mass.add_mul]

theorem eval_mul (x : Nat → Mass) : ∀ p q : Poly, eval x (mul p q) = omul (eval x p) (eval x q)
  | [], q => rfl
  | s :: p, q => by
    have hp := eval_mul x p q
    simp only [mul, List.flatMap_cons] at hp ⊢
    rw [eval_append, hp]
    have hq : eval x (q.map fun t => (Mon.mul s.1 t.1, s.2 * t.2)) =
        omul (some (s.2 * s.1.eval x)) (eval x q) := by
      simp only [eval, List.map_map]
      rw [← osum_map_mul]
      congr 1
      apply List.map_congr_left
      intro t _
      simp only [Function.comp, Mon.eval_mul]
      qeq
    rw [hq]
    simp only [eval, List.map_cons, osum]
    rw [omul_oadd]

theorem tie_refl (a : Bal Poly) : Tie a a := fun _ => rfl

theorem tie_symm {a b : Bal Poly} (h : Tie a b) : Tie b a := fun m => (h m).symm

end Poly

end Qpp
