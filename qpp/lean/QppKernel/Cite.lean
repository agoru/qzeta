module

public import QppKernel.Poly

/-!
# Cited facts

A classical fact that the core does not prove is cited: its statement, over the core, and its source, a DOI with
the number of the statement when there is one. A result that uses it takes the statement as a hypothesis, so the
dependence is explicit in its type, and the Python suite checks the statement on fixtures. A qpp `cit` item is a
`Cited` (`Source` and `Cited` are defined in `Base.lean`), and its source goes into the bibliography.

The example is Polya's theorem on the simplex, cited from Powers and Reznick: a homogeneous polynomial positive on
the closed simplex has, after multiplication by a power of `x_0 + ... + x_(n-1)`, every monomial of its degree with
a positive coefficient. Over masses the closed simplex is its faces: the restrictions to the nonempty sets of
variables, each positive at every point.
-/

@[expose] public section

namespace Qpp

namespace Poly

/-- The terms whose monomials use only the variables in `S`. -/
def restrict (S : List Nat) (p : Poly) : Poly :=
  p.filter fun t => t.1.zipIdx.all fun (e, i) => e == 0 || S.contains i

/-- The power `p ^ k`, with `p ^ 0 = 1`. -/
def npow (p : Poly) : Nat → Poly
  | 0 => const 1
  | k + 1 => mul (npow p k) p

/-- `x_0 + ... + x_(n-1)`. -/
def sumVars (n : Nat) : Poly := (List.range n).flatMap var

/-- Every term has total degree `d`. -/
def Homog (p : Poly) (d : Nat) : Prop := ∀ t ∈ p, t.1.deg = d

/-- A pair of polynomials is positive at `x`: its left side is present and above its right side, or the right side
is absent. -/
def Pos (x : Nat → Mass) (a : Bal Poly) : Prop :=
  match eval x a.l, eval x a.r with
  | some u, some v => v < u
  | some _, none => True
  | none, _ => False

/-- The monomials of degree `d` in the variables below `n`, each present in `q`. -/
def FullSupport (n d : Nat) (q : Poly) : Prop :=
  ∀ m : Mon, m.length ≤ n → m.deg = d → (coeff q m).isSome

end Poly

/-- **Polya's theorem**, cited: a homogeneous pair of polynomials in `n` variables positive on every face of the
simplex becomes, times `(x_0 + ... + x_(n-1)) ^ N` for some `N`, a polynomial with every monomial of its degree. -/
def polya : Cited where
  statement := ∀ (n d : Nat) (a : Bal Poly), Poly.Homog a.l d → Poly.Homog a.r d →
    (∀ S : List Nat, S ≠ [] → (∀ i ∈ S, i < n) → ∀ x : Nat → Mass,
      Poly.Pos x ⟨Poly.restrict S a.l, Poly.restrict S a.r⟩) →
    ∃ (N : Nat) (q : Poly), Poly.FullSupport n (N + d) q ∧
      Poly.Tie ⟨Poly.mul (Poly.npow (Poly.sumVars n) N) a.l, Poly.mul (Poly.npow (Poly.sumVars n) N) a.r⟩ ⟨q, []⟩
  source := { doi := "10.1016/S0022-4049(00)00155-9" }

end Qpp
