module

public import QppKernel.Poly

/-!
# The integral of a law

A law on `Q` has atoms `x_i` with masses `π_i` and cells `[u_j, v_j]` with polynomial densities `p_j`. The integral
of a polynomial `g` is `Σ π_i g(x_i) + Σ_j ∫_{u_j}^{v_j} g p_j`, a finite word in counts, polynomials and pairs:
`∫_u^v c x^k` is `c (v^(k+1) - u^(k+1)) / (k+1)`, a pair of masses. Points, ends and polynomials with coefficients of
both kinds are pairs, so the integral is a pair too; the integral over `[u, v]` and `[v, w]` is the integral over
`[u, w]` (`Poly.integral_split`).
-/

@[expose] public section

namespace Qpp

namespace Bal

/-- Both sides scaled by the mass `c`. -/
def scale (c : Mass) (a : Bal Mass) : Bal Mass := ⟨c * a.l, c * a.r⟩

/-- The sum of a list of pairs; with no entries, `level`. -/
def sum : List (Bal Mass) → Bal Mass
  | [] => level
  | a :: l => a + sum l

@[simp] theorem scale_l (c : Mass) (a : Bal Mass) : (scale c a).l = c * a.l := rfl
@[simp] theorem scale_r (c : Mass) (a : Bal Mass) : (scale c a).r = c * a.r := rfl

end Bal

namespace Mass

open Bal

theorem bal_sum_append : ∀ l m : List (Bal Mass), (sum (l ++ m)).Tie (sum l + sum m)
  | [], m => bal_tie_symm (bal_level_add (sum m))
  | a :: l, m => by
    show (a + sum (l ++ m)).Tie (a + sum l + sum m)
    exact bal_tie_trans (bal_add_tie (bal_tie_refl a) (bal_sum_append l m))
      (bal_tie_symm (bal_add_assoc a (sum l) (sum m)))

end Mass

namespace Mon

/-- The value at a point given as pairs, the variables counted from `i`. -/
def evalBalFrom (x : Nat → Bal Mass) : Nat → Mon → Bal Mass
  | _, [] => Bal.of 1
  | i, e :: m => x i ^ e * evalBalFrom x (i + 1) m

/-- The value at a point given as pairs. -/
def evalBal (x : Nat → Bal Mass) (m : Mon) : Bal Mass := evalBalFrom x 0 m

end Mon

namespace Poly

/-- The value at a point given as pairs; `level` with no terms. -/
def evalBal (x : Nat → Bal Mass) (p : Poly) : Bal Mass := Bal.sum (p.map fun t => Bal.scale t.2 (t.1.evalBal x))

/-- `∫_u^v c x^k = c (v^(k+1) - u^(k+1)) / (k+1)`, as a pair. -/
def integralTerm (u v : Bal Mass) (k : Nat) (c : Mass) : Bal Mass :=
  Bal.scale (c / Mass.ofCount (Count.ofNatSucc k)) (v ^ (k + 1) + Bal.swap (u ^ (k + 1)))

/-- `∫_u^v p` for a polynomial in the variable `0`. -/
def integral (u v : Bal Mass) (p : Poly) : Bal Mass := Bal.sum (p.map fun t => integralTerm u v (t.1.headD 0) t.2)

/-- The product of pairs of polynomials. -/
def balMul (a b : Bal Poly) : Bal Poly := ⟨mul a.l b.l ++ mul a.r b.r, mul a.l b.r ++ mul a.r b.l⟩

/-- The value of a pair of polynomials at a point given as pairs. -/
def balEval (x : Nat → Bal Mass) (a : Bal Poly) : Bal Mass := evalBal x a.l + Bal.swap (evalBal x a.r)

/-- `∫_u^v` of a pair of polynomials in the variable `0`. -/
def balIntegral (u v : Bal Mass) (a : Bal Poly) : Bal Mass := integral u v a.l + Bal.swap (integral u v a.r)

open Bal Mass in
theorem integralTerm_split (u v w : Bal Mass) (k : Nat) (c : Mass) :
    (integralTerm u v k c + integralTerm v w k c).Tie (integralTerm u w k c) := by
  unfold integralTerm Bal.Tie
  simp only [add_l, add_r, scale_l, scale_r, swap_l, swap_r]
  qeq

open Bal Mass in
theorem integral_split (u v w : Bal Mass) : ∀ p : Poly, (integral u v p + integral v w p).Tie (integral u w p)
  | [] => by unfold integral Bal.Tie; simp only [List.map_nil, sum, add_l, add_r, level_l, level_r]; qeq
  | t :: p => by
    have ih := integral_split u v w p
    have ht := integralTerm_split u v w (t.1.headD 0) t.2
    unfold integral at *
    simp only [List.map_cons, sum]
    revert ih ht
    generalize sum (p.map fun t => integralTerm u v (t.1.headD 0) t.2) = A
    generalize sum (p.map fun t => integralTerm v w (t.1.headD 0) t.2) = B
    generalize sum (p.map fun t => integralTerm u w (t.1.headD 0) t.2) = C
    generalize integralTerm u v (t.1.headD 0) t.2 = a
    generalize integralTerm v w (t.1.headD 0) t.2 = b
    generalize integralTerm u w (t.1.headD 0) t.2 = c
    intro ih ht
    unfold Bal.Tie at *
    simp only [add_l, add_r] at *
    calc a.l + A.l + (b.l + B.l) + (c.r + C.r) = (a.l + b.l + c.r) + (A.l + B.l + C.r) := by qeq
      _ = (c.l + (a.r + b.r)) + (C.l + (A.r + B.r)) := by rw [ht, ih]
      _ = c.l + C.l + (a.r + A.r + (b.r + B.r)) := by qeq

open Mass in
theorem integral_append (u v : Bal Mass) (p q : Poly) :
    (integral u v (p ++ q)).Tie (integral u v p + integral u v q) := by
  unfold integral
  rw [List.map_append]
  exact bal_sum_append _ _

end Poly

/-- A law on `Q`: atoms `x_i` with masses `π_i`, and cells `[u_j, v_j]` with densities `p_j`, pairs of polynomials in
the variable `0`. -/
structure Law where
  atoms : List (Bal Mass × Mass)
  cells : List (Bal Mass × Bal Mass × Bal Poly)

namespace Law

/-- `∫ g dq = Σ π_i g(x_i) + Σ_j ∫_{u_j}^{v_j} g p_j`. -/
def integral (q : Law) (g : Bal Poly) : Bal Mass :=
  Bal.sum (q.atoms.map fun a => Bal.scale a.2 (Poly.balEval (fun _ => a.1) g)) +
    Bal.sum (q.cells.map fun c => Poly.balIntegral c.1 c.2.1 (Poly.balMul g c.2.2))

/-- The uniform law on `[0, 1]`: one cell, density `1`. -/
def uniform : Law := ⟨[], [(Bal.level, Bal.of 1, ⟨Poly.const 1, []⟩)]⟩

open Bal Mass in
/-- Its mean is `1/2`. -/
theorem uniform_mean : (uniform.integral ⟨Poly.var 0, []⟩).Tie (Bal.of (1 / 2)) := by
  unfold integral uniform Poly.balIntegral Poly.balMul Poly.integral Poly.integralTerm Tie
  simp only [Poly.mul, Poly.var, Poly.const, List.map, List.flatMap_cons, List.flatMap_nil, List.map_cons,
    List.map_nil, List.append_nil, List.nil_append, sum, Mon.mul, List.headD, add_l, add_r, scale_l, scale_r,
    swap_l, swap_r, level_l, level_r, of_l, of_r, List.replicate]
  simp only [Bal.pow_succ, Bal.pow_zero, mul_l, mul_r, level_l, level_r, of_l, of_r]
  rw [show ofCount (Count.ofNatSucc 1) = 1 + 1 from rfl]
  qeq

end Law

end Qpp
