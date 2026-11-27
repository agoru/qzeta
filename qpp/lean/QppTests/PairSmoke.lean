module

public import QppKernel

/-! Checks of `peq` and `pfarkas` on identities and inequalities of pairs. -/

namespace Qpp.PairSmoke

open Bal

/-- `(u + v)^2 ≤ 2u^2 + 2v^2` in its tie form: `2u^2 + 2v^2 - (u + v)^2 = (u - v)^2`. -/
example (u v : Bal Mass) : ((of 2) * (u * u) + (of 2) * (v * v)).Tie ((u + v) * (u + v) + (u + swap v) * (u + swap v)) := by
  peq

/-- The identity of one interval at order one. -/
example (s b l r : Bal Mass) :
    ((of (1 / 3)) * (s * s) * (r * r * r + swap (l * l * l)) + s * b * (r * r + swap (l * l)) +
      b * b * (r + swap l)).Tie
    ((of (1 / 3)) * (r + swap l) * ((s * l + b) * (s * l + b) + (s * l + b) * (s * r + b) + (s * r + b) * (s * r + b))) := by
  peq

/-- `(ρ + ψ)^2 ≥ ρ^2/2 - ψ^2`, from the square `(ρ + 2ψ)^2`. -/
example (ρ ψ : Bal Mass) : (of (1 / 2)) * (ρ * ρ) + swap (ψ * ψ) ≤ (ρ + ψ) * (ρ + ψ) := by
  have h := sq_nonneg (ρ + ψ + ψ)
  pfarkas [(1 / 2) • h]

/-- A linear consequence: `x ≤ y`, `y ≤ z` give `x ≤ z`. -/
example (x y z : Bal Mass) (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  pfarkas [h1, h2]

end Qpp.PairSmoke
