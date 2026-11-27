module

public import QppKernel.MassTactic

/-!
# The laws of the masses

The four laws of Q++ (Tarski's axiom for `/`, the unit `1 / 1 = 1`, `+` associative, `(x + y) / z = x / z + y / z`),
`neq` and `ind`, the laws of a semifield with no zero that follow, and cancellation. Each law is an identity of
masses, checked by `qeq`; `neq`, `ind` and cancellation come from the counts. Of the laws that follow, only those
that the tactics and the kernel's own results use are proved here; the others are Mathlib's, read through
`Mass ≃ ℚ>0` (`lean/QppBridge/Mass.lean`).
-/

@[expose] public section

namespace Qpp.Mass

/-! ## The four laws -/

/-- Tarski's axiom: `/` is the division of a commutative group. -/
theorem tarski (x y z : Mass) : x / (y / (z / (x / y))) = z := by qeq

theorem one_div_one : (1 : Mass) / 1 = 1 := by qeq

theorem add_assoc (x y z : Mass) : x + y + z = x + (y + z) := by qeq

theorem add_div (x y z : Mass) : (x + y) / z = x / z + y / z := by qeq

/-! ## `neq` and `ind` -/

/-- `neq`: `1 + 1 ≠ 1`. -/
theorem one_add_one_ne_one : (1 : Mass) + 1 ≠ 1 := by
  intro h
  have h' : (1 * 1 + 1 * 1 : Count) * 1 = 1 * (1 * 1) := mk_eq_mk.mp h
  exact Count.succ_ne_one 1 h'

theorem ofCount_one : ofCount 1 = 1 := rfl

theorem ofCount_succ (n : Count) : ofCount (Count.succ n) = ofCount n + 1 := by
  show mk (Count.succ n) 1 = mk (n * 1 + 1 * 1) (1 * 1)
  rw [mk_eq_mk]; qeq

theorem mk_eq_div (p q : Count) : mk p q = ofCount p / ofCount q := by
  show mk p q = mk (p * 1) (1 * q); rw [mk_eq_mk]; qeq

/-- `ind`: a property of `1` kept by `+` and by `/` holds for every mass. -/
theorem ind {P : Mass → Prop} (h1 : P 1) (hadd : ∀ x y, P x → P y → P (x + y))
    (hdiv : ∀ x y, P x → P y → P (x / y)) (x : Mass) : P x := by
  have hc : ∀ n : Count, P (ofCount n) := by
    intro n
    induction n using Count.ind with
    | h1 => exact h1
    | hs n ih => rw [ofCount_succ]; exact hadd _ _ ih h1
  induction x using ind_mk with
  | h p q => rw [mk_eq_div]; exact hdiv _ _ (hc p) (hc q)

/-! ## The laws of a semifield with no zero -/

theorem add_comm (x y : Mass) : x + y = y + x := by qeq
theorem mul_comm (x y : Mass) : x * y = y * x := by qeq
theorem mul_assoc (x y z : Mass) : x * y * z = x * (y * z) := by qeq
theorem one_mul (x : Mass) : 1 * x = x := by qeq
theorem mul_one (x : Mass) : x * 1 = x := by qeq
theorem mul_add (x y z : Mass) : x * (y + z) = x * y + x * z := by qeq
theorem add_mul (x y z : Mass) : (x + y) * z = x * z + y * z := by qeq

/-! ## Cancellation -/

theorem add_right_cancel {x y z : Mass} (h : x + z = y + z) : x = y := by
  induction x using ind_mk with | h p q =>
  induction y using ind_mk with | h p' q' =>
  induction z using ind_mk with | h u v =>
  rw [add_mk, add_mk, mk_eq_mk] at h
  apply mk_eq_mk.mpr
  apply Count.mul_right_cancel (c := v * v)
  apply Count.add_right_cancel (c := u * q * q' * v)
  calc p * q' * (v * v) + u * q * q' * v = (p * v + u * q) * (q' * v) := by qeq
    _ = (p' * v + u * q') * (q * v) := h
    _ = p' * q * (v * v) + u * q * q' * v := by qeq

theorem add_left_cancel {x y z : Mass} (h : z + x = z + y) : x = y := by
  rw [add_comm z x, add_comm z y] at h; exact add_right_cancel h

/-- No mass is the sum of itself and another (the strong form of `neq`). -/
theorem add_ne_left (x y : Mass) : x + y ≠ x := by
  induction x using ind_mk with | h p q =>
  induction y using ind_mk with | h r s =>
  intro h
  rw [add_mk, mk_eq_mk] at h
  apply Count.add_ne_left (p * q * s) (r * q * q)
  calc p * q * s + r * q * q = (p * s + r * q) * q := by qeq
    _ = p * (q * s) := h
    _ = p * q * s := by qeq

end Qpp.Mass
