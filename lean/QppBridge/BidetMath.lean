module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.LinearCombination

/-!
# The bideterminant over Mathlib

The two halves `QppMathlib.bidetP T U`, `QppMathlib.bidetM T U` of the determinant of a couple of square tables
`(T, U)` over `ℚ≥0`, standing for `T - U`: the determinant over the semiring of couples (Akian, Gaubert and Guterman,
arXiv:0812.3496, Def. 4.14); for `U = 0`, the bideterminant `(|T|^+, |T|^-)` of Gondran and Minoux, the sums over the
even and over the odd permutations. They are defined by Laplace's recursion along the first row: the column `j` of
`Fin (n + 1)`, counted from `0`, keeps the halves of its minor when `j` is even and exchanges them when `j` is odd, and
the minor of `(0, j)` is read through `Fin.succ` and `Fin.succAbove j`. This module imports Mathlib only, so that a
statement over Mathlib names the halves without the kernel; `QppBridge.Bidet` reads the kernel's halves as these.

`QppMathlib.bidetP_eq` is the one law of the word: in `ℚ`, the half `+` is the half `-` plus `Matrix.det` of the
difference `T - U`, by Laplace's expansion along the first row (Mathlib's `Matrix.det_succ_row_zero`) and induction on
the size. Every other law of the halves comes from a law of `Matrix.det` through it.
-/

@[expose] public section

namespace QppMathlib

open Finset

/-- The half `s` (`true` for `+`) of the determinant of the couple of tables `(T, U)` over `ℚ≥0`: `(1, 0)` on no rows;
on `n + 1` rows, the sum over the columns `j` of `T 0 j` times the half `s` of the minor of `(0, j)` and `U 0 j` times
its other half, the two halves of the minor exchanged when `j` is odd. -/
def bidet : (n : ℕ) → Bool → (Fin n → Fin n → ℚ≥0) → (Fin n → Fin n → ℚ≥0) → ℚ≥0
  | 0, s, _, _ => if s then 1 else 0
  | n + 1, s, T, U => ∑ j : Fin (n + 1),
      (T 0 j * bidet n (s == decide (Even (j : ℕ))) (fun a b => T a.succ (j.succAbove b))
          (fun a b => U a.succ (j.succAbove b))
        + U 0 j * bidet n (s != decide (Even (j : ℕ))) (fun a b => T a.succ (j.succAbove b))
          (fun a b => U a.succ (j.succAbove b)))

/-- `|(T, U)|^+`, the half `+` of the couple of tables `(T, U)`. -/
def bidetP {n : ℕ} (T U : Fin n → Fin n → ℚ≥0) : ℚ≥0 := bidet n true T U

/-- `|(T, U)|^-`, the half `-` of the couple of tables `(T, U)`. -/
def bidetM {n : ℕ} (T U : Fin n → Fin n → ℚ≥0) : ℚ≥0 := bidet n false T U

/-- The law of the halves: `|(T, U)|^+ = |(T, U)|^- + det (T - U)` in `ℚ`. -/
theorem bidet_true_eq : ∀ (n : ℕ) (T U : Fin n → Fin n → ℚ≥0),
    ((bidet n true T U : ℚ≥0) : ℚ) = (bidet n false T U : ℚ) + (Matrix.of fun a b => (T a b : ℚ) - U a b).det
  | 0, T, U => by
    rw [Matrix.det_fin_zero]
    show ((1 : ℚ≥0) : ℚ) = ((0 : ℚ≥0) : ℚ) + 1
    rw [NNRat.coe_one, NNRat.coe_zero, zero_add]
  | n + 1, T, U => by
    rw [Matrix.det_succ_row_zero, bidet.eq_2, bidet.eq_2, NNRat.cast_sum, NNRat.cast_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ih := bidet_true_eq n (fun a b => T a.succ (j.succAbove b)) (fun a b => U a.succ (j.succAbove b))
    have hm : (Matrix.of fun a b => (T a b : ℚ) - U a b).submatrix Fin.succ j.succAbove
        = Matrix.of fun a b => ((T a.succ (j.succAbove b) : ℚ≥0) : ℚ) - U a.succ (j.succAbove b) := rfl
    rw [hm, Matrix.of_apply, NNRat.coe_add, NNRat.coe_add, NNRat.coe_mul, NNRat.coe_mul, NNRat.coe_mul,
      NNRat.coe_mul]
    rcases Nat.even_or_odd (j : ℕ) with h | h
    · rw [decide_eq_true h, h.neg_one_pow]
      show (T 0 j : ℚ) * (bidet n true _ _ : ℚ) + (U 0 j : ℚ) * (bidet n false _ _ : ℚ)
        = (T 0 j : ℚ) * (bidet n false _ _ : ℚ) + (U 0 j : ℚ) * (bidet n true _ _ : ℚ) + _
      linear_combination ((T 0 j : ℚ) - U 0 j) * ih
    · rw [decide_eq_false (Nat.not_even_iff_odd.mpr h), h.neg_one_pow]
      show (T 0 j : ℚ) * (bidet n false _ _ : ℚ) + (U 0 j : ℚ) * (bidet n true _ _ : ℚ)
        = (T 0 j : ℚ) * (bidet n true _ _ : ℚ) + (U 0 j : ℚ) * (bidet n false _ _ : ℚ) + _
      linear_combination (-((T 0 j : ℚ) - U 0 j)) * ih

/-- `|(T, U)|^+ = |(T, U)|^- + det (T - U)` in `ℚ`. -/
theorem bidetP_eq {n : ℕ} (T U : Fin n → Fin n → ℚ≥0) :
    ((bidetP T U : ℚ≥0) : ℚ) = (bidetM T U : ℚ) + (Matrix.of fun a b => (T a b : ℚ) - U a b).det :=
  bidet_true_eq n T U

end QppMathlib
