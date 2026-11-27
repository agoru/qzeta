module

public import QppBridge.Sums
public import QppBridge.BidetMath

/-!
# The bridge of the bideterminant

The two halves `bidetP T U`, `bidetM T U` of the kernel (`qpp/lean/QppKernel/Words.lean`) are read as
`QppMathlib.bidetP` and `QppMathlib.bidetM` over `ℚ≥0` (`QppBridge.BidetMath`), which follow the same recursion: the
count `j` of the kernel is the column `j - 1` of `Fin`, odd counts are even columns, and the column `b` of the minor
of the column `j` (`Count.skip`) is `Fin.succAbove`. The reading goes through tables on every count (`readTab`), by
induction on the number of rows; the recursion is unfolded here only, to read it, and in no proof of a statement.
-/

@[expose] public section

namespace Qpp

open Finset

/-! ## The kernel's recursion read over `Fin` -/

theorem Count.odd_ofNatSucc : ∀ j : ℕ, (Count.ofNatSucc j).odd = decide (Even j)
  | 0 => (decide_eq_true Even.zero).symm
  | j + 1 => by
    show (!(Count.ofNatSucc j).odd) = _
    rw [Count.odd_ofNatSucc j]
    rcases Nat.even_or_odd j with h | h
    · rw [decide_eq_true h, decide_eq_false (Nat.not_even_iff_odd.mpr h.add_one)]; rfl
    · rw [decide_eq_false (Nat.not_even_iff_odd.mpr h), decide_eq_true h.add_one]; rfl

theorem Count.skip_ofNatSucc : ∀ j b : ℕ,
    Count.skip (Count.ofNatSucc j) (Count.ofNatSucc b) = Count.ofNatSucc (if b < j then b else b + 1)
  | 0, b => by rw [ite_eq_right (Nat.not_lt_zero b)]; rfl
  | j + 1, 0 => by rw [ite_eq_left (Nat.succ_pos j)]; rfl
  | j + 1, b + 1 => by
    show Count.succ (Count.skip (Count.ofNatSucc j) (Count.ofNatSucc b)) = _
    rw [Count.skip_ofNatSucc j b]
    by_cases h : b < j
    · rw [ite_eq_left h, ite_eq_left (Nat.succ_lt_succ h)]; rfl
    · rw [ite_eq_right h, ite_eq_right fun h' => h (Nat.lt_of_succ_lt_succ h')]; rfl

theorem val_succAbove {n : ℕ} (j : Fin (n + 1)) (b : Fin n) :
    (j.succAbove b : ℕ) = if (b : ℕ) < j then (b : ℕ) else (b : ℕ) + 1 := by
  by_cases h : (b : ℕ) < j
  · rw [ite_eq_left h, Fin.succAbove_of_castSucc_lt j b (Fin.lt_def.mpr h)]; rfl
  · rw [ite_eq_right h, Fin.succAbove_of_le_castSucc j b (Fin.le_def.mpr (Nat.le_of_not_lt h))]; rfl

/-- A table on every count read on `Fin m`: the entry `(a, b)` is the entry `(a + 1, b + 1)`. -/
def readTab (T : Count → Count → Mass0) (m : ℕ) : Fin m → Fin m → ℚ≥0 :=
  fun a b => Mass0.toNNRat (T (Count.ofNatSucc a) (Count.ofNatSucc b))

theorem map_sumTo_eq {γ : Type} [AddCommMonoid γ] (φ : Mass0 → γ) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (g : Count → Mass0) (c : Count) (m : ℕ) (hc : c.toNat = m) :
    φ (sumTo g c) = ∑ j : Fin m, φ (g (Count.ofNatSucc j)) := by
  rw [map_sumTo φ hφ]
  exact Fintype.sum_equiv (finCongr hc) _ _ fun _ => rfl

theorem toNNRat_bidet0 (s : Bool) (T U : Count → Count → Mass0) :
    Mass0.toNNRat (bidet0 s T U) = QppMathlib.bidet 0 s (readTab T 0) (readTab U 0) := by
  cases s
  · exact Mass0.toNNRat_zero
  · exact Mass0.toNNRat_one

theorem toNNRat_bidetStep (B : Bool → (Count → Count → Mass0) → (Count → Count → Mass0) → Mass0) (m : ℕ)
    (hB : ∀ s T U, Mass0.toNNRat (B s T U) = QppMathlib.bidet m s (readTab T m) (readTab U m))
    (c : Count) (hc : c.toNat = m + 1) (s : Bool) (T U : Count → Count → Mass0) :
    Mass0.toNNRat (bidetStep B c s T U) = QppMathlib.bidet (m + 1) s (readTab T (m + 1)) (readTab U (m + 1)) := by
  rw [bidetStep, map_sumTo_eq Mass0.toNNRat Mass0.toNNRat_add _ c (m + 1) hc, QppMathlib.bidet.eq_2]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hT : ∀ V : Count → Count → Mass0, readTab (minorAt V (Count.ofNatSucc j)) m
      = fun a b => readTab V (m + 1) a.succ (j.succAbove b) := by
    intro V
    funext a b
    show Mass0.toNNRat (V (Count.succ (Count.ofNatSucc a)) (Count.skip (Count.ofNatSucc j) (Count.ofNatSucc b)))
      = Mass0.toNNRat (V (Count.ofNatSucc (a.succ : ℕ)) (Count.ofNatSucc (j.succAbove b : ℕ)))
    rw [Count.skip_ofNatSucc, val_succAbove]; rfl
  rw [Mass0.toNNRat_add, Mass0.toNNRat_mul, Mass0.toNNRat_mul, hB, hB, Count.odd_ofNatSucc, hT T, hT U]
  rfl

theorem toNNRat_bidetCount : ∀ (c : Count) (s : Bool) (T U : Count → Count → Mass0),
    Mass0.toNNRat (bidetCount c s T U) = QppMathlib.bidet c.toNat s (readTab T c.toNat) (readTab U c.toNat)
  | .one, s, T, U => toNNRat_bidetStep bidet0 0 toNNRat_bidet0 1 rfl s T U
  | .succ c, s, T, U => toNNRat_bidetStep (bidetCount c) c.toNat (toNNRat_bidetCount c) (.succ c) rfl s T U

theorem toNNRat_bidetExt : ∀ (n : Count0) (s : Bool) (T U : Count → Count → Mass0),
    Mass0.toNNRat (bidetExt n s T U) = QppMathlib.bidet n.toNat s (readTab T n.toNat) (readTab U n.toNat)
  | none, s, T, U => toNNRat_bidet0 s T U
  | some c, s, T, U => toNNRat_bidetCount c s T U

theorem readTab_extend2 {n : Count0} (T : Idx n → Idx n → Mass0) :
    readTab (Idx.extend2 T) n.toNat = Idx.map (Idx.map Mass0.toNNRat) T := by
  funext a b
  show Mass0.toNNRat (Idx.extend (fun _ => 0) (fun i => Idx.extend 0 (T i)) (Count.ofNatSucc a) (Count.ofNatSucc b))
    = Mass0.toNNRat (T (Idx.ofFin a) (Idx.ofFin b))
  rw [Idx.extend_ofNatSucc]
  exact congrArg Mass0.toNNRat (Idx.extend_ofNatSucc 0 (T (Idx.ofFin a)) b)

/-! ## The words -/

@[qpp_bridge] theorem Mass0.toNNRat_bidetP {n : Count0} (T U : Idx n → Idx n → Mass0) :
    Mass0.toNNRat (bidetP T U)
      = QppMathlib.bidetP (Idx.map (Idx.map Mass0.toNNRat) T) (Idx.map (Idx.map Mass0.toNNRat) U) := by
  rw [← readTab_extend2 T, ← readTab_extend2 U]
  exact toNNRat_bidetExt n true _ _

@[qpp_bridge] theorem Mass0.toNNRat_bidetM {n : Count0} (T U : Idx n → Idx n → Mass0) :
    Mass0.toNNRat (bidetM T U)
      = QppMathlib.bidetM (Idx.map (Idx.map Mass0.toNNRat) T) (Idx.map (Idx.map Mass0.toNNRat) U) := by
  rw [← readTab_extend2 T, ← readTab_extend2 U]
  exact toNNRat_bidetExt n false _ _

@[qpp_bridge] theorem Mass0.toRat_bidetP {n : Count0} (T U : Idx n → Idx n → Mass0) :
    Mass0.toRat (bidetP T U)
      = ((QppMathlib.bidetP (Idx.map (Idx.map Mass0.toNNRat) T) (Idx.map (Idx.map Mass0.toNNRat) U) : ℚ≥0) : ℚ) := by
  rw [← Mass0.coe_toNNRat, Mass0.toNNRat_bidetP]

@[qpp_bridge] theorem Mass0.toRat_bidetM {n : Count0} (T U : Idx n → Idx n → Mass0) :
    Mass0.toRat (bidetM T U)
      = ((QppMathlib.bidetM (Idx.map (Idx.map Mass0.toNNRat) T) (Idx.map (Idx.map Mass0.toNNRat) U) : ℚ≥0) : ℚ) := by
  rw [← Mass0.coe_toNNRat, Mass0.toNNRat_bidetM]

end Qpp
