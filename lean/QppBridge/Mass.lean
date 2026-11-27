module

public import QppBridge.Count
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# The bridge of masses: `Mass ≃ ℚ>0` and `Mass0 ≃ ℚ≥0`

A mass `p / q` is read as the rational `p / q` (`Mass.toRat`, well defined on the tie), and a mass or absent as a
rational at least `0`, absent at `0` (`Mass0.toRat`, with `Mass0.toNNRat` into `ℚ≥0`). The readings are bijections
onto the positive and the nonnegative rationals (`Mass.equivPos`, `Mass0.equivNNRat`), and they carry every word of
the kernel on masses to the word of Mathlib of the same name (`qpp_bridge`). Each proof only connects the two sides;
the laws of `ℚ` come from Mathlib.
-/

@[expose] public section

namespace Qpp

open Classical

/-! ## Masses -/

namespace Mass

theorem tie_rat {p q r s : Count} (h : p * s = r * q) :
    (p.toNat : ℚ) / q.toNat = r.toNat / s.toNat := by
  have hq : (q.toNat : ℚ) ≠ 0 := by exact_mod_cast (Count.toNat_pos q).ne'
  have hs : (s.toNat : ℚ) ≠ 0 := by exact_mod_cast (Count.toNat_pos s).ne'
  rw [div_eq_div_iff hq hs]
  have := congrArg Count.toNat h
  rw [Count.toNat_mul, Count.toNat_mul] at this
  exact_mod_cast this

/-- The reading of a mass `p / q` as the rational `p / q`. -/
def toRat : Mass → ℚ :=
  Quotient.lift (fun a : Qpp.Pair => (a.num.toNat : ℚ) / a.den.toNat) fun _ _ h => tie_rat h

theorem toRat_mk (p q : Count) : toRat (mk p q) = (p.toNat : ℚ) / q.toNat := rfl

theorem toRat_pos (x : Mass) : 0 < toRat x := by
  induction x using Quotient.inductionOn with
  | h a =>
    show 0 < (a.num.toNat : ℚ) / a.den.toNat
    have := Count.toNat_pos a.num; have := Count.toNat_pos a.den; positivity

theorem toRat_ne_zero (x : Mass) : toRat x ≠ 0 := (toRat_pos x).ne'

/-- The mass of a positive rational: its numerator over its denominator. -/
def ofPos (q : {q : ℚ // 0 < q}) : Mass := mk (Count.ofNat q.1.num.toNat) (Count.ofNat q.1.den)

theorem toRat_ofPos (q : {q : ℚ // 0 < q}) : toRat (ofPos q) = q.1 := by
  have hn : 0 < q.1.num := Rat.num_pos.mpr q.2
  rw [ofPos, toRat_mk, Count.toNat_ofNat_of_pos (by omega), Count.toNat_ofNat_of_pos q.1.den_pos]
  have e : ((q.1.num.toNat : ℕ) : ℚ) = (q.1.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hn.le
  rw [e]
  exact Rat.num_div_den q.1

theorem toRat_injective : Function.Injective toRat := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h a =>
  induction y using Quotient.inductionOn with
  | h b =>
    apply Quotient.sound
    show a.num * b.den = b.num * a.den
    apply Count.toNat_inj
    rw [Count.toNat_mul, Count.toNat_mul]
    have h' : (a.num.toNat : ℚ) / a.den.toNat = b.num.toNat / b.den.toNat := h
    have ha : (a.den.toNat : ℚ) ≠ 0 := by exact_mod_cast (Count.toNat_pos a.den).ne'
    have hb : (b.den.toNat : ℚ) ≠ 0 := by exact_mod_cast (Count.toNat_pos b.den).ne'
    rw [div_eq_div_iff ha hb] at h'
    exact_mod_cast h'

/-- The reading of a mass as a positive rational. -/
def toPos (x : Mass) : {q : ℚ // 0 < q} := ⟨toRat x, toRat_pos x⟩

/-- `Mass ≃ ℚ>0`. -/
def equivPos : Mass ≃ {q : ℚ // 0 < q} where
  toFun := toPos
  invFun := ofPos
  left_inv x := toRat_injective (toRat_ofPos (toPos x))
  right_inv q := Subtype.ext (toRat_ofPos q)

@[qpp_bridge] theorem coe_toPos (x : Mass) : ((toPos x : {q : ℚ // 0 < q}) : ℚ) = toRat x := rfl

/-- The mass of a rational, for the rationals above `0` (and `1` otherwise). -/
def ofRat (q : ℚ) : Mass := if h : 0 < q then ofPos ⟨q, h⟩ else 1

theorem toRat_ofRat {q : ℚ} (h : 0 < q) : toRat (ofRat q) = q := by
  simp only [ofRat, h, dite_true, toRat_ofPos]

@[qpp_bridge] theorem toRat_eq {x y : Mass} : x = y ↔ toRat x = toRat y := toRat_injective.eq_iff.symm

@[qpp_bridge] theorem toRat_add (x y : Mass) : toRat (x + y) = toRat x + toRat y := by
  induction x using Quotient.inductionOn with
  | h a =>
  induction y using Quotient.inductionOn with
  | h b =>
    show toRat (mk _ _) = toRat (mk _ _) + toRat (mk _ _)
    simp only [toRat_mk, Count.toNat_add, Count.toNat_mul, Nat.cast_add, Nat.cast_mul]
    have := Count.toNat_pos a.den; have := Count.toNat_pos b.den
    field_simp

@[qpp_bridge] theorem toRat_div (x y : Mass) : toRat (x / y) = toRat x / toRat y := by
  induction x using Quotient.inductionOn with
  | h a =>
  induction y using Quotient.inductionOn with
  | h b =>
    show toRat (mk _ _) = toRat (mk _ _) / toRat (mk _ _)
    simp only [toRat_mk, Count.toNat_mul, Nat.cast_mul]
    have := Count.toNat_pos a.den; have := Count.toNat_pos b.den; have := Count.toNat_pos b.num
    field_simp

@[qpp_bridge] theorem toRat_one : toRat 1 = 1 := by
  show ((1 : Count).toNat : ℚ) / (1 : Count).toNat = 1; simp [Count.toNat_one']

@[qpp_bridge] theorem toRat_ofNat (n : ℕ) : toRat (no_index (OfNat.ofNat (n + 1)) : Mass) = ((n + 1 : ℕ) : ℚ) := by
  show ((Count.ofNatSucc n).toNat : ℚ) / (1 : Count).toNat = _
  rw [Count.toNat_ofNatSucc, Count.toNat_one']; simp

@[qpp_bridge] theorem toRat_mul (x y : Mass) : toRat (x * y) = toRat x * toRat y := by
  show toRat (x / (1 / y)) = _
  rw [toRat_div, toRat_div, toRat_one]; have := toRat_ne_zero y; field_simp

@[qpp_bridge] theorem toRat_inv (x : Mass) : toRat x⁻¹ = (toRat x)⁻¹ := by
  show toRat (1 / x) = _
  rw [toRat_div, toRat_one, one_div]

@[qpp_bridge] theorem toRat_ofCount (c : Count) : toRat (ofCount c) = (c.toNat : ℚ) := by
  show (c.toNat : ℚ) / (1 : Count).toNat = _; simp [Count.toNat_one']

@[qpp_bridge] theorem toRat_npow (x : Mass) (k : ℕ) : toRat (x ^ k) = toRat x ^ k := by
  induction k with
  | zero => show toRat 1 = _; rw [toRat_one, pow_zero]
  | succ k ih =>
    show toRat (Mass.npow x k * x) = _
    rw [toRat_mul]; exact congrArg (· * toRat x) ih |>.trans (pow_succ _ _).symm

theorem toRat_powCount (x : Mass) (e : Count) : toRat (powCount x e) = toRat x ^ e.toNat := by
  induction e using Count.ind with
  | h1 => exact (pow_one _).symm
  | hs e ih => rw [powCount, toRat_mul, ih, Count.toNat_succ', pow_succ]

@[qpp_bridge] theorem toRat_hpowCount (x : Mass) (e : Count) : toRat (x ^ e) = toRat x ^ e.toNat :=
  toRat_powCount x e

@[qpp_bridge] theorem toRat_hpowCount0 (x : Mass) (e : Count0) : toRat (x ^ e) = toRat x ^ e.toNat := by
  cases e with
  | none => show toRat 1 = toRat x ^ 0; rw [toRat_one, pow_zero]
  | some e => exact toRat_powCount x e

@[qpp_bridge] theorem toRat_lt {x y : Mass} : x < y ↔ toRat x < toRat y := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [toRat_add]; linarith [toRat_pos z]
  · intro h
    refine ⟨ofRat (toRat y - toRat x), toRat_injective ?_⟩
    rw [toRat_add, toRat_ofRat (by linarith)]; ring

@[qpp_bridge] theorem toRat_le {x y : Mass} : x ≤ y ↔ toRat x ≤ toRat y := by
  show x = y ∨ x < y ↔ _
  rw [toRat_lt, toRat_eq, le_iff_eq_or_lt]

@[qpp_bridge] theorem toRat_min (x y : Mass) : toRat (min x y) = min (toRat x) (toRat y) := by
  show toRat (if x ≤ y then x else y) = _
  split_ifs with h
  · rw [toRat_le] at h; exact (min_eq_left h).symm
  · rw [toRat_le] at h; exact (min_eq_right (le_of_lt (not_le.mp h))).symm

@[qpp_bridge] theorem toRat_max (x y : Mass) : toRat (max x y) = max (toRat x) (toRat y) := by
  show toRat (if x ≤ y then y else x) = _
  split_ifs with h
  · rw [toRat_le] at h; exact (max_eq_right h).symm
  · rw [toRat_le] at h; exact (max_eq_left (le_of_lt (not_le.mp h))).symm

end Mass

/-! ## Masses or absent -/

namespace Mass0

/-- The reading of a mass or absent as a rational: absent is `0`. -/
def toRat : Mass0 → ℚ
  | none => 0
  | some x => Mass.toRat x

theorem toRat_nonneg (x : Mass0) : 0 ≤ toRat x := by
  cases x with
  | none => exact le_refl 0
  | some x => exact (Mass.toRat_pos x).le

/-- The reading of a mass or absent as a nonnegative rational. -/
def toNNRat (x : Mass0) : ℚ≥0 := ⟨toRat x, toRat_nonneg x⟩

/-- The mass or absent of a rational at least `0` (absent below). -/
def ofRat (q : ℚ) : Mass0 := if h : 0 < q then of (Mass.ofPos ⟨q, h⟩) else 0

theorem toRat_ofRat {q : ℚ} (h : 0 ≤ q) : toRat (ofRat q) = q := by
  unfold ofRat
  split_ifs with h'
  · exact Mass.toRat_ofPos _
  · exact (le_antisymm (not_lt.mp h') h).symm

/-- The mass or absent of a nonnegative rational. -/
def ofNNRat (q : ℚ≥0) : Mass0 := ofRat q

theorem toRat_injective : Function.Injective toRat := by
  intro x y h
  rcases x with _ | x <;> rcases y with _ | y
  · rfl
  · exact absurd h (Mass.toRat_pos y).ne
  · exact absurd h (Mass.toRat_pos x).ne'
  · exact congrArg some (Mass.toRat_injective h)

/-- `Mass0 ≃ ℚ≥0`. -/
def equivNNRat : Mass0 ≃ ℚ≥0 where
  toFun := toNNRat
  invFun := ofNNRat
  left_inv x := toRat_injective (toRat_ofRat (toRat_nonneg x))
  right_inv q := NNRat.ext (toRat_ofRat q.2)

@[qpp_bridge] theorem coe_toNNRat (x : Mass0) : ((toNNRat x : ℚ≥0) : ℚ) = toRat x := rfl

@[qpp_bridge] theorem toRat_ofNNRat (q : ℚ≥0) : toRat (ofNNRat q) = q := toRat_ofRat q.2

theorem ofNNRat_toNNRat (x : Mass0) : ofNNRat (toNNRat x) = x := equivNNRat.left_inv x

@[qpp_bridge] theorem toRat_eq {x y : Mass0} : x = y ↔ toRat x = toRat y := toRat_injective.eq_iff.symm

@[qpp_bridge] theorem toRat_of (a : Mass) : toRat (of a) = Mass.toRat a := rfl
@[qpp_bridge] theorem toRat_zero : toRat 0 = 0 := rfl
@[qpp_bridge] theorem toRat_one : toRat 1 = 1 := Mass.toRat_one
@[qpp_bridge] theorem toRat_ofNat2 (n : ℕ) : toRat (no_index (OfNat.ofNat (n + 2)) : Mass0) = ((n + 2 : ℕ) : ℚ) :=
  Mass.toRat_ofNat (n + 1)

@[qpp_bridge] theorem toRat_ofCount0 (c : Count0) : toRat (ofCount0 c) = (c.toNat : ℚ) := by
  cases c with
  | none => simp [ofCount0, toRat, Count0.toNat]
  | some c => exact Mass.toRat_ofCount c

@[qpp_bridge] theorem toRat_add (x y : Mass0) : toRat (x + y) = toRat x + toRat y := by
  rcases x with _ | x <;> rcases y with _ | y
  · exact (add_zero 0).symm
  · exact (zero_add _).symm
  · exact (add_zero _).symm
  · exact Mass.toRat_add x y

@[qpp_bridge] theorem toRat_mul (x y : Mass0) : toRat (x * y) = toRat x * toRat y := by
  rcases x with _ | x <;> rcases y with _ | y
  · exact (mul_zero 0).symm
  · exact (zero_mul _).symm
  · exact (mul_zero _).symm
  · exact Mass.toRat_mul x y

@[qpp_bridge] theorem toRat_div (x y : Mass0) : toRat (x / y) = toRat x / toRat y := by
  rcases x with _ | x <;> rcases y with _ | y
  · exact (div_zero 0).symm
  · exact (zero_div _).symm
  · exact (div_zero _).symm
  · exact Mass.toRat_div x y

@[qpp_bridge] theorem toRat_npow (x : Mass0) (k : ℕ) : toRat (x ^ k) = toRat x ^ k := by
  induction k with
  | zero => show toRat 1 = _; rw [toRat_one, pow_zero]
  | succ k ih =>
    show toRat (powNat x k * x) = _
    rw [toRat_mul]; exact congrArg (· * toRat x) ih |>.trans (pow_succ _ _).symm

theorem toRat_powCount (x : Mass0) (e : Count) : toRat (powCount x e) = toRat x ^ e.toNat := by
  induction e using Count.ind with
  | h1 => exact (pow_one _).symm
  | hs e ih => rw [powCount, toRat_mul, ih, Count.toNat_succ', pow_succ]

@[qpp_bridge] theorem toRat_hpowCount (x : Mass0) (e : Count) : toRat (x ^ e) = toRat x ^ e.toNat :=
  toRat_powCount x e

@[qpp_bridge] theorem toRat_hpowCount0 (x : Mass0) (e : Count0) : toRat (x ^ e) = toRat x ^ e.toNat := by
  cases e with
  | none => show toRat 1 = toRat x ^ 0; rw [toRat_one, pow_zero]
  | some e => exact toRat_powCount x e

@[qpp_bridge] theorem toRat_lt {x y : Mass0} : x < y ↔ toRat x < toRat y := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [toRat_add, toRat_of]; linarith [Mass.toRat_pos z]
  · intro h
    refine ⟨Mass.ofRat (toRat y - toRat x), toRat_injective ?_⟩
    rw [toRat_add, toRat_of, Mass.toRat_ofRat (by linarith)]; ring

@[qpp_bridge] theorem toRat_le {x y : Mass0} : x ≤ y ↔ toRat x ≤ toRat y := by
  show x = y ∨ x < y ↔ _
  rw [toRat_lt, toRat_eq, le_iff_eq_or_lt]

@[qpp_bridge] theorem toRat_min (x y : Mass0) : toRat (min x y) = min (toRat x) (toRat y) := by
  show toRat (if x ≤ y then x else y) = _
  split_ifs with h
  · rw [toRat_le] at h; exact (min_eq_left h).symm
  · rw [toRat_le] at h; exact (min_eq_right (le_of_lt (not_le.mp h))).symm

@[qpp_bridge] theorem toRat_max (x y : Mass0) : toRat (max x y) = max (toRat x) (toRat y) := by
  show toRat (if x ≤ y then y else x) = _
  split_ifs with h
  · rw [toRat_le] at h; exact (max_eq_right h).symm
  · rw [toRat_le] at h; exact (max_eq_left (le_of_lt (not_le.mp h))).symm

/-- The deficit is `max (a - b) 0`. -/
@[qpp_bridge] theorem toRat_deficit (a b : Mass0) : toRat (deficit a b) = max (toRat a - toRat b) 0 := by
  unfold deficit
  split_ifs with h
  · have e := congrArg toRat (Classical.choose_spec h)
    rw [toRat_add, toRat_of] at e
    rw [toRat_of, e, add_sub_cancel_left, max_eq_left (Mass.toRat_pos _).le]
  · rw [toRat_lt, not_lt] at h
    rw [toRat_zero, max_eq_right (by linarith)]

@[qpp_bridge] theorem toRat_iverson (P : Prop) [Decidable P] : toRat (iverson P) = if P then 1 else 0 := by
  unfold iverson; split_ifs
  · exact toRat_one
  · rfl

/-! The reading in `ℚ≥0` (the content of a pair, `PairLM.toMath`), pushed to the leaves: a mass `a` read as
`(Mass.toRat a).toNNRat`, a count as its cast, a numeral as itself, as the content of a literal pair is written over
Mathlib; the reading of a mass or absent in `ℚ`, made nonnegative, is its reading in `ℚ≥0`. -/

@[qpp_bridge] theorem toNNRat_of (a : Mass) : toNNRat (of a) = (Mass.toRat a).toNNRat :=
  NNRat.ext (by rw [coe_toNNRat, toRat_of, Rat.coe_toNNRat _ (Mass.toRat_pos a).le])

@[qpp_bridge] theorem toRat_toNNRat (x : Mass0) : (toRat x).toNNRat = toNNRat x :=
  NNRat.ext (by rw [coe_toNNRat, Rat.coe_toNNRat _ (toRat_nonneg x)])

@[qpp_bridge] theorem toNNRat_zero : toNNRat 0 = 0 :=
  NNRat.ext (by rw [coe_toNNRat, toRat_zero, NNRat.coe_zero])

@[qpp_bridge] theorem toNNRat_one : toNNRat 1 = 1 :=
  NNRat.ext (by rw [coe_toNNRat, toRat_one, NNRat.coe_one])

@[qpp_bridge] theorem toNNRat_ofNat2 (n : ℕ) :
    toNNRat (no_index (OfNat.ofNat (n + 2)) : Mass0) = ((n + 2 : ℕ) : ℚ≥0) :=
  NNRat.ext (by simp only [coe_toNNRat, toRat_ofNat2, NNRat.coe_natCast])

@[qpp_bridge] theorem toNNRat_ofCount0 (c : Count0) : toNNRat (ofCount0 c) = (c.toNat : ℚ≥0) :=
  NNRat.ext (by rw [coe_toNNRat, toRat_ofCount0, NNRat.coe_natCast])

@[qpp_bridge] theorem toNNRat_add (x y : Mass0) : toNNRat (x + y) = toNNRat x + toNNRat y :=
  NNRat.ext (by simp only [NNRat.coe_add, coe_toNNRat, toRat_add])

@[qpp_bridge] theorem toNNRat_mul (x y : Mass0) : toNNRat (x * y) = toNNRat x * toNNRat y :=
  NNRat.ext (by simp only [NNRat.coe_mul, coe_toNNRat, toRat_mul])

@[qpp_bridge] theorem toNNRat_div (x y : Mass0) : toNNRat (x / y) = toNNRat x / toNNRat y :=
  NNRat.ext (by simp only [NNRat.coe_div, coe_toNNRat, toRat_div])

@[qpp_bridge] theorem toNNRat_min (x y : Mass0) : toNNRat (min x y) = min (toNNRat x) (toNNRat y) :=
  NNRat.ext (by simp only [NNRat.coe_min, coe_toNNRat, toRat_min])

@[qpp_bridge] theorem toNNRat_max (x y : Mass0) : toNNRat (max x y) = max (toNNRat x) (toNNRat y) :=
  NNRat.ext (by simp only [NNRat.coe_max, coe_toNNRat, toRat_max])

@[qpp_bridge] theorem toNNRat_npow (x : Mass0) (k : ℕ) : toNNRat (x ^ k) = toNNRat x ^ k :=
  NNRat.ext (by simp only [NNRat.coe_pow, coe_toNNRat, toRat_npow])

@[qpp_bridge] theorem toNNRat_hpowCount (x : Mass0) (e : Count) : toNNRat (x ^ e) = toNNRat x ^ e.toNat :=
  NNRat.ext (by simp only [NNRat.coe_pow, coe_toNNRat, toRat_hpowCount])

@[qpp_bridge] theorem toNNRat_hpowCount0 (x : Mass0) (e : Count0) : toNNRat (x ^ e) = toNNRat x ^ e.toNat :=
  NNRat.ext (by simp only [NNRat.coe_pow, coe_toNNRat, toRat_hpowCount0])

end Mass0

end Qpp
