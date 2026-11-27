module

public import QppBridge.Sums
public import Mathlib.Order.WithBot
public import Mathlib.Order.OrderDual
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# The bridge of balances and of the pair

A balance `Bal Mass` (a pair of masses, `l` less `r`) is read as the rational `l - r` (`Bal.toRat`): the tie is
equality, the level pair is `0`, `swap` is the negation, and every rational is the reading of a balance.

The pair `(l, m)` of the kernel (`PairLM`) is read as the pair of Mathlib, `WithTop (Lex (ℚ≥0 × ℕᵒᵈ))` with
`(l, m) ↦ (l, m - 1)` (`QppMathlib.Pair.mk`): order, sum, least and equality are carried over, and the least over a
range of candidates, `0..b` (`infUpTo`) or `1..J` with `J` a count (`infFrom1`), is `Finset.inf` over `Finset.Icc`.
Neither range is empty.
-/

@[expose] public section

/-! ## The pair of Mathlib -/

namespace QppMathlib

/-- The pair: a content in `ℚ≥0` and an order in `ℕ`, ordered by content and then by the larger order, or `⊤`. -/
abbrev Pair : Type := WithTop (Lex (Prod NNRat (OrderDual Nat)))

/-- The pair `(l, m)` as `(l, o)` with `o = m - 1`: the sum of pairs is `+`. -/
def Pair.mk (l : NNRat) (o : ℕ) : Pair := ((toLex (l, OrderDual.toDual o) : Lex (Prod NNRat (OrderDual ℕ))) : Pair)

theorem Pair.mk_le {l l' : NNRat} {o o' : ℕ} : Pair.mk l o ≤ Pair.mk l' o' ↔ l < l' ∨ (l = l' ∧ o' ≤ o) := by
  simp [Pair.mk, Prod.Lex.le_iff]

theorem Pair.mk_add (l l' : NNRat) (o o' : ℕ) : Pair.mk l o + Pair.mk l' o' = Pair.mk (l + l') (o + o') := rfl

theorem Pair.mk_eq {l l' : NNRat} {o o' : ℕ} : Pair.mk l o = Pair.mk l' o' ↔ l = l' ∧ o = o' := by
  simp [Pair.mk]

end QppMathlib

namespace Qpp

/-! ## Balances -/

namespace Bal

/-- The reading of a balance: `l - r`. -/
def toRat (b : Bal Mass) : ℚ := b.l.toRat - b.r.toRat

theorem toRat_add (a b : Bal Mass) : (a + b).toRat = a.toRat + b.toRat := by
  show (a.l + b.l).toRat - (a.r + b.r).toRat = _
  simp only [toRat, Mass.toRat_add]; ring

theorem toRat_mul (a b : Bal Mass) : (a * b).toRat = a.toRat * b.toRat := by
  show (a.l * b.l + a.r * b.r).toRat - (a.l * b.r + a.r * b.l).toRat = _
  simp only [toRat, Mass.toRat_add, Mass.toRat_mul]; ring

theorem toRat_swap (a : Bal Mass) : (swap a).toRat = - a.toRat := by
  show a.r.toRat - a.l.toRat = _; simp only [toRat]; ring

theorem toRat_level : (level : Bal Mass).toRat = 0 := by
  show (1 : Mass).toRat - (1 : Mass).toRat = 0; ring

theorem toRat_of (a : Mass) : (Bal.of a).toRat = a.toRat := by
  show (a + 1).toRat - (1 : Mass).toRat = _; rw [Mass.toRat_add, Mass.toRat_one]; ring

theorem tie_iff {a b : Bal Mass} : Tie a b ↔ a.toRat = b.toRat := by
  show a.l + b.r = b.l + a.r ↔ _
  rw [Mass.toRat_eq, Mass.toRat_add, Mass.toRat_add]; unfold toRat
  constructor <;> intro h <;> linarith

/-- The balance of a rational `q`: `q + (|q| + 1)` less `|q| + 1`. -/
noncomputable def ofRat (q : ℚ) : Bal Mass := ⟨Mass.ofRat (q + (|q| + 1)), Mass.ofRat (|q| + 1)⟩

theorem toRat_ofRat (q : ℚ) : (ofRat q).toRat = q := by
  have h1 : 0 < |q| + 1 := by positivity
  have h2 : 0 < q + (|q| + 1) := by have := neg_abs_le q; linarith
  show (Mass.ofRat _).toRat - (Mass.ofRat _).toRat = q
  rw [Mass.toRat_ofRat h1, Mass.toRat_ofRat h2]; ring

end Bal

theorem Mass0.toRat_toBal (x : Mass0) : (Mass0.toBal x).toRat = x.toRat := by
  cases x with
  | none => exact Bal.toRat_level
  | some a => exact Bal.toRat_of a

/-! ## The pair -/

namespace PairLM

/-- The reading of a pair: `top` is `⊤`, and `(l, m)` is `(l, m - 1)`. -/
noncomputable def toMath : PairLM → QppMathlib.Pair
  | top => ⊤
  | mk l m => QppMathlib.Pair.mk l.toNNRat (m.toNat - 1)

theorem le_def {p q : PairLM} : p ≤ q ↔ PairLM.Le p q := Iff.rfl

theorem nnrat_lt {x y : Mass0} : x < y ↔ x.toNNRat < y.toNNRat := by
  rw [Mass0.toRat_lt, ← NNRat.coe_lt_coe, Mass0.coe_toNNRat, Mass0.coe_toNNRat]

theorem nnrat_eq {x y : Mass0} : x = y ↔ x.toNNRat = y.toNNRat := by
  rw [Mass0.toRat_eq, ← NNRat.coe_inj, Mass0.coe_toNNRat, Mass0.coe_toNNRat]

theorem pred_le {m m' : Count} : m' ≤ m ↔ m'.toNat - 1 ≤ m.toNat - 1 := by
  have := Count.toNat_pos m; have := Count.toNat_pos m'
  rw [Count.toNat_le]; omega

@[qpp_bridge] theorem toMath_le {p q : PairLM} : p ≤ q ↔ p.toMath ≤ q.toMath := by
  rw [le_def]
  cases p with
  | top =>
    cases q with
    | top => exact iff_of_true trivial le_rfl
    | mk l' m' => exact iff_of_false id (WithTop.not_top_le_coe _)
  | mk l m =>
    cases q with
    | top => exact iff_of_true trivial le_top
    | mk l' m' =>
      show (l < l' ∨ (l = l' ∧ m' ≤ m)) ↔ QppMathlib.Pair.mk _ _ ≤ QppMathlib.Pair.mk _ _
      rw [QppMathlib.Pair.mk_le, nnrat_lt, nnrat_eq, pred_le]

theorem toMath_injective : Function.Injective toMath := by
  intro p q h
  cases p with
  | top =>
    cases q with
    | top => rfl
    | mk l' m' => exact absurd h.symm (WithTop.coe_ne_top)
  | mk l m =>
    cases q with
    | top => exact absurd h (WithTop.coe_ne_top)
    | mk l' m' =>
      obtain ⟨h1, h2⟩ := QppMathlib.Pair.mk_eq.1 h
      have := Count.toNat_pos m; have := Count.toNat_pos m'
      rw [nnrat_eq.2 h1, Count.toNat_eq.2 (by omega : m.toNat = m'.toNat)]

@[qpp_bridge] theorem toMath_eq {p q : PairLM} : p = q ↔ p.toMath = q.toMath :=
  toMath_injective.eq_iff.symm

@[qpp_bridge] theorem toMath_lt {p q : PairLM} : p < q ↔ p.toMath < q.toMath := by
  show (p ≤ q ∧ ¬ q ≤ p) ↔ _
  rw [toMath_le, toMath_le, lt_iff_le_not_ge]

@[qpp_bridge] theorem toMath_top : toMath top = ⊤ := rfl

@[qpp_bridge] theorem toMath_mk (l : Mass0) (m : Count) : toMath (mk l m) = QppMathlib.Pair.mk l.toNNRat (m.toNat - 1) := rfl

theorem toNat_addMult (m m' : Count) : (addMult m m').toNat - 1 = (m.toNat - 1) + (m'.toNat - 1) := by
  cases m' with
  | one => show m.toNat - 1 = _ + (1 - 1); omega
  | succ m' =>
    show (m + m').toNat - 1 = _ + (m'.toNat + 1 - 1)
    rw [Count.toNat_add]; have := Count.toNat_pos m; omega

@[qpp_bridge] theorem toMath_add (p q : PairLM) : (p + q).toMath = p.toMath + q.toMath := by
  cases p with
  | top => cases q <;> rfl
  | mk l m =>
    cases q with
    | top => rfl
    | mk l' m' =>
      show toMath (mk (l + l') (addMult m m')) = _
      rw [toMath_mk, toMath_mk, toMath_mk, QppMathlib.Pair.mk_add, toNat_addMult]
      congr 1
      exact NNRat.ext (by simp only [NNRat.coe_add, Mass0.coe_toNNRat, Mass0.toRat_add])

@[qpp_bridge] theorem toMath_min (p q : PairLM) : (min p q).toMath = min p.toMath q.toMath := by
  show (least p q).toMath = _
  unfold least
  by_cases h : p ≤ q
  · rw [ite_eq_left h, min_eq_left (toMath_le.1 h)]
  · rw [ite_eq_right h, min_eq_right (le_of_not_ge (fun h' => h (toMath_le.2 h')))]

/-! ## The tropical sum over a range: `Finset.inf` over `Finset.Icc` -/

theorem toMath_infTo0 (g : Count0 → PairLM) (c : Count) :
    (infTo0 g c).toMath = (Finset.range (c.toNat + 1)).inf (fun v => (g (Count0.ofNat v)).toMath) := by
  induction c using Count.ind with
  | h1 =>
    show (min (g 0) (g 1)).toMath = _
    rw [toMath_min]
    simp only [Finset.range_add_one, Count.toNat_one', Finset.range_zero, insert_empty_eq, Finset.inf_insert,
      Finset.inf_singleton]
    exact min_comm _ _
  | hs c ih =>
    show (min (infTo0 g c) (g (Count0.of (.succ c)))).toMath = _
    rw [toMath_min, ih, Count.toNat_succ', Finset.range_add_one (n := c.toNat + 1), Finset.inf_insert, inf_comm]
    rw [show Count0.ofNat (c.toNat + 1) = Count0.of c.succ from congrArg Count0.of (ofNatSucc_toNat c)]

@[qpp_bridge] theorem toMath_infUpTo (b : Count0) (g : Count0 → PairLM) :
    (infUpTo b g).toMath = (Finset.Icc 0 b.toNat).inf (fun v => (g (Count0.ofNat v)).toMath) := by
  rw [← Nat.range_succ_eq_Icc_zero]
  cases b with
  | none => show (g 0).toMath = (Finset.range 1).inf _; simp only [Finset.range_one, Finset.inf_singleton]; rfl
  | some c => exact toMath_infTo0 g c

@[qpp_bridge] theorem toMath_infFrom1 (g : Count0 → PairLM) (J : Count) :
    (infFrom1 g J).toMath = (Finset.Icc 1 J.toNat).inf (fun v => (g (Count0.ofNat v)).toMath) := by
  induction J using Count.ind with
  | h1 =>
    show (g 1).toMath = _
    rw [Count.toNat_one', Finset.Icc_self, Finset.inf_singleton]; rfl
  | hs c ih =>
    show (min (infFrom1 g c) (g (Count0.of (.succ c)))).toMath = _
    rw [toMath_min, ih, Count.toNat_succ', ← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.inf_insert,
      inf_comm]
    rw [show Count0.ofNat (c.toNat + 1) = Count0.of c.succ from congrArg Count0.of (ofNatSucc_toNat c)]

end PairLM

end Qpp
