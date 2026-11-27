module

/-!
# The base: counts, masses, the order, pairs, sums and cited facts

Everything that a generated statement may name, in one module that imports nothing: counts, masses, the order of
both, pairs of masses (the rationals), the words read by relation (min, max, the indicator), sums over the counts
and the source of a cited fact. Its proofs use the laws of counts and no tactic of the
kernel, so a Palomar Challenge repeats it verbatim (a Challenge may import Lean core only), and one module keeps
the auxiliary declarations of its definitions (matchers) those of the library; the rest of the kernel builds on
it.

## Counts

The counts are `1` and its successors, an inductive type with two constructors. Its recursor is `ind` (a property
of `1` kept by the successor holds for every count), and its no-confusion principle is `neq` (`1` is no successor,
and the successor is injective). Sum and product are defined by recursion, and their laws are proved here once,
by `ind` and `neq` alone.

`toNat` sends a count to Lean's numeral of the same size. It is used only by the tactics that replay certificates,
because the kernel computes with those numerals in binary.

## Masses, the order, sums, cited facts

A mass is a pair of counts `(p, q)`, read `p / q`, up to the tie: `p / q` and `r / s` are the same mass when
`p * s = r * q`. The quotient (`Quotient`, with the axiom `Quot.sound`) is what lets `=` mean the tie. Sum and
division are defined on pairs, `1` is `1 / 1`; product and inverse are derived, `x * y := x / (1 / y)` and
`x⁻¹ := 1 / x`, as in Q++. `a < b` when `b` is `a` plus something. There is no zero: the sum of no terms is absent
(`none`, `osum`); a sum or a product over the counts `1, ..., n` is never empty (`sumTo`, `prodTo`). A cited fact is
a statement taken as a hypothesis, with its source: a DOI and, optionally, the number of the statement.
-/

@[expose] public section

-- the congruences of masses rewrite with one list of laws of counts each, not all of which each step uses
set_option linter.unusedSimpArgs false

namespace Qpp

/-- The counts: `1` and its successors. -/
inductive Count where
  | one : Count
  | succ : Count → Count

namespace Count

/-- The count `n + 1`, for a numeral `n` of Lean: the numerals `1, 2, 3, ...` of the counts. -/
def ofNatSucc : Nat → Count
  | 0 => one
  | n + 1 => succ (ofNatSucc n)

instance (n : Nat) : OfNat Count (n + 1) := ⟨ofNatSucc n⟩

theorem one_def : one = 1 := rfl

/-- `ind`: a property of `1` kept by the successor holds for every count (the recursor of `Count`). -/
theorem ind {P : Count → Prop} (h1 : P 1) (hs : ∀ n, P n → P (succ n)) (n : Count) : P n :=
  Count.rec (motive := P) h1 hs n

/-- `neq`: `1` is no successor (no confusion). -/
theorem succ_ne_one (n : Count) : succ n ≠ 1 := fun h => Count.noConfusion h

/-- `neq`: the successor is injective (no confusion). -/
theorem succ_inj {a b : Count} (h : succ a = succ b) : a = b := Count.noConfusion h id

/-! ## Sum -/

/-- The sum, by recursion on the second argument: `a + 1` is the successor of `a`. -/
protected def add : Count → Count → Count
  | a, one => succ a
  | a, succ b => succ (Count.add a b)

instance : Add Count := ⟨Count.add⟩

theorem add_one (a : Count) : a + 1 = succ a := rfl
theorem add_succ (a b : Count) : a + succ b = succ (a + b) := rfl

theorem one_add (a : Count) : 1 + a = succ a := by
  induction a using ind with
  | h1 => rfl
  | hs a ih => show succ (1 + a) = _; rw [ih]

theorem succ_add (a b : Count) : succ a + b = succ (a + b) := by
  induction b using ind with
  | h1 => rfl
  | hs b ih => show succ (succ a + b) = _; rw [ih]; rfl

theorem add_assoc (a b c : Count) : a + b + c = a + (b + c) := by
  induction c using ind with
  | h1 => rfl
  | hs c ih => show succ (a + b + c) = succ (a + (b + c)); rw [ih]

theorem add_comm (a b : Count) : a + b = b + a := by
  induction b using ind with
  | h1 => rw [add_one, one_add]
  | hs b ih => rw [add_succ, succ_add, ih]

/-- No count is the sum of itself and another (the strong form of `neq`). -/
theorem add_ne_left (a b : Count) : a + b ≠ a := by
  induction a using ind with
  | h1 => rw [one_add]; exact succ_ne_one b
  | hs a ih => rw [succ_add]; exact fun h => ih (succ_inj h)

theorem add_right_cancel {a b c : Count} (h : a + c = b + c) : a = b := by
  induction c using ind with
  | h1 => exact succ_inj h
  | hs c ih => exact ih (succ_inj h)

theorem add_left_cancel {a b c : Count} (h : c + a = c + b) : a = b := by
  rw [add_comm c a, add_comm c b] at h; exact add_right_cancel h

/-! ## Product -/

/-- The product, by recursion on the second argument: `a * (b + 1) = a * b + a`. -/
protected def mul : Count → Count → Count
  | a, one => a
  | a, succ b => Count.mul a b + a

instance : Mul Count := ⟨Count.mul⟩

theorem mul_one (a : Count) : a * 1 = a := rfl
theorem mul_succ (a b : Count) : a * succ b = a * b + a := rfl

theorem one_mul (a : Count) : 1 * a = a := by
  induction a using ind with
  | h1 => rfl
  | hs a ih => rw [mul_succ, ih, add_one]

theorem succ_mul (a b : Count) : succ a * b = a * b + b := by
  induction b using ind with
  | h1 => rfl
  | hs b ih => rw [mul_succ, mul_succ, ih, add_succ, add_succ, add_assoc, add_assoc, add_comm b a]

theorem mul_comm (a b : Count) : a * b = b * a := by
  induction b using ind with
  | h1 => rw [mul_one, one_mul]
  | hs b ih => rw [mul_succ, succ_mul, ih]

theorem mul_add (a b c : Count) : a * (b + c) = a * b + a * c := by
  induction c using ind with
  | h1 => rfl
  | hs c ih => rw [add_succ, mul_succ, mul_succ, ih, add_assoc]

theorem add_mul (a b c : Count) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

theorem mul_assoc (a b c : Count) : a * b * c = a * (b * c) := by
  induction c using ind with
  | h1 => rfl
  | hs c ih => rw [mul_succ, mul_succ, ih, mul_add]

theorem mul_left_comm (a b c : Count) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

theorem mul_right_cancel {a b c : Count} (h : a * c = b * c) : a = b := by
  induction a using ind generalizing b with
  | h1 =>
    cases b with
    | one => rfl
    | succ b => rw [one_mul, succ_mul, add_comm] at h; exact absurd h.symm (add_ne_left c (b * c))
  | hs a ih =>
    cases b with
    | one => rw [one_def, one_mul, succ_mul, add_comm] at h; exact absurd h (add_ne_left c (a * c))
    | succ b => rw [succ_mul, succ_mul] at h; rw [ih (add_right_cancel h)]

/-! ## Powers -/

/-- `a ^ k` for a numeral `k` of Lean; `a ^ 0 = 1` is the empty product. -/
protected def npow (a : Count) : Nat → Count
  | 0 => 1
  | k + 1 => Count.npow a k * a

instance : NatPow Count := ⟨Count.npow⟩

theorem pow_succ (a : Count) (k : Nat) : a ^ (k + 1) = a ^ k * a := rfl

/-! ## The numeral of a count -/

/-- The numeral of Lean of the same size: `1 ↦ 1`, `succ n ↦ n + 1`. -/
def toNat : Count → Nat
  | one => 1
  | succ n => toNat n + 1

theorem toNat_succ (n : Count) : toNat (succ n) = toNat n + 1 := rfl

theorem toNat_ofNatSucc (n : Nat) : toNat (ofNatSucc n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => show toNat (ofNatSucc n) + 1 = _; rw [ih]

theorem toNat_add (a b : Count) : toNat (a + b) = toNat a + toNat b := by
  induction b using ind with
  | h1 => rfl
  | hs b ih => show toNat (a + b) + 1 = toNat a + (toNat b + 1); rw [ih, Nat.add_assoc]

theorem toNat_mul (a b : Count) : toNat (a * b) = toNat a * toNat b := by
  induction b using ind with
  | h1 => exact (Nat.mul_one _).symm
  | hs b ih => rw [mul_succ, toNat_add, ih, toNat_succ, Nat.mul_succ]

theorem toNat_pow (a : Count) (k : Nat) : toNat (a ^ k) = toNat a ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, toNat_mul, ih, Nat.pow_succ]

theorem toNat_pos (a : Count) : 0 < toNat a := by
  cases a with
  | one => exact Nat.one_pos
  | succ a => exact Nat.succ_pos _

theorem toNat_inj {a b : Count} (h : toNat a = toNat b) : a = b := by
  induction a using ind generalizing b with
  | h1 =>
    cases b with
    | one => rfl
    | succ b => have := toNat_pos b; have h' : 1 = toNat b + 1 := h; omega
  | hs a ih =>
    cases b with
    | one => have := toNat_pos a; have h' : toNat a + 1 = 1 := h; omega
    | succ b => rw [ih (Nat.succ.inj h)]

end Count

/-- A power by a numeral is a power by a numeral of Lean. Without it the elaborator leaves the type of each exponent
open and settles it by default instances at the end, at a cost quadratic in the number of powers. -/
scoped macro_rules | `($x ^ $n:num) => `(HPow.hPow $x ($n : Nat))

/-! ## Masses -/

/-- A pair of counts `(p, q)`: the mass `p / q`. -/
structure Pair where
  num : Count
  den : Count

namespace Pair

/-- The tie of two pairs: `p / q` and `r / s` are the same mass when `p * s = r * q`. -/
def Tie (a b : Pair) : Prop := a.num * b.den = b.num * a.den

theorem Tie.trans {a b c : Pair} (h1 : Tie a b) (h2 : Tie b c) : Tie a c := by
  unfold Tie at *
  apply Count.mul_right_cancel (c := b.den)
  calc a.num * c.den * b.den = (a.num * b.den) * c.den := by
        simp only [Count.mul_assoc, Count.mul_comm c.den]
    _ = (b.num * a.den) * c.den := by rw [h1]
    _ = (b.num * c.den) * a.den := by simp only [Count.mul_assoc, Count.mul_comm a.den]
    _ = (c.num * b.den) * a.den := by rw [h2]
    _ = c.num * a.den * b.den := by simp only [Count.mul_assoc, Count.mul_comm a.den]

instance setoid : Setoid Pair := ⟨Tie, ⟨fun _ => rfl, Eq.symm, Tie.trans⟩⟩

end Pair

/-- The masses: pairs of counts up to the tie. -/
def Mass : Type := Quotient Pair.setoid

namespace Mass

/-- The mass `p / q`. -/
def mk (p q : Count) : Mass := Quotient.mk _ ⟨p, q⟩

theorem mk_eq_mk {p q r s : Count} : mk p q = mk r s ↔ p * s = r * q :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- The numerals `1, 2, 3, ...` of the masses. -/
instance (n : Nat) : OfNat Mass (n + 1) := ⟨mk (OfNat.ofNat (n + 1)) 1⟩

/-- The sum: `p / q + r / s = (p * s + r * q) / (q * s)`. -/
protected def add : Mass → Mass → Mass :=
  Quotient.lift₂ (fun a b => mk (a.num * b.den + b.num * a.den) (a.den * b.den)) fun a b a' b' h1 h2 => by
    apply mk_eq_mk.mpr
    change a.num * a'.den = a'.num * a.den at h1
    change b.num * b'.den = b'.num * b.den at h2
    calc (a.num * b.den + b.num * a.den) * (a'.den * b'.den)
        = (a.num * a'.den) * (b.den * b'.den) + (b.num * b'.den) * (a.den * a'.den) := by
          simp only [Count.add_mul, Count.mul_add, Count.mul_assoc, Count.mul_comm, Count.mul_left_comm]
      _ = (a'.num * a.den) * (b.den * b'.den) + (b'.num * b.den) * (a.den * a'.den) := by rw [h1, h2]
      _ = (a'.num * b'.den + b'.num * a'.den) * (a.den * b.den) := by
          simp only [Count.add_mul, Count.mul_add, Count.mul_assoc, Count.mul_comm, Count.mul_left_comm]

/-- The division: `(p / q) / (r / s) = (p * s) / (q * r)`. -/
protected def div : Mass → Mass → Mass :=
  Quotient.lift₂ (fun a b => mk (a.num * b.den) (a.den * b.num)) fun a b a' b' h1 h2 => by
    apply mk_eq_mk.mpr
    change a.num * a'.den = a'.num * a.den at h1
    change b.num * b'.den = b'.num * b.den at h2
    calc a.num * b.den * (a'.den * b'.num) = (a.num * a'.den) * (b'.num * b.den) := by
          simp only [Count.mul_assoc, Count.mul_comm, Count.mul_left_comm]
      _ = (a'.num * a.den) * (b.num * b'.den) := by rw [h1, h2]
      _ = a'.num * b'.den * (a.den * b.num) := by
          simp only [Count.mul_assoc, Count.mul_comm, Count.mul_left_comm]

instance : Add Mass := ⟨Mass.add⟩
instance : Div Mass := ⟨Mass.div⟩
/-- The product, derived: `x * y := x / (1 / y)`. -/
instance : Mul Mass := ⟨fun x y => x / (1 / y)⟩
/-- The inverse, derived: `x⁻¹ := 1 / x`. -/
instance : Inv Mass := ⟨fun x => 1 / x⟩

/-- `x ^ k` for a numeral `k` of Lean; `x ^ 0 = 1` is the empty product. -/
protected def npow (x : Mass) : Nat → Mass
  | 0 => 1
  | k + 1 => Mass.npow x k * x

instance : NatPow Mass := ⟨Mass.npow⟩

/-- A count as a mass: `n / 1`. -/
def ofCount (n : Count) : Mass := mk n 1

end Mass

/-! ## The order -/

namespace Count

protected def Lt (a b : Count) : Prop := ∃ c, b = a + c

instance : LT Count := ⟨Count.Lt⟩
instance : LE Count := ⟨fun a b => a = b ∨ a < b⟩

end Count

namespace Mass

/-- `x < y`: `y` is `x` plus a mass. -/
protected def Lt (x y : Mass) : Prop := ∃ z, y = x + z

instance : LT Mass := ⟨Mass.Lt⟩
instance : LE Mass := ⟨fun x y => x = y ∨ x < y⟩

end Mass

/-! ## Sums -/

section Sums

variable {α : Type} [Add α]

/-- The sum of two possibly absent terms; absent is the unit. -/
def oadd : Option α → Option α → Option α
  | none, y => y
  | some x, none => some x
  | some x, some y => some (x + y)

/-- The sum of a list; absent when the list is empty. -/
def osum : List α → Option α
  | [] => none
  | x :: l => oadd (some x) (osum l)

/-- The count of a list: one `1` per entry; absent when the list is empty. -/
def card {β : Type} (l : List β) : Option Count := osum (l.map fun _ => (1 : Count))

end Sums

/-- `Σ_{i=1}^{n} f i`, a sum over the counts up to `n`. -/
def sumTo {β : Type} [Add β] (f : Count → β) : Count → β
  | .one => f 1
  | .succ n => sumTo f n + f (.succ n)

/-- `Π_{i=1}^{n} f i`, a product over the counts up to `n`. -/
def prodTo {β : Type} [Mul β] (f : Count → β) : Count → β
  | .one => f 1
  | .succ n => prodTo f n * f (.succ n)

/-! ## Pairs

A pair `⟨l, r⟩` stands for `l` less `r`; two pairs are tied when `a.l + b.r = b.l + a.r`. The rationals are the
pairs of masses: a statement over `ℚ` is one over `Bal Mass` in which `=` is the tie (`Bal.Tie`), `0` is the level
pair `⟨1, 1⟩` and `-a` is `swap a`. -/

/-- A pair: `l` less `r`. -/
structure Bal (α : Type) where
  l : α
  r : α

namespace Bal

variable {α : Type}

/-- Two pairs stand for the same: `a.l + b.r = b.l + a.r`. -/
def Tie [Add α] (a b : Bal α) : Prop := a.l + b.r = b.l + a.r

instance [Add α] : Add (Bal α) := ⟨fun a b => ⟨a.l + b.l, a.r + b.r⟩⟩

instance [Add α] [Mul α] : Mul (Bal α) := ⟨fun a b => ⟨a.l * b.l + a.r * b.r, a.l * b.r + a.r * b.l⟩⟩

/-- The pair the other way round: `r` less `l`. -/
def swap (a : Bal α) : Bal α := ⟨a.r, a.l⟩

/-- `a < b`: `a.l + b.r < b.l + a.r`. -/
protected def Lt [Add α] [LT α] (a b : Bal α) : Prop := a.l + b.r < b.l + a.r

instance [Add α] [LT α] : LT (Bal α) := ⟨Bal.Lt⟩

instance [Add α] [LT α] : LE (Bal α) := ⟨fun a b => Tie a b ∨ a < b⟩

/-- `x` as a pair: `x + 1` less `1`. -/
def of [Add α] [OfNat α 1] (x : α) : Bal α := ⟨x + 1, 1⟩

/-- A pair that stands for nothing. -/
def level [OfNat α 1] : Bal α := ⟨1, 1⟩

/-- Powers by a natural number; the power `0` is `of 1`. -/
protected def npow [Add α] [Mul α] [OfNat α 1] (a : Bal α) : Nat → Bal α
  | 0 => ⟨1 + 1, 1⟩
  | k + 1 => Bal.npow a k * a

instance [Add α] [Mul α] [OfNat α 1] : NatPow (Bal α) := ⟨Bal.npow⟩

end Bal

/-- A numeral of Lean as a pair: `0` is the level pair. -/
def Bal.nat : Nat → Bal Mass
  | 0 => Bal.level
  | n + 1 => Bal.of (Mass.ofCount (Count.ofNatSucc n))

/-- The values `0` and `1` of a pair, for a vector in `{0,1}^k`. -/
def Bal.IsBit (s : Bal Mass) : Prop := Bal.Tie s Bal.level ∨ Bal.Tie s (Bal.of 1)

/-! ## Words read by relation

No rational function is the larger of two masses, so `max`, `min`, the positive part `(x)_+ = max(x, 0)`, the
size `|x| = max(x, -x)` and the indicator `1[P]` are not words of `1`, `+` and `/`. A statement reads each one as a
name bound by its relation; the relation needs only the order, and its solution exists and is unique up to ties
(`MinMax.lean`). -/

section Relations

variable {α : Type}

/-- `m` is the least of `a` and `b`. -/
def IsMin [LE α] (m a b : α) : Prop := (m = a ∧ a ≤ b) ∨ (m = b ∧ b ≤ a)

/-- `m` is the greatest of `a` and `b`. -/
def IsMax [LE α] (m a b : α) : Prop := (m = a ∧ b ≤ a) ∨ (m = b ∧ a ≤ b)

/-- `m` is the least entry of the list `l`. -/
def IsLeast [LE α] (m : α) (l : List α) : Prop := m ∈ l ∧ ∀ x ∈ l, m ≤ x

/-- `m` is the greatest entry of the list `l`. -/
def IsGreatest [LE α] (m : α) (l : List α) : Prop := m ∈ l ∧ ∀ x ∈ l, x ≤ m

/-- `y` is the indicator `1[P]` of the proposition `P`: `1` if it holds, `0` if not. -/
def IsInd (y : Bal Mass) (P : Prop) : Prop := (P ∧ Bal.Tie y (Bal.of 1)) ∨ (¬P ∧ Bal.Tie y Bal.level)

end Relations

/-! ## Binomial coefficients and sums from zero -/

/-- The binomial coefficient `binom n k`, by Pascal's rule. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- `Σ_{h=1}^{n} f h` over the counts up to a numeral `n` of Lean, with the value `z` when `n = 0`. -/
def sumN {β : Type} [Add β] (z : β) (f : Count → β) : Nat → β
  | 0 => z
  | n + 1 => sumN z f n + f (Count.ofNatSucc n)

/-- `Σ_{i=0}^{n-1} f i` over the numerals of Lean below `n`, with the value `z` when `n = 0`. -/
def sumBelow {β : Type} [Add β] (z : β) (f : Nat → β) : Nat → β
  | 0 => z
  | n + 1 => sumBelow z f n + f n

/-! ## Cited facts -/

/-- The source of a cited fact: a DOI and, optionally, the number of the statement. -/
structure Source where
  doi : String
  stmt : Option String := none

/-- A cited fact: a statement over the core, taken as a hypothesis by the results that use it, and its source. -/
structure Cited where
  statement : Prop
  source : Source

end Qpp
