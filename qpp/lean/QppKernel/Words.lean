module

public import QppKernel.Base

/-!
# The words of the modules

What a statement of the modules names beyond `Base`, defined over its counts and masses with Lean core alone:

* zero as absent: `Mass0` (a mass or absent, `QQ>=0`) and `Count0` (a count or absent, `NN`), with their sums,
  products, quotients, powers and order, and the casts between the four;
* the deficit `max(a - b, 0)` (absent when `a ≤ b`, otherwise the mass `c` with `a = b + c`), the least and the
  greatest of two, and the indicator `iverson(P)`;
* indices as counts: `Idx n`, the counts `1, ..., n`; a tuple of `X^n` is a function on `Idx n`;
* sums and products over the indices of a tuple, over a range `a..b`, and over the lattice points of a box `u ≤ b`;
* the bideterminant `bidetP`, `bidetM`: the two halves of the determinant of a couple of square tables, by Laplace's
  recursion along the first row;
* the pair `(l, m)` of a content `l` and a multiplicity `m`, with its top, its sum, its order and the least of the
  pairs over a range (the tropical sum `oplus`);
* the program atom: the least content of a cost over the feasible points, and the dimension of the face of the
  feasible points of least content, read by the affine independence of their differences as balances.

Nothing here is a law. Each word is shown equivalent to its reading over Mathlib by the bridge (`lean/QppBridge`),
and every law that a proof needs comes from Mathlib through that bridge. The words that need a choice (the deficit,
the least of two, the indicator, the extension of a tuple by absent entries) choose by `Classical.propDecidable`.
-/

@[expose] public section

namespace Qpp

open Classical

/-! ## Zero as absent -/

/-- `NN`: a count, or absent. Absent is the zero of the modules. -/
def Count0 : Type := Option Count

/-- `QQ>=0`: a mass, or absent. -/
def Mass0 : Type := Option Mass

namespace Count0

/-- A count as a count or absent. -/
def of (c : Count) : Count0 := some c

instance : Zero Count0 := ⟨(none : Option Count)⟩
instance : One Count0 := ⟨of 1⟩
/-- The numerals `2, 3, ...`. -/
instance (n : Nat) : OfNat Count0 (n + 2) := ⟨of (Count.ofNatSucc (n + 1))⟩

/-- The sum; absent is its unit. -/
protected def add : Count0 → Count0 → Count0
  | none, y => y
  | some a, none => some a
  | some a, some b => some (a + b)

/-- The product; a product with an absent factor is absent. -/
protected def mul : Count0 → Count0 → Count0
  | some a, some b => some (a * b)
  | _, _ => none

instance : Add Count0 := ⟨Count0.add⟩
instance : Mul Count0 := ⟨Count0.mul⟩

/-- `x < y`: `y` is `x` plus a count. -/
protected def Lt (x y : Count0) : Prop := ∃ c : Count, y = x + of c

instance : LT Count0 := ⟨Count0.Lt⟩
instance : LE Count0 := ⟨fun x y => x = y ∨ x < y⟩

end Count0

/-- A count plus a count or absent: a count (absent adds nothing). A multiplicity `j + r_(j)` of a literal pair, with
`r_(j)` a count, is a count whatever `j`. -/
def Count.add0 (c : Count) : Count0 → Count
  | none => c
  | some d => c + d

instance : HAdd Count Count0 Count := ⟨Count.add0⟩
instance : HAdd Count0 Count Count := ⟨fun j c => Count.add0 c j⟩

namespace Mass0

/-- A mass as a mass or absent. -/
def of (a : Mass) : Mass0 := some a

/-- A count or absent as a mass or absent. -/
def ofCount0 : Count0 → Mass0
  | none => none
  | some c => some (Mass.ofCount c)

instance : Zero Mass0 := ⟨(none : Option Mass)⟩
instance : One Mass0 := ⟨of 1⟩
/-- The numerals `2, 3, ...`. -/
instance (n : Nat) : OfNat Mass0 (n + 2) := ⟨of (OfNat.ofNat (n + 2))⟩

/-- The sum; absent is its unit. -/
protected def add : Mass0 → Mass0 → Mass0
  | none, y => y
  | some a, none => some a
  | some a, some b => some (a + b)

/-- The product; a product with an absent factor is absent. -/
protected def mul : Mass0 → Mass0 → Mass0
  | some a, some b => some (a * b)
  | _, _ => none

/-- The quotient; absent divided, or divided by absent, is absent. -/
protected def div : Mass0 → Mass0 → Mass0
  | some a, some b => some (a / b)
  | _, _ => none

instance : Add Mass0 := ⟨Mass0.add⟩
instance : Mul Mass0 := ⟨Mass0.mul⟩
instance : Div Mass0 := ⟨Mass0.div⟩

/-- `x < y`: `y` is `x` plus a mass. -/
protected def Lt (x y : Mass0) : Prop := ∃ z : Mass, y = x + of z

instance : LT Mass0 := ⟨Mass0.Lt⟩
instance : LE Mass0 := ⟨fun x y => x = y ∨ x < y⟩

end Mass0

/-! ## Powers

`x ^ k` for a numeral `k` of Lean is `NatPow` (as in `Base`); `x ^ e` for an exponent `e` in `NN` or `NN>=1` is the
product of `e` factors `x`, and `x ^ 0 = 1`. -/

section Powers

variable {β : Type} [Mul β] [OfNat β 1]

/-- `x ^ c` for a count `c`: `c` factors `x`. -/
def powCount (x : β) : Count → β
  | .one => x
  | .succ c => powCount x c * x

/-- `x ^ e` for a count or absent `e`; `x ^ 0 = 1`. -/
def powCount0 (x : β) : Count0 → β
  | none => 1
  | some c => powCount x c

instance : HPow β Count β := ⟨powCount⟩
instance : HPow β Count0 β := ⟨powCount0⟩

/-- `x ^ k` for a numeral `k` of Lean. -/
def powNat (x : β) : Nat → β
  | 0 => 1
  | k + 1 => powNat x k * x

end Powers

instance : NatPow Count0 := ⟨powNat⟩
instance : NatPow Mass0 := ⟨powNat⟩

/-! ## The deficit, the least and the greatest of two, the indicator -/

/-- The deficit `max(a - b, 0)`: absent when `a ≤ b`, otherwise the count `c` with `a = b + c`. -/
noncomputable def Count0.deficit (a b : Count0) : Count0 :=
  if h : b < a then Count0.of (Classical.choose h) else 0

/-- The deficit `max(a - b, 0)`: absent when `a ≤ b`, otherwise the mass `c` with `a = b + c`. -/
noncomputable def Mass0.deficit (a b : Mass0) : Mass0 :=
  if h : b < a then Mass0.of (Classical.choose h) else 0

/-- `min(a, b)`: the first when it is at most the second, else the second. -/
noncomputable def least {α : Type} [LE α] (a b : α) : α := if a ≤ b then a else b

/-- `max(a, b)`: the second when the first is at most it, else the first. -/
noncomputable def greatest {α : Type} [LE α] (a b : α) : α := if a ≤ b then b else a

noncomputable instance : Min Count := ⟨least⟩
noncomputable instance : Max Count := ⟨greatest⟩
noncomputable instance : Min Mass := ⟨least⟩
noncomputable instance : Max Mass := ⟨greatest⟩
noncomputable instance : Min Count0 := ⟨least⟩
noncomputable instance : Max Count0 := ⟨greatest⟩
noncomputable instance : Min Mass0 := ⟨least⟩
noncomputable instance : Max Mass0 := ⟨greatest⟩

/-- `iverson(P)`: `1` when `P` holds, absent when it does not. -/
noncomputable def iverson (P : Prop) : Mass0 := if P then 1 else 0

/-- `iverson(P)` as a count or absent. -/
noncomputable def iversonN (P : Prop) : Count0 := if P then 1 else 0

/-- The count before a count: absent before `1`. -/
def Count.pred0 : Count → Count0
  | .one => 0
  | .succ c => Count0.of c

/-- `binom(c, k)` for a count `c`, by Pascal's rule. -/
def Count.binom : Count → Count0 → Count0
  | _, none => 1
  | .one, some .one => 1
  | .one, some (.succ _) => 0
  | .succ c, some k => Count.binom c (Count.pred0 k) + Count.binom c (some k)

/-- `binom(n, k)`: the number of choices of `k` among `n`, by Pascal's rule. -/
def Count0.binom : Count0 → Count0 → Count0
  | none, none => 1
  | none, some _ => 0
  | some c, k => Count.binom c k

/-! ## Indices as counts, tuples, sums over the coordinates -/

/-- The indices of a tuple of `n` coordinates: the counts `1, ..., n`; there are none when `n` is absent. A tuple of
`X^n` is a function `Idx n → X`. -/
def Idx (n : Count0) : Type := {i : Count // Count0.of i ≤ n}

/-- Indices compare as counts. -/
instance {n : Count0} : LT (Idx n) := ⟨fun i j => i.1 < j.1⟩
instance {n : Count0} : LE (Idx n) := ⟨fun i j => i.1 ≤ j.1⟩

/-- A function on the indices of `n`, extended to every count by `z` beyond `n`. -/
noncomputable def Idx.extend {β : Type} {n : Count0} (z : β) (f : Idx n → β) (i : Count) : β :=
  if h : Count0.of i ≤ n then f ⟨i, h⟩ else z

/-- `sum i, f i`: the sum over the indices `1, ..., n`; absent when `n` is. -/
noncomputable def Idx.sum {β : Type} [Add β] [Zero β] : (n : Count0) → (Idx n → β) → β
  | none, _ => 0
  | some c, f => sumTo (Idx.extend 0 f) c

/-- `prod i, f i`: the product over the indices `1, ..., n`; `1` when `n` is absent. -/
noncomputable def Idx.prod {β : Type} [Mul β] [OfNat β 1] : (n : Count0) → (Idx n → β) → β
  | none, _ => 1
  | some c, f => prodTo (Idx.extend 1 f) c

/-! ## Two tuples joined, and the two halves of a tuple -/

/-- A value to read where no index reads one (`default`): `1` for a mass, absent for a mass or a count that may be
absent. -/
instance : Inhabited Mass := ⟨1⟩
instance : Inhabited Mass0 := ⟨0⟩
instance : Inhabited Count0 := ⟨0⟩

/-- `join(x, y)`: the tuple of `n + n'` coordinates that reads `x` at an index up to `n`, and `y` at `j` at the index
`n + j`. The index `j` is chosen; `default` is read at no index. -/
noncomputable def Idx.join {β : Type} [Inhabited β] {n n' : Count0} (x : Idx n → β) (y : Idx n' → β)
    (i : Idx (n + n')) : β :=
  if h : Count0.of i.1 ≤ n then x ⟨i.1, h⟩
  else if h' : ∃ j : Idx n', Count0.of i.1 = n + Count0.of j.1 then y (Classical.choose h') else default

/-- The first equation of `join`: at an index up to `n`, the entry of `x`. -/
theorem Idx.join_left {β : Type} [Inhabited β] {n n' : Count0} (x : Idx n → β) (y : Idx n' → β)
    (i : Idx (n + n')) (h : Count0.of i.1 ≤ n) : Idx.join x y i = x ⟨i.1, h⟩ := by
  unfold Idx.join; simp only [h, ↓reduceDIte]

/-- The second equation of `join`: at the index `n + j`, the entry of `y` at `j` (the index chosen). -/
theorem Idx.join_right {β : Type} [Inhabited β] {n n' : Count0} (x : Idx n → β) (y : Idx n' → β)
    (i : Idx (n + n')) (h : ¬ Count0.of i.1 ≤ n) (h' : ∃ j : Idx n', Count0.of i.1 = n + Count0.of j.1) :
    Idx.join x y i = y (Classical.choose h') := by
  unfold Idx.join; simp only [h, h', ↓reduceDIte]

/-- The first half of a tuple of `n + n'` coordinates: its entries at the indices up to `n`. -/
noncomputable def Idx.fst {β : Type} [Inhabited β] {n n' : Count0} (z : Idx (n + n') → β) (i : Idx n) : β :=
  Idx.extend default z i.1

/-- The second half: at `j` up to `n'`, the entry at the index `n + j`. -/
noncomputable def Idx.snd {β : Type} [Inhabited β] {n n' : Count0} (z : Idx (n + n') → β) (j : Idx n') : β :=
  Idx.extend default z (n + j.1)

/-! ## Sums over a range and over a box -/

/-- `Σ_{v = 0}^{b} g v`: the term at absent, then the terms at the counts up to `b`. -/
def upTo {β : Type} [Add β] (b : Count0) (g : Count0 → β) : β :=
  match b with
  | none => g 0
  | some c => g 0 + sumTo (fun i => g (Count0.of i)) c

/-- `Π_{v = 0}^{b} g v`. -/
def upToProd {β : Type} [Mul β] (b : Count0) (g : Count0 → β) : β :=
  match b with
  | none => g 0
  | some c => g 0 * prodTo (fun i => g (Count0.of i)) c

/-- `sum k in a..b, f k`: the sum over `a ≤ k ≤ b`; absent when `b < a`. -/
noncomputable def rangeSum {β : Type} [Add β] [Zero β] (a b : Count0) (f : Count0 → β) : β :=
  upTo b fun k => if a ≤ k then f k else 0

/-- `prod k in a..b, f k`: the product over `a ≤ k ≤ b`; `1` when `b < a`. -/
noncomputable def rangeProd {β : Type} [Mul β] [OfNat β 1] (a b : Count0) (f : Count0 → β) : β :=
  upToProd b fun k => if a ≤ k then f k else 1

/-- The sum over the lattice points of the box `[0, b]` of the first `c` coordinates, the points read as functions
on every count, absent beyond `c`: the last coordinate `v` runs from `0` to `b c`, and the first `c - 1` over their
box. -/
noncomputable def boxTo {β : Type} [Add β] (b : Count → Count0) : Count → ((Count → Count0) → β) → β
  | .one, f => upTo (b 1) fun v => f fun i => if i = 1 then v else 0
  | .succ c, f => upTo (b (.succ c)) fun v => boxTo b c fun u => f fun i => if i = .succ c then v else u i

/-- `sum u <= b, f u`: the sum over the lattice points `u` of `NN^n` with `u ≤ b` at every coordinate. The box of
no coordinates has one point. -/
noncomputable def boxSum {β : Type} [Add β] : (n : Count0) → (Idx n → Count0) → ((Idx n → Count0) → β) → β
  | none, _, f => f fun _ => 0
  | some c, b, f => boxTo (Idx.extend 0 b) c fun u => f fun i => u i.1

/-! ## The bideterminant

The two halves `(|(T, U)|^+, |(T, U)|^-)` of the determinant of a couple of tables `(T, U)` that stands for `T - U`:
the determinant over the semiring of couples (Akian, Gaubert and Guterman, arXiv:0812.3496, Def. 4.14). By Laplace's
recursion along the first row: the couple of no rows is `(1, absent)`, and the couple of `c` rows is the sum over
the columns `j` of `T_(1, j)` times the couple of the minor of `(1, j)` and `U_(1, j)` times that couple exchanged,
the two halves of the minor exchanged again at the even columns. A half is named by a flag: `true` for `+`. -/

/-- `true` at the odd counts `1, 3, 5, ...`. -/
def Count.odd : Count → Bool
  | .one => true
  | .succ c => !(Count.odd c)

/-- The column `b` of the minor of the column `j`: `b` before `j`, `b + 1` from `j` on. -/
def Count.skip : Count → Count → Count
  | .one, b => .succ b
  | .succ _, .one => .one
  | .succ j, .succ b => .succ (Count.skip j b)

/-- The minor of the entry `(1, j)` of a table on every count. -/
def minorAt (T : Count → Count → Mass0) (j : Count) : Count → Count → Mass0 :=
  fun a b => T (.succ a) (Count.skip j b)

/-- The couple of no rows: `1` on the half `+`, absent on the half `-`. -/
def bidet0 (s : Bool) (_ _ : Count → Count → Mass0) : Mass0 := if s then 1 else 0

/-- One step of Laplace's recursion on the first `c` rows, from the halves `B` of the minors. -/
def bidetStep (B : Bool → (Count → Count → Mass0) → (Count → Count → Mass0) → Mass0) (c : Count) (s : Bool)
    (T U : Count → Count → Mass0) : Mass0 :=
  sumTo (fun j => T 1 j * B (s == Count.odd j) (minorAt T j) (minorAt U j)
    + U 1 j * B (s != Count.odd j) (minorAt T j) (minorAt U j)) c

/-- The half `s` of the couple `(T, U)` on its first `c` rows and columns. -/
def bidetCount : Count → Bool → (Count → Count → Mass0) → (Count → Count → Mass0) → Mass0
  | .one => bidetStep bidet0 1
  | .succ c => bidetStep (bidetCount c) (.succ c)

/-- The half `s` of the couple `(T, U)` on its first `n` rows and columns; the couple of no rows when `n` is absent. -/
def bidetExt : Count0 → Bool → (Count → Count → Mass0) → (Count → Count → Mass0) → Mass0
  | none => bidet0
  | some c => bidetCount c

/-- A table of `Forms(n, n)` extended to every count by absent entries. -/
noncomputable def Idx.extend2 {n : Count0} (T : Idx n → Idx n → Mass0) : Count → Count → Mass0 :=
  Idx.extend (fun _ => 0) (fun i => Idx.extend 0 (T i))

/-- `bidetP(T, U)`: the half `|(T, U)|^+` of the couple of tables `(T, U)`. -/
noncomputable def bidetP {n : Count0} (T U : Idx n → Idx n → Mass0) : Mass0 :=
  bidetExt n true (Idx.extend2 T) (Idx.extend2 U)

/-- `bidetM(T, U)`: the half `|(T, U)|^-` of the couple of tables `(T, U)`. -/
noncomputable def bidetM {n : Count0} (T U : Idx n → Idx n → Mass0) : Mass0 :=
  bidetExt n false (Idx.extend2 T) (Idx.extend2 U)

/-! ## The pair `(l, m)` -/

/-- The pair `(l, m)` of a content `l` (a mass or absent) and a multiplicity `m` (a count), or `top`. -/
inductive PairLM where
  | top : PairLM
  | mk : Mass0 → Count → PairLM

namespace PairLM

/-- `m + m' - 1`: the multiplicity of a sum of pairs. -/
def addMult (m : Count) : Count → Count
  | .one => m
  | .succ m' => m + m'

/-- The sum: contents add, multiplicities add less one; `top` absorbs. -/
protected def add : PairLM → PairLM → PairLM
  | mk l m, mk l' m' => mk (l + l') (addMult m m')
  | _, _ => top

instance : Add PairLM := ⟨PairLM.add⟩

/-- The order: a smaller content, or the same content and a larger multiplicity; `top` is the greatest. -/
protected def Le : PairLM → PairLM → Prop
  | _, top => True
  | top, mk _ _ => False
  | mk l m, mk l' m' => l < l' ∨ (l = l' ∧ m' ≤ m)

instance : LE PairLM := ⟨PairLM.Le⟩
instance : LT PairLM := ⟨fun p q => p ≤ q ∧ ¬ q ≤ p⟩

noncomputable instance : Min PairLM := ⟨least⟩

end PairLM

/-- The least of the pairs `g 0, g 1, ..., g c`. -/
noncomputable def infTo0 (g : Count0 → PairLM) : Count → PairLM
  | .one => min (g 0) (g 1)
  | .succ c => min (infTo0 g c) (g (Count0.of (.succ c)))

/-- The least of the pairs `g v` for `0 ≤ v ≤ b`. -/
noncomputable def infUpTo (b : Count0) (g : Count0 → PairLM) : PairLM :=
  match b with
  | none => g 0
  | some c => infTo0 g c

/-- The least of the pairs `g 1, ..., g J`, `J` a count: `oplus k in 1..J, g k`. A range of candidates is never empty,
here and in `infUpTo` (`oplus k in 0..b`): an empty range would have no least member, and `top` is reached only as
the pair of a program that a Farkas line refutes. -/
noncomputable def infFrom1 (g : Count0 → PairLM) : Count → PairLM
  | .one => g 1
  | .succ c => min (infFrom1 g c) (g (Count0.of (.succ c)))

/-! ## The program atom

A program of `k` coordinates: the feasible points `S` (a predicate on the points of `(QQ>=0)^k`) and a cost `c`. Its
pair is `top` when no point is feasible; otherwise `(L, d + 1)` with `L` the least cost over the feasible points and
`d` the dimension of the face `{x ∈ S : c x = L}`: the largest number of its points, after a first, whose differences
from the first are affinely independent. Differences have both signs, so they are read as balances (`Bal`): a
combination of the differences with balance coefficients that ties with zero at every coordinate has coefficients
that tie with zero. -/

/-- `L` is the least cost of a feasible point. -/
def ProgLeast {k : Count0} (S : (Idx k → Mass0) → Prop) (c : (Idx k → Mass0) → Mass0) (L : Mass0) : Prop :=
  (∃ x, S x ∧ c x = L) ∧ ∀ x, S x → L ≤ c x

/-- A mass or absent as a balance: `x + 1` less `1`, and absent is the level pair. -/
def Mass0.toBal : Mass0 → Bal Mass
  | none => Bal.level
  | some a => Bal.of a

/-- The balance `Σ_{j=1}^{d} y_j (p_j - p_0)` at the coordinate `i`, for the points `p_0, ..., p_d`. -/
def faceComb {k : Count0} (d : Count) (p : Count0 → Idx k → Mass0) (y : Count → Bal Mass) (i : Idx k) : Bal Mass :=
  sumTo (fun j => y j * (Mass0.toBal (p (Count0.of j) i) + Bal.swap (Mass0.toBal (p 0 i)))) d

/-- The points `p_0, ..., p_d` lie in `F` and their differences from `p_0` are affinely independent. -/
def AffIndep {k : Count0} (F : (Idx k → Mass0) → Prop) (d : Count0) (p : Count0 → Idx k → Mass0) : Prop :=
  (∀ j, j ≤ d → F (p j)) ∧
    match d with
    | none => True
    | some d => ∀ y : Count → Bal Mass, (∀ i, Bal.Tie (faceComb d p y i) Bal.level) →
        ∀ j, Count0.of j ≤ some d → Bal.Tie (y j) Bal.level

/-- `d` is the dimension of the face `F`: it has `d + 1` affinely independent points, and no `d + 2`. -/
def FaceDim {k : Count0} (F : (Idx k → Mass0) → Prop) (d : Count0) : Prop :=
  (∃ p, AffIndep F d p) ∧ ∀ e : Count0, d < e → ∀ p, ¬ AffIndep F e p

/-- `prog(S : c) = P`: `P` is `top` and no point is feasible, or `P = (L, d + 1)` with `L` the least cost and `d`
the dimension of the face of the feasible points of cost `L`. -/
def IsProg {k : Count0} (S : (Idx k → Mass0) → Prop) (c : (Idx k → Mass0) → Mass0) : PairLM → Prop
  | .top => ∀ x, ¬ S x
  | .mk L m => ProgLeast S c L ∧ ∃ d : Count0, FaceDim (fun x => S x ∧ c x = L) d ∧ Count0.of m = d + 1

end Qpp
