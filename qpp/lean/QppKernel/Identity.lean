module

public import QppKernel.Base

/-!
# Identities of count polynomials, checked at one point

An identity between two polynomial expressions in counts `x_0, ..., x_(n-1)` is checked by evaluating both sides
at a few points, on Lean's numerals, which the kernel adds and multiplies in binary. With radices `R_0, ..., R_(n-1)`
let `π_i` be the point `x_k = R_k` for `k < i` and `x_k = 1` for `k ≥ i`. If each side is below `R_i` at `π_i` for
every `i < n`, and the two sides agree at `π_n`, then they agree everywhere (`IsPol.eq_of_points`): at `π_n` a
polynomial is a number written in the radix `R_(n-1)` whose digits are its coefficients in `x_(n-1)` taken at
`π_(n-1)`, and the bound at `π_(n-1)` makes them digits. This is Kronecker's substitution; the bounds are part of
the check, so the radices are free, and the tactic chooses them as small as it can.

`IsPol n` is the class of functions of `n` variables that this argument covers, built by Horner's rule; it
contains every expression (`CExpr.isPol`). Every recursion that the kernel evaluates is structural.
-/

@[expose] public section

namespace Qpp

/-- A Braun tree: entry `0` at the root, the odd entries in the left subtree and the even entries above `0` in the
right one, so that the entry `i` is found in `log i` steps. It holds the values of the variables of a check. -/
inductive Tree (α : Type) where
  | nil
  | node (l : Tree α) (x : α) (r : Tree α)

/-- The entry `i`, or `d` past the end. -/
def Tree.get {α : Type} (d : α) : Tree α → Nat → α
  | .nil, _ => d
  | .node l x r, i =>
    bif Nat.beq i 0 then x else bif Nat.beq (i % 2) 1 then Tree.get d l (i / 2) else Tree.get d r (i / 2 - 1)

/-- A polynomial expression in counts: variables (indices into a list of counts), `1`, numerals, the successor,
sum, product and powers by numerals. -/
inductive CExpr where
  | var (i : Nat)
  | one
  /-- the numeral `n + 1` -/
  | num (n : Nat)
  | succ (a : CExpr)
  | add (a b : CExpr)
  | mul (a b : CExpr)
  | pow (a : CExpr) (k : Nat)

namespace CExpr

/-- The value of an expression, the variable `i` taking the count `ρ i`. -/
def eval (ρ : Nat → Count) : CExpr → Count
  | var i => ρ i
  | one => 1
  | num n => (OfNat.ofNat (n + 1) : Count)
  | succ a => Count.succ (eval ρ a)
  | add a b => eval ρ a + eval ρ b
  | mul a b => eval ρ a * eval ρ b
  | pow a k => eval ρ a ^ k

/-- The value on Lean's numerals. -/
def evalNat (σ : Nat → Nat) : CExpr → Nat
  | var i => σ i
  | one => 1
  | num n => n + 1
  | succ a => evalNat σ a + 1
  | add a b => evalNat σ a + evalNat σ b
  | mul a b => evalNat σ a * evalNat σ b
  | pow a k => evalNat σ a ^ k

/-- Every variable of the expression is below `n`. -/
def varsLt (n : Nat) : CExpr → Bool
  | var i => Nat.blt i n
  | one | num _ => true
  | succ a | pow a _ => varsLt n a
  | add a b | mul a b => varsLt n a && varsLt n b

theorem toNat_eval (ρ : Nat → Count) (e : CExpr) :
    (eval ρ e).toNat = evalNat (fun i => (ρ i).toNat) e := by
  induction e with
  | var i => rfl
  | one => rfl
  | num n => exact Count.toNat_ofNatSucc n
  | succ a ih => exact congrArg (· + 1) ih
  | add a b iha ihb => simp only [eval, evalNat, Count.toNat_add, iha, ihb]
  | mul a b iha ihb => simp only [eval, evalNat, Count.toNat_mul, iha, ihb]
  | pow a k ih => simp only [eval, evalNat, Count.toNat_pow, ih]

end CExpr

/-! ## Polynomial functions by Horner's rule -/

/-- A function of the variables, on Lean's numerals. -/
abbrev Fn := (Nat → Nat) → Nat

/-- `Σ_j cs[j] σ * (σ n)^j`, by Horner's rule. -/
def horner (n : Nat) (σ : Nat → Nat) : List Fn → Nat
  | [] => 0
  | c :: cs => c σ + σ n * horner n σ cs

/-- The polynomial functions of the variables `0, ..., n-1` with coefficients in Lean's numerals: constants for
`n = 0`, and Horner sums in the variable `n` with coefficients in `IsPol n` for `n + 1`. -/
inductive IsPol : Nat → Fn → Prop
  | const (c : Nat) (f : Fn) (h : ∀ σ, f σ = c) : IsPol 0 f
  | horner {n : Nat} (cs : List Fn) (hcs : ∀ c ∈ cs, IsPol n c) (f : Fn) (h : ∀ σ, f σ = horner n σ cs) :
      IsPol (n + 1) f

/-- Sum of coefficient lists, entry by entry. -/
def addL : List Fn → List Fn → List Fn
  | [], ds => ds
  | c :: cs, [] => c :: cs
  | c :: cs, d :: ds => (fun σ => c σ + d σ) :: addL cs ds

/-- Product of coefficient lists (convolution). -/
def mulL : List Fn → List Fn → List Fn
  | [], _ => []
  | c :: cs, ds => addL (ds.map fun d σ => c σ * d σ) ((fun _ => 0) :: mulL cs ds)

theorem horner_addL (n : Nat) (σ : Nat → Nat) (cs ds : List Fn) :
    horner n σ (addL cs ds) = horner n σ cs + horner n σ ds := by
  induction cs generalizing ds with
  | nil => simp [addL, horner]
  | cons c cs ih =>
    cases ds with
    | nil => simp [addL, horner]
    | cons d ds => simp only [addL, horner, ih, Nat.mul_add]; omega

theorem horner_map_mul (n : Nat) (σ : Nat → Nat) (c : Fn) (ds : List Fn) :
    horner n σ (ds.map fun d σ => c σ * d σ) = c σ * horner n σ ds := by
  induction ds with
  | nil => simp [horner]
  | cons d ds ih => simp only [List.map, horner, ih, Nat.mul_add, Nat.mul_left_comm]

theorem horner_mulL (n : Nat) (σ : Nat → Nat) (cs ds : List Fn) :
    horner n σ (mulL cs ds) = horner n σ cs * horner n σ ds := by
  induction cs with
  | nil => simp [mulL, horner]
  | cons c cs ih =>
    simp only [mulL, horner_addL, horner_map_mul, horner, ih, Nat.zero_add, Nat.add_mul, Nat.mul_assoc]

namespace IsPol

theorem congr {n : Nat} {f g : Fn} (hf : IsPol n f) (h : ∀ σ, g σ = f σ) : IsPol n g := by
  cases hf with
  | const c f hc => exact const c g fun σ => (h σ).trans (hc σ)
  | horner cs hcs f hc => exact horner cs hcs g fun σ => (h σ).trans (hc σ)

/-- A polynomial function of the variables below `n` depends on them only. -/
theorem depends {n : Nat} {f : Fn} (hf : IsPol n f) {σ τ : Nat → Nat} (h : ∀ k, k < n → σ k = τ k) :
    f σ = f τ := by
  induction hf with
  | const c f hc => rw [hc, hc]
  | @horner n cs hcs f hc ih =>
    rw [hc, hc]
    have hn : σ n = τ n := h n (Nat.lt_succ_self n)
    have h' : ∀ k, k < n → σ k = τ k := fun k hk => h k (Nat.lt_succ_of_lt hk)
    clear hc
    induction cs with
    | nil => rfl
    | cons c cs ihcs =>
      simp only [Qpp.horner]
      rw [ih c (List.mem_cons_self) h', hn,
        ihcs (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) (fun c hc => ih c (List.mem_cons_of_mem _ hc))]

theorem lift {n : Nat} {f : Fn} (hf : IsPol n f) : IsPol (n + 1) f :=
  horner [f] (fun c hc => by rw [List.mem_singleton.mp hc]; exact hf) f fun σ => by
    show f σ = f σ + σ n * 0; rw [Nat.mul_zero, Nat.add_zero]

theorem zero : ∀ n, IsPol n fun _ => 0
  | 0 => const 0 _ fun _ => rfl
  | _ + 1 => horner [] (fun _ h => nomatch h) _ fun _ => rfl

theorem constant (c : Nat) : ∀ n, IsPol n fun _ => c
  | 0 => const c _ fun _ => rfl
  | n + 1 => (constant c n).lift

theorem var {i n : Nat} (h : i < n) : IsPol n fun σ => σ i := by
  have base : IsPol (i + 1) fun σ => σ i :=
    horner [fun _ => 0, fun _ => 1]
      (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact zero i
        · exact constant 1 i)
      _ fun σ => by simp [_root_.Qpp.horner]
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero i)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact (ih h).lift
    · exact base

/-- Closure under sum and product, by induction on the number of variables. -/
theorem add_mul : ∀ n, (∀ f g, IsPol n f → IsPol n g → IsPol n fun σ => f σ + g σ) ∧
    (∀ f g, IsPol n f → IsPol n g → IsPol n fun σ => f σ * g σ)
  | 0 => by
    refine ⟨fun f g hf hg => ?_, fun f g hf hg => ?_⟩ <;> cases hf with | const c _ hc => ?_ <;>
      cases hg with | const d _ hd => ?_
    · exact const (c + d) _ fun σ => by rw [hc, hd]
    · exact const (c * d) _ fun σ => by rw [hc, hd]
  | n + 1 => by
    obtain ⟨hadd, hmul⟩ := add_mul n
    have haddL : ∀ cs ds : List Fn, (∀ c ∈ cs, IsPol n c) → (∀ d ∈ ds, IsPol n d) →
        ∀ e ∈ addL cs ds, IsPol n e := by
      intro cs
      induction cs with
      | nil => intro ds _ hds; simpa [addL] using hds
      | cons c cs ih =>
        intro ds hcs hds
        cases ds with
        | nil => simpa [addL] using hcs
        | cons d ds =>
          intro e he
          simp only [addL, List.mem_cons] at he
          rcases he with rfl | he
          · exact hadd c d (hcs c List.mem_cons_self) (hds d List.mem_cons_self)
          · exact ih ds (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
              (fun d hd => hds d (List.mem_cons_of_mem _ hd)) e he
    have hmulL : ∀ cs ds : List Fn, (∀ c ∈ cs, IsPol n c) → (∀ d ∈ ds, IsPol n d) →
        ∀ e ∈ mulL cs ds, IsPol n e := by
      intro cs
      induction cs with
      | nil => intro ds _ _ e he; simp [mulL] at he
      | cons c cs ih =>
        intro ds hcs hds
        apply haddL
        · intro e he
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
          exact hmul c d (hcs c List.mem_cons_self) (hds d hd)
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact zero n
          · exact ih ds (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hds e he
    refine ⟨fun f g hf hg => ?_, fun f g hf hg => ?_⟩ <;> cases hf with | horner cs hcs _ hc => ?_ <;>
      cases hg with | horner ds hds _ hd => ?_
    · exact horner (addL cs ds) (haddL cs ds hcs hds) _ fun σ => by rw [hc, hd, horner_addL]
    · exact horner (mulL cs ds) (hmulL cs ds hcs hds) _ fun σ => by rw [hc, hd, horner_mulL]

theorem add {n : Nat} {f g : Fn} (hf : IsPol n f) (hg : IsPol n g) : IsPol n fun σ => f σ + g σ :=
  (add_mul n).1 f g hf hg

theorem mul {n : Nat} {f g : Fn} (hf : IsPol n f) (hg : IsPol n g) : IsPol n fun σ => f σ * g σ :=
  (add_mul n).2 f g hf hg

theorem pow {n : Nat} {f : Fn} (hf : IsPol n f) : ∀ k, IsPol n fun σ => f σ ^ k
  | 0 => constant 1 n
  | k + 1 => (mul (pow hf k) hf).congr fun σ => Nat.pow_succ (n := f σ) (m := k)

end IsPol

theorem CExpr.isPol {n : Nat} : ∀ e : CExpr, e.varsLt n = true → IsPol n fun σ => e.evalNat σ
  | .var i, h => IsPol.var (Nat.le_of_ble_eq_true h)
  | .one, _ => IsPol.constant 1 n
  | .num k, _ => IsPol.constant (k + 1) n
  | .succ a, h => (IsPol.add (CExpr.isPol a h) (IsPol.constant 1 n)).congr fun _ => rfl
  | .add a b, h => by
    simp only [CExpr.varsLt, Bool.and_eq_true] at h
    exact (IsPol.add (CExpr.isPol a h.1) (CExpr.isPol b h.2)).congr fun _ => rfl
  | .mul a b, h => by
    simp only [CExpr.varsLt, Bool.and_eq_true] at h
    exact (IsPol.mul (CExpr.isPol a h.1) (CExpr.isPol b h.2)).congr fun _ => rfl
  | .pow a k, h => (IsPol.pow (CExpr.isPol a h) k).congr fun _ => rfl

/-! ## Digits -/

/-- `Σ_j ds[j] R^j`, the number with digits `ds` in the radix `R`. -/
def digits (R : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + R * digits R ds

theorem digits_eq_zero {R : Nat} (hR : 0 < R) :
    ∀ es : List Nat, digits R es = 0 → ∀ j, es.getD j 0 = 0
  | [], _, _ => rfl
  | e :: es, h, j => by
    simp only [digits] at h
    have h1 : R * digits R es = 0 := by omega
    have h2 := (Nat.mul_eq_zero.mp h1).resolve_left (Nat.pos_iff_ne_zero.mp hR)
    cases j with
    | zero => simp; omega
    | succ j => simpa using digits_eq_zero hR es h2 j

/-- Digits below the radix are determined by the number they write (up to zeros at the end). -/
theorem digits_inj (R : Nat) (ds : List Nat) :
    ∀ es : List Nat, (∀ d ∈ ds, d < R) → (∀ e ∈ es, e < R) → digits R ds = digits R es →
      ∀ j, ds.getD j 0 = es.getD j 0 := by
  induction ds with
  | nil =>
    intro es _ he h j
    cases es with
    | nil => rfl
    | cons e es =>
      have hR : 0 < R := Nat.lt_of_le_of_lt (Nat.zero_le e) (he e List.mem_cons_self)
      exact (digits_eq_zero hR (e :: es) h.symm j).symm
  | cons d ds ih =>
    intro es hd he h j
    have hdR := hd d List.mem_cons_self
    have hR : 0 < R := Nat.lt_of_le_of_lt (Nat.zero_le d) hdR
    cases es with
    | nil => exact digits_eq_zero hR (d :: ds) h j
    | cons e es =>
      have heR := he e List.mem_cons_self
      simp only [digits] at h
      have hmod : d = e := by
        have h1 : (d + R * digits R ds) % R = d := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdR]
        have h2 : (e + R * digits R es) % R = e := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt heR]
        rw [← h1, ← h2, h]
      subst hmod
      have hrest : digits R ds = digits R es := Nat.eq_of_mul_eq_mul_left hR (Nat.add_left_cancel h)
      cases j with
      | zero => rfl
      | succ j =>
        simpa using ih es (fun x h => hd x (List.mem_cons_of_mem _ h))
          (fun x h => he x (List.mem_cons_of_mem _ h)) hrest j

/-! ## The check -/

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by rw [Nat.blt_eq]; exact h

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b with
  | false => rfl
  | true => rw [Nat.blt_eq] at hb; exact absurd hb h

/-- The point `π_i`: `x_k = R_k` for `k < i`, `x_k = 1` for `k ≥ i`. -/
def point (R : Nat → Nat) (i : Nat) (k : Nat) : Nat := bif Nat.blt k i then R k else 1

theorem horner_point_digits (n : Nat) (R : Nat → Nat) (cs : List Fn) (hcs : ∀ c ∈ cs, IsPol n c) :
    horner n (point R (n + 1)) cs = digits (R n) (cs.map fun c => c (point R n)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [horner, List.map, digits]
    rw [ih (fun c h => hcs c (List.mem_cons_of_mem _ h))]
    have hc : c (point R (n + 1)) = c (point R n) := by
      apply (hcs c List.mem_cons_self).depends
      intro k hk
      simp only [point, blt_true hk, blt_true (Nat.lt_succ_of_lt hk), cond]
    have hn : point R (n + 1) n = R n := by simp only [point, blt_true (Nat.lt_succ_self n), cond]
    rw [hc, hn]

/-- At a point where the last variable is `1`, each coefficient is at most the sum. -/
theorem getD_le_horner (n : Nat) (σ : Nat → Nat) (hσ : σ n = 1) :
    ∀ (cs : List Fn) (j : Nat), (cs.getD j fun _ => 0) σ ≤ horner n σ cs
  | [], _ => Nat.zero_le _
  | c :: cs, 0 => by simp [horner]
  | c :: cs, j + 1 => by
    simp only [List.getD_cons_succ, horner, hσ, Nat.one_mul]
    exact Nat.le_add_left_of_le (getD_le_horner n σ hσ cs j)

theorem horner_zero (n : Nat) (σ : Nat → Nat) :
    ∀ ds : List Fn, (∀ j, (ds.getD j fun _ => 0) σ = 0) → horner n σ ds = 0
  | [], _ => rfl
  | d :: ds, h => by
    have h0 := h 0
    simp only [List.getD_cons_zero] at h0
    simp only [horner, h0, horner_zero n σ ds fun j => by simpa using h (j + 1), Nat.mul_zero]

theorem horner_congr (n : Nat) (σ : Nat → Nat) (cs : List Fn) :
    ∀ ds : List Fn, (∀ j, (cs.getD j fun _ => 0) σ = (ds.getD j fun _ => 0) σ) → horner n σ cs = horner n σ ds := by
  induction cs with
  | nil => intro ds h; exact (horner_zero n σ ds fun j => by simpa using (h j).symm).symm
  | cons c cs ih =>
    intro ds h
    cases ds with
    | nil => exact horner_zero n σ (c :: cs) fun j => by simpa using h j
    | cons d ds =>
      have h0 := h 0
      simp only [List.getD_cons_zero] at h0
      simp only [horner, h0, ih ds fun j => by simpa using h (j + 1)]

theorem point_lt (R : Nat → Nat) {i : Nat} {n : Nat} (h : i ≤ n) : point R i n = 1 := by
  simp only [point, blt_false (Nat.not_lt.mpr h), cond]

theorem mem_le_horner (n : Nat) (σ : Nat → Nat) (hσ : σ n = 1) :
    ∀ (cs : List Fn) (c : Fn), c ∈ cs → c σ ≤ horner n σ cs
  | [], _, h => nomatch h
  | d :: cs, c, h => by
    simp only [horner, hσ, Nat.one_mul]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_add_left_of_le (mem_le_horner n σ hσ cs c h)

theorem IsPol.getD {n : Nat} : ∀ (cs : List Fn), (∀ c ∈ cs, IsPol n c) → ∀ j, IsPol n (cs.getD j fun _ => 0)
  | [], _, _ => IsPol.zero n
  | c :: _, h, 0 => h c List.mem_cons_self
  | _ :: cs, h, j + 1 => IsPol.getD cs (fun c hc => h c (List.mem_cons_of_mem _ hc)) j

/-- **Kronecker's substitution.** Two polynomial functions of `n` variables, each below `R_i` at `π_i` for every
`i < n`, that agree at `π_n` agree everywhere. -/
theorem IsPol.eq_of_points {n : Nat} {f g : Fn} (hf : IsPol n f) (hg : IsPol n g) (R : Nat → Nat)
    (hb : ∀ i, i < n → f (point R i) < R i ∧ g (point R i) < R i) (he : f (point R n) = g (point R n)) :
    ∀ σ, f σ = g σ := by
  induction n generalizing f g with
  | zero =>
    cases hf with | const c _ hc => cases hg with | const d _ hd =>
    intro σ; rw [hc, hd]; rw [hc, hd] at he; exact he
  | succ n ih =>
    cases hf with | horner cs hcs _ hc => cases hg with | horner ds hds _ hd =>
    -- the digits: the coefficients at `π_n`, below `R_n` by the bound at `π_n`
    have hdig : ∀ j, ((cs.map fun c => c (point R n)).getD j 0) = ((ds.map fun d => d (point R n)).getD j 0) := by
      have hb' := hb n (Nat.lt_succ_self n)
      rw [hc, hd] at hb'
      apply digits_inj (R n)
      · intro x hx
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hx
        exact Nat.lt_of_le_of_lt (mem_le_horner n _ (point_lt R (Nat.le_refl n)) cs c hc') hb'.1
      · intro x hx
        obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hx
        exact Nat.lt_of_le_of_lt (mem_le_horner n _ (point_lt R (Nat.le_refl n)) ds d hd') hb'.2
      · rw [← horner_point_digits n R cs hcs, ← horner_point_digits n R ds hds, ← hc, ← hd]; exact he
    -- each coefficient agrees everywhere, by the induction
    have hcoef : ∀ j σ, (cs.getD j fun _ => 0) σ = (ds.getD j fun _ => 0) σ := by
      intro j
      apply ih (IsPol.getD cs hcs j) (IsPol.getD ds hds j)
      · intro i hi
        have hp : point R i n = 1 := point_lt R (Nat.le_of_lt hi)
        have h1 := getD_le_horner n (point R i) hp cs j
        have h2 := getD_le_horner n (point R i) hp ds j
        have hb' := hb i (Nat.lt_succ_of_lt hi)
        rw [hc, hd] at hb'
        exact ⟨Nat.lt_of_le_of_lt h1 hb'.1, Nat.lt_of_le_of_lt h2 hb'.2⟩
      · have := hdig j
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
        cases h1 : cs[j]? <;> cases h2 : ds[j]? <;> simp_all
    intro σ
    rw [hc, hd]
    exact horner_congr n σ cs ds fun j => hcoef j σ

namespace CExpr

/-- The bounds of the check: each side below `R_i` at `π_i`, for `i < m`. -/
def bounds (R : Nat → Nat) (a b : CExpr) : Nat → Bool
  | 0 => true
  | i + 1 => bounds R a b i && (Nat.blt (evalNat (point R i) a) (R i) && Nat.blt (evalNat (point R i) b) (R i))

/-- The check, with the radices `Rs`: the variables are below `n = Rs.length`, the bounds hold, and the two sides
agree at `π_n`. -/
def check (Rs : List Nat) (a b : CExpr) : Bool :=
  varsLt Rs.length a && varsLt Rs.length b && bounds (fun k => Rs.getD k 1) a b Rs.length &&
    Nat.beq (evalNat (point (fun k => Rs.getD k 1) Rs.length) a) (evalNat (point (fun k => Rs.getD k 1) Rs.length) b)

theorem bounds_spec (R : Nat → Nat) (a b : CExpr) :
    ∀ m, bounds R a b m = true → ∀ i, i < m → evalNat (point R i) a < R i ∧ evalNat (point R i) b < R i
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | m + 1, h, i, hi => by
    simp only [bounds, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact bounds_spec R a b m h.1 i hi
    · exact ⟨Nat.le_of_ble_eq_true h.2.1, Nat.le_of_ble_eq_true h.2.2⟩

theorem evalNat_eq_of_check (Rs : List Nat) (a b : CExpr) (h : check Rs a b = true) (σ : Nat → Nat) :
    evalNat σ a = evalNat σ b := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ha, hb⟩, hbd⟩, he⟩ := h
  exact IsPol.eq_of_points (isPol a ha) (isPol b hb) _ (bounds_spec _ a b _ hbd)
    (Nat.eq_of_beq_eq_true he) σ

/-- Soundness of the check: the two expressions are equal counts for every value of the variables. -/
theorem eq_of_check (Rs : List Nat) (ρ : Nat → Count) (a b : CExpr) (h : check Rs a b = true) :
    eval ρ a = eval ρ b := by
  apply Count.toNat_inj
  rw [toNat_eval, toNat_eval, evalNat_eq_of_check Rs a b h]

end CExpr

end Qpp
