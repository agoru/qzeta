module

public import QppKernel.Identity

/-!
# Identities of count polynomials, by sparse normal forms

The check at points (`Identity.lean`) works on numbers of `Π (deg_i + 1)` digits, the dense size, exponential in
the number of variables. Here both sides are expanded into normal forms: lists of terms `(key, c)` by increasing
key, the monomial `Π x_i ^ e_i` packed into the one number `key = Σ e_i W ^ i`. With `W` above the total degree of
each side, the exponents are the digits of the key in base `W`, and the product of two monomials is the sum of
their keys, with no carries (`valid_add`). The kernel compares keys and adds and multiplies coefficients in binary;
the cost is the number of terms times the length of a key, linear in the number of variables, with no dense factor.
Coefficients are never zero (every expression is positive), so the normal form is unique. `CExpr.eq_of_scheck` is
the soundness theorem.
-/

@[expose] public section

namespace Qpp

/-- A sparse polynomial: its terms `(key, coefficient)` by increasing key. -/
abbrev SPoly := List (Nat × Nat)

namespace SPoly

/-- Merge the term `t`, followed by terms that `rest` merges into what it is given, into `q`. -/
def mergeAux (t : Nat × Nat) (rest : SPoly → SPoly) : SPoly → SPoly
  | [] => t :: rest []
  | s :: q =>
    bif Nat.blt t.1 s.1 then t :: rest (s :: q)
    else bif Nat.blt s.1 t.1 then s :: mergeAux t rest q
    else (t.1, t.2 + s.2) :: rest q

/-- The sum: merge by key, adding the coefficients of equal keys. -/
def add : SPoly → SPoly → SPoly
  | [], q => q
  | t :: p, q => mergeAux t (add p) q

/-- A term times a polynomial: the keys add, the coefficients multiply. -/
def mulTerm (t : Nat × Nat) (q : SPoly) : SPoly := q.map fun s => (t.1 + s.1, t.2 * s.2)

/-- Sums of adjacent pairs: `[a + b, c + d, ...]`. -/
def pairs : List SPoly → List SPoly
  | a :: b :: l => add a b :: pairs l
  | l => l

/-- The sum of a list, from the right. -/
def sumSeq : List SPoly → SPoly
  | [] => []
  | a :: l => add a (sumSeq l)

/-- The sum of a list by rounds of `pairs`, at most `k` rounds, so that each term is merged `log` times. -/
def sumAllF : Nat → List SPoly → SPoly
  | 0, l => sumSeq l
  | k + 1, l => match l with
    | [] => []
    | [a] => a
    | a :: b :: l => sumAllF k (pairs (a :: b :: l))

/-- The sum of a list, balanced. -/
def sumAll (l : List SPoly) : SPoly := sumAllF 64 l

/-- The product: the sum, balanced, of the products of the terms of `p` with `q`. -/
def mul (p q : SPoly) : SPoly := sumAll (p.map fun t => mulTerm t q)

/-- Powers by a natural number. -/
def pow (p : SPoly) : Nat → SPoly
  | 0 => [(0, 1)]
  | k + 1 => mul p (pow p k)

/-- Equality of term lists, on Lean's numerals. -/
def beq : SPoly → SPoly → Bool
  | [], [] => true
  | s :: p, t :: q => Nat.beq s.1 t.1 && Nat.beq s.2 t.2 && beq p q
  | _, _ => false

theorem eq_of_beq : ∀ p q : SPoly, beq p q = true → p = q
  | [], [], _ => rfl
  | s :: p, t :: q, h => by
    simp only [beq, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [eq_of_beq p q h3, show s = t from Prod.ext (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-! ## Keys -/

variable (W : Nat) (σ : Nat → Nat)

/-- The monomial of a key: `Π σ_(j+i) ^ (digit i of k)` for `i < n`. -/
def monK : Nat → Nat → Nat → Nat
  | _, 0, _ => 1
  | j, n + 1, k => σ j ^ (k % W) * monK (j + 1) n (k / W)

/-- The sum of the first `n` digits of a key, its total degree. -/
def dsum : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, k => k % W + dsum n (k / W)

/-- A key of `n` digits and total degree at most `d`. -/
def Valid (n d k : Nat) : Prop := k < W ^ n ∧ dsum W n k ≤ d

/-- The value of a sparse polynomial in `n` variables. -/
def denote (n : Nat) : SPoly → Nat
  | [] => 0
  | t :: p => t.2 * monK W σ 0 n t.1 + denote n p

/-- Every key is valid. -/
def AllValid (n d : Nat) (p : SPoly) : Prop := ∀ t ∈ p, Valid W n d t.1

theorem monK_zero : ∀ j n, monK W σ j n 0 = 1
  | _, 0 => rfl
  | j, n + 1 => by simp only [monK, Nat.zero_mod, Nat.zero_div, Nat.pow_zero, monK_zero (j + 1) n, Nat.mul_one]

theorem dsum_zero : ∀ n, dsum W n 0 = 0
  | 0 => rfl
  | n + 1 => by simp only [dsum, Nat.zero_mod, Nat.zero_div, dsum_zero n]

theorem valid_zero (hW : 0 < W) (n d : Nat) : Valid W n d 0 :=
  ⟨Nat.pow_pos_iff.mpr (Or.inl hW), by rw [dsum_zero]; exact Nat.zero_le d⟩

theorem valid_mono {n d d' k : Nat} (h : Valid W n d k) (hd : d ≤ d') : Valid W n d' k :=
  ⟨h.1, Nat.le_trans h.2 hd⟩

theorem allValid_mono {n d d' : Nat} {p : SPoly} (h : AllValid W n d p) (hd : d ≤ d') : AllValid W n d' p :=
  fun t ht => valid_mono W (h t ht) hd

/-- The key of the variable `x_(j+i)`. -/
theorem valid_var (hW : 1 < W) : ∀ n j i, i < n → monK W σ j n (W ^ i) = σ (j + i) ∧ dsum W n (W ^ i) = 1
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, 0, _ => by
    refine ⟨?_, ?_⟩ <;> simp only [Nat.pow_zero, monK, dsum, Nat.mod_eq_of_lt hW, Nat.div_eq_of_lt hW, monK_zero,
      dsum_zero, Nat.pow_one, Nat.mul_one, Nat.add_zero]
  | n + 1, j, i + 1, h => by
    have hW0 : 0 < W := Nat.lt_trans Nat.zero_lt_one hW
    have ih := valid_var hW n (j + 1) i (Nat.lt_of_succ_lt_succ h)
    refine ⟨?_, ?_⟩ <;> simp only [monK, dsum, Nat.pow_succ, Nat.mul_mod_left, Nat.mul_div_cancel _ hW0,
      Nat.pow_zero, Nat.one_mul, Nat.zero_add, ih.1, ih.2]
    rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- **No carries.** Two keys whose degrees sum below `W` add digit by digit, and their monomials multiply. -/
theorem valid_add : ∀ n {k₁ k₂ d₁ d₂ : Nat}, Valid W n d₁ k₁ → Valid W n d₂ k₂ → d₁ + d₂ < W →
    Valid W n (d₁ + d₂) (k₁ + k₂) ∧ ∀ j, monK W σ j n (k₁ + k₂) = monK W σ j n k₁ * monK W σ j n k₂
  | 0, k₁, k₂, _, _, h₁, h₂, _ => by
    have e₁ : k₁ = 0 := Nat.lt_one_iff.mp h₁.1
    have e₂ : k₂ = 0 := Nat.lt_one_iff.mp h₂.1
    subst e₁ e₂
    exact ⟨⟨Nat.zero_lt_one, Nat.zero_le _⟩, fun _ => rfl⟩
  | n + 1, k₁, k₂, d₁, d₂, ⟨hk₁, hd₁⟩, ⟨hk₂, hd₂⟩, hW => by
    have hW0 : 0 < W := Nat.lt_of_le_of_lt (Nat.zero_le _) hW
    simp only [dsum] at hd₁ hd₂
    have hq₁ : k₁ / W < W ^ n := Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ, Nat.mul_comm] at hk₁; exact hk₁)
    have hq₂ : k₂ / W < W ^ n := Nat.div_lt_of_lt_mul (by rw [Nat.pow_succ, Nat.mul_comm] at hk₂; exact hk₂)
    have ih := valid_add n (d₁ := dsum W n (k₁ / W)) (d₂ := dsum W n (k₂ / W)) ⟨hq₁, Nat.le_refl _⟩
      ⟨hq₂, Nat.le_refl _⟩ (by omega)
    have ha : k₁ % W + k₂ % W < W := by omega
    have e : k₁ + k₂ = (k₁ % W + k₂ % W) + W * (k₁ / W + k₂ / W) := by
      have := Nat.mod_add_div k₁ W
      have := Nat.mod_add_div k₂ W
      rw [Nat.mul_add]; omega
    have emod : (k₁ + k₂) % W = k₁ % W + k₂ % W := by
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have ediv : (k₁ + k₂) / W = k₁ / W + k₂ / W := by
      rw [e, Nat.add_mul_div_left _ _ hW0, Nat.div_eq_of_lt ha, Nat.zero_add]
    refine ⟨⟨?_, ?_⟩, fun j => ?_⟩
    · have hle : W * (k₁ / W + k₂ / W + 1) ≤ W * W ^ n := Nat.mul_le_mul_left W ih.1.1
      rw [Nat.pow_succ, Nat.mul_comm (W ^ n), e]
      rw [Nat.mul_add, Nat.mul_one] at hle
      omega
    · simp only [dsum, emod, ediv]
      have := ih.1.2
      omega
    · simp only [monK, emod, ediv, ih.2 (j + 1), Nat.pow_add]
      exact Nat.mul_mul_mul_comm _ _ _ _

/-! ## Soundness of the operations -/

theorem denote_mergeAux (n : Nat) (t : Nat × Nat) (rest : SPoly → SPoly) (P : Nat)
    (hrest : ∀ r, denote W σ n (rest r) = P + denote W σ n r) :
    ∀ q, denote W σ n (mergeAux t rest q) = t.2 * monK W σ 0 n t.1 + P + denote W σ n q
  | [] => by simp only [mergeAux, denote, hrest]; omega
  | s :: q => by
    cases h₁ : Nat.blt t.1 s.1 with
    | true => simp only [mergeAux, h₁, Bool.cond_true, denote, hrest]; omega
    | false =>
      cases h₂ : Nat.blt s.1 t.1 with
      | true => simp only [mergeAux, h₁, h₂, Bool.cond_true, Bool.cond_false, denote, denote_mergeAux n t rest P hrest q]; omega
      | false =>
        have e : t.1 = s.1 := by
          have := blt_false_iff.mp h₁
          have := blt_false_iff.mp h₂
          omega
        simp only [mergeAux, h₁, h₂, Bool.cond_false, denote, hrest, Nat.add_mul]
        rw [e]
        omega
where
  blt_false_iff {a b : Nat} : Nat.blt a b = false ↔ ¬ a < b := by
    constructor
    · intro h h'; rw [blt_true h'] at h; cases h
    · exact blt_false

theorem denote_add (n : Nat) : ∀ p q, denote W σ n (add p q) = denote W σ n p + denote W σ n q
  | [], q => (Nat.zero_add _).symm
  | t :: p, q => by
    simp only [add]
    rw [denote_mergeAux W σ n t (add p) (denote W σ n p) (fun r => denote_add n p r) q]
    rfl

theorem allValid_mergeAux {n d : Nat} (t : Nat × Nat) (rest : SPoly → SPoly) (ht : Valid W n d t.1)
    (hrest : ∀ r, AllValid W n d r → AllValid W n d (rest r)) :
    ∀ q, AllValid W n d q → AllValid W n d (mergeAux t rest q)
  | [], _ => by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ht
    · exact hrest [] (fun _ h => nomatch h) u hu
  | s :: q, hq => by
    have hs : Valid W n d s.1 := hq s List.mem_cons_self
    have hq' : AllValid W n d q := fun u hu => hq u (List.mem_cons_of_mem _ hu)
    intro u hu
    cases h₁ : Nat.blt t.1 s.1 with
    | true =>
      simp only [mergeAux, h₁, Bool.cond_true] at hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ht
      · exact hrest _ hq u hu
    | false =>
      cases h₂ : Nat.blt s.1 t.1 with
      | true =>
        simp only [mergeAux, h₁, h₂, Bool.cond_true, Bool.cond_false] at hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hs
        · exact allValid_mergeAux t rest ht hrest q hq' u hu
      | false =>
        simp only [mergeAux, h₁, h₂, Bool.cond_false] at hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact ht
        · exact hrest _ hq' u hu

theorem allValid_add {n d : Nat} : ∀ p q, AllValid W n d p → AllValid W n d q → AllValid W n d (add p q)
  | [], _, _, hq => hq
  | t :: p, q, hp, hq =>
    allValid_mergeAux W t (add p) (hp t List.mem_cons_self)
      (fun r hr => allValid_add p r (fun u hu => hp u (List.mem_cons_of_mem _ hu)) hr) q hq

theorem mulTerm_spec {n d₁ d₂ : Nat} (t : Nat × Nat) (ht : Valid W n d₁ t.1) (hW : d₁ + d₂ < W) :
    ∀ q, AllValid W n d₂ q →
      AllValid W n (d₁ + d₂) (mulTerm t q) ∧ denote W σ n (mulTerm t q) = t.2 * monK W σ 0 n t.1 * denote W σ n q
  | [], _ => ⟨(fun _ h => nomatch h), (Nat.mul_zero _).symm⟩
  | s :: q, hq => by
    have hs : Valid W n d₂ s.1 := hq s List.mem_cons_self
    have ih := mulTerm_spec t ht hW q fun u hu => hq u (List.mem_cons_of_mem _ hu)
    have hk := valid_add W σ n ht hs hW
    refine ⟨fun u hu => ?_, ?_⟩
    · simp only [mulTerm, List.map_cons] at hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hk.1
      · exact ih.1 u hu
    · show (t.2 * s.2) * monK W σ 0 n (t.1 + s.1) + denote W σ n (mulTerm t q) = _
      rw [ih.2, hk.2 0, denote, Nat.mul_add, Nat.mul_mul_mul_comm]

/-- The values of a list of sparse polynomials, added. -/
def denoteL (n : Nat) : List SPoly → Nat
  | [] => 0
  | p :: l => denote W σ n p + denoteL n l

/-- Every key of every entry is valid. -/
def AllValidL (n d : Nat) (l : List SPoly) : Prop := ∀ p ∈ l, AllValid W n d p

theorem pairs_spec {n d : Nat} : ∀ l : List SPoly, AllValidL W n d l →
    AllValidL W n d (pairs l) ∧ denoteL W σ n (pairs l) = denoteL W σ n l
  | [], h => ⟨h, rfl⟩
  | [a], h => ⟨h, rfl⟩
  | a :: b :: l, h => by
    have ih := pairs_spec l fun p hp => h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact allValid_add W _ _ (h a List.mem_cons_self) (h b (List.mem_cons_of_mem _ List.mem_cons_self))
      · exact ih.1 p hp
    · simp only [pairs, denoteL, denote_add, ih.2]; omega

theorem sumSeq_spec {n d : Nat} : ∀ l : List SPoly, AllValidL W n d l →
    AllValid W n d (sumSeq l) ∧ denote W σ n (sumSeq l) = denoteL W σ n l
  | [], _ => ⟨(fun _ h => nomatch h), rfl⟩
  | a :: l, h => by
    have ih := sumSeq_spec l fun p hp => h p (List.mem_cons_of_mem _ hp)
    exact ⟨allValid_add W _ _ (h a List.mem_cons_self) ih.1, by simp only [sumSeq, denoteL, denote_add, ih.2]⟩

theorem sumAllF_spec {n d : Nat} : ∀ (k : Nat) (l : List SPoly), AllValidL W n d l →
    AllValid W n d (sumAllF k l) ∧ denote W σ n (sumAllF k l) = denoteL W σ n l
  | 0, l, h => sumSeq_spec W σ l h
  | _ + 1, [], _ => ⟨(fun _ h => nomatch h), rfl⟩
  | _ + 1, [a], h => ⟨h a List.mem_cons_self, by simp only [sumAllF, denoteL, Nat.add_zero]⟩
  | k + 1, a :: b :: l, h => by
    have hp := pairs_spec W σ (a :: b :: l) h
    have ih := sumAllF_spec k _ hp.1
    exact ⟨ih.1, by rw [sumAllF, ih.2, hp.2]⟩

theorem sumAll_spec {n d : Nat} (l : List SPoly) (h : AllValidL W n d l) :
    AllValid W n d (sumAll l) ∧ denote W σ n (sumAll l) = denoteL W σ n l :=
  sumAllF_spec W σ 64 l h

theorem mul_spec {n d₁ d₂ : Nat} (hW : d₁ + d₂ < W) (p q : SPoly) (hp : AllValid W n d₁ p)
    (hq : AllValid W n d₂ q) :
    AllValid W n (d₁ + d₂) (mul p q) ∧ denote W σ n (mul p q) = denote W σ n p * denote W σ n q := by
  have h : ∀ p : SPoly, AllValid W n d₁ p → AllValidL W n (d₁ + d₂) (p.map fun t => mulTerm t q) ∧
      denoteL W σ n (p.map fun t => mulTerm t q) = denote W σ n p * denote W σ n q := by
    intro p
    induction p with
    | nil => exact fun _ => ⟨(fun _ h => nomatch h), (Nat.zero_mul _).symm⟩
    | cons t p ih =>
      intro hp
      have ht := mulTerm_spec W σ t (hp t List.mem_cons_self) hW q hq
      have ih := ih fun u hu => hp u (List.mem_cons_of_mem _ hu)
      refine ⟨fun r hr => ?_, ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact ht.1
        · exact ih.1 r hr
      · simp only [List.map_cons, denoteL, ht.2, ih.2, denote, Nat.add_mul]
  have hl := h p hp
  have hs := sumAll_spec W σ _ hl.1
  exact ⟨hs.1, by rw [mul, hs.2, hl.2]⟩

theorem pow_spec {n d : Nat} (p : SPoly) (hp : AllValid W n d p) :
    ∀ k, k * d < W → AllValid W n (k * d) (pow p k) ∧ denote W σ n (pow p k) = denote W σ n p ^ k
  | 0, hW => by
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [List.mem_singleton.mp hu]; exact valid_zero W (by omega) n _
    · simp only [pow, denote, monK_zero, Nat.mul_one, Nat.add_zero, Nat.pow_zero]
  | k + 1, hW => by
    rw [Nat.succ_mul] at hW ⊢
    have ih := pow_spec p hp k (by omega)
    have hm := mul_spec W σ (n := n) (d₁ := d) (d₂ := k * d) (by omega) p (pow p k) hp ih.1
    refine ⟨allValid_mono W hm.1 (by omega), ?_⟩
    rw [pow, hm.2, ih.2, Nat.pow_succ, Nat.mul_comm]

end SPoly

namespace CExpr

open SPoly

/-- The total degree, a bound for the degree of every monomial. -/
def deg : CExpr → Nat
  | var _ => 1
  | one => 0
  | num _ => 0
  | succ a => deg a
  | add a b => max (deg a) (deg b)
  | mul a b => deg a + deg b
  | pow a k => k * deg a

/-- The summands of the normal form, with keys in base `W`, before `acc`: a sum gives the summands of its two
sides, so that a long sum is merged in a balanced way (`SPoly.sumAll`). -/
def nfs (W : Nat) : CExpr → List SPoly → List SPoly
  | var i, acc => [(W ^ i, 1)] :: acc
  | one, acc => [(0, 1)] :: acc
  | num n, acc => [(0, n + 1)] :: acc
  | succ a, acc => nfs W a ([(0, 1)] :: acc)
  | add a b, acc => nfs W a (nfs W b acc)
  | mul a b, acc => SPoly.mul (SPoly.sumAll (nfs W a [])) (SPoly.sumAll (nfs W b [])) :: acc
  | pow a k, acc => SPoly.pow (SPoly.sumAll (nfs W a [])) k :: acc

/-- The sparse normal form, with keys in base `W`. -/
def nf (W : Nat) (e : CExpr) : SPoly := SPoly.sumAll (nfs W e [])

theorem nfs_spec (W n : Nat) (σ : Nat → Nat) : ∀ (e : CExpr) (acc : List SPoly) (d : Nat), varsLt n e = true →
    deg e ≤ d → d < W → AllValidL W n d acc →
    AllValidL W n d (nfs W e acc) ∧ denoteL W σ n (nfs W e acc) = evalNat σ e + denoteL W σ n acc
  | var i, acc, d, hv, hd, hW, hacc => by
    have hi : i < n := Nat.le_of_ble_eq_true hv
    have hW1 : 1 < W := Nat.lt_of_le_of_lt hd hW
    have hv := valid_var W σ hW1 n 0 i hi
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · intro u hu
        rw [List.mem_singleton.mp hu]
        exact ⟨Nat.pow_lt_pow_right hW1 hi, Nat.le_trans (Nat.le_of_eq hv.2) hd⟩
      · exact hacc p hp
    · simp only [nfs, denoteL, denote, hv.1, Nat.zero_add, Nat.one_mul, Nat.add_zero, evalNat]
  | one, acc, d, _, _, hW, hacc => by
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · intro u hu; rw [List.mem_singleton.mp hu]; exact valid_zero W (by omega) n _
      · exact hacc p hp
    · simp only [nfs, denoteL, denote, monK_zero, Nat.one_mul, Nat.add_zero, evalNat]
  | num m, acc, d, _, _, hW, hacc => by
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · intro u hu; rw [List.mem_singleton.mp hu]; exact valid_zero W (by omega) n _
      · exact hacc p hp
    · simp only [nfs, denoteL, denote, monK_zero, Nat.mul_one, Nat.add_zero, evalNat]
  | succ a, acc, d, hv, hd, hW, hacc => by
    have h1 : AllValidL W n d ([(0, 1)] :: acc) := fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · intro u hu; rw [List.mem_singleton.mp hu]; exact valid_zero W (by omega) n _
      · exact hacc p hp
    have ih := nfs_spec W n σ a _ d hv hd hW h1
    refine ⟨ih.1, ?_⟩
    simp only [nfs, ih.2, denoteL, denote, monK_zero, Nat.one_mul, Nat.add_zero, evalNat]
    omega
  | add a b, acc, d, hv, hd, hW, hacc => by
    simp only [varsLt, Bool.and_eq_true] at hv
    have hd' : deg a ≤ d ∧ deg b ≤ d := Nat.max_le.mp hd
    have ihb := nfs_spec W n σ b acc d hv.2 hd'.2 hW hacc
    have iha := nfs_spec W n σ a _ d hv.1 hd'.1 hW ihb.1
    refine ⟨iha.1, ?_⟩
    simp only [nfs, iha.2, ihb.2, evalNat]
    omega
  | mul a b, acc, d, hv, hd, hW, hacc => by
    simp only [varsLt, Bool.and_eq_true] at hv
    simp only [deg] at hd
    have nil : ∀ d', AllValidL W n d' [] := fun _ _ h => nomatch h
    have iha := nfs_spec W n σ a [] (deg a) hv.1 (Nat.le_refl _) (by omega) (nil _)
    have ihb := nfs_spec W n σ b [] (deg b) hv.2 (Nat.le_refl _) (by omega) (nil _)
    have sa := sumAll_spec W σ _ iha.1
    have sb := sumAll_spec W σ _ ihb.1
    have hm := mul_spec W σ (by omega) _ _ sa.1 sb.1
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact allValid_mono W hm.1 hd
      · exact hacc p hp
    · simp only [nfs, denoteL, hm.2, sa.2, sb.2, iha.2, ihb.2, Nat.add_zero, evalNat]
  | pow a k, acc, d, hv, hd, hW, hacc => by
    cases k with
    | zero =>
      refine ⟨fun p hp => ?_, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · intro u hu
          simp only [SPoly.pow] at hu
          rw [List.mem_singleton.mp hu]; exact valid_zero W (by omega) n _
        · exact hacc p hp
      · simp only [nfs, SPoly.pow, denoteL, denote, monK_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero, evalNat]
    | succ k =>
      simp only [deg] at hd
      have hda : deg a ≤ (k + 1) * deg a := by rw [Nat.succ_mul]; omega
      have iha := nfs_spec W n σ a [] (deg a) hv (Nat.le_refl _) (by omega) (fun _ h => nomatch h)
      have sa := sumAll_spec W σ _ iha.1
      have hp := pow_spec W σ _ sa.1 (k + 1) (by omega)
      refine ⟨fun p hp' => ?_, ?_⟩
      · rcases List.mem_cons.mp hp' with rfl | hp'
        · exact allValid_mono W hp.1 hd
        · exact hacc p hp'
      · simp only [nfs, denoteL, hp.2, sa.2, iha.2, Nat.add_zero, evalNat]

theorem nf_spec (W n : Nat) (σ : Nat → Nat) (e : CExpr) (hv : varsLt n e = true) (hW : deg e < W) :
    AllValid W n (deg e) (nf W e) ∧ evalNat σ e = denote W σ n (nf W e) := by
  have h := nfs_spec W n σ e [] (deg e) hv (Nat.le_refl _) hW (fun _ h => nomatch h)
  have hs := sumAll_spec W σ _ h.1
  exact ⟨hs.1, by rw [nf, hs.2, h.2]; rfl⟩

/-- The sparse check, keys in base `W`: the variables are below `n`, the degrees below `W`, and the normal forms
agree. -/
def scheck (W n : Nat) (a b : CExpr) : Bool :=
  varsLt n a && varsLt n b && Nat.blt (deg a) W && Nat.blt (deg b) W && SPoly.beq (nf W a) (nf W b)

theorem evalNat_eq_of_scheck (W n : Nat) (a b : CExpr) (h : scheck W n a b = true) (σ : Nat → Nat) :
    evalNat σ a = evalNat σ b := by
  simp only [scheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ha, hb⟩, hda⟩, hdb⟩, he⟩ := h
  rw [(nf_spec W n σ a ha (Nat.le_of_ble_eq_true hda)).2, (nf_spec W n σ b hb (Nat.le_of_ble_eq_true hdb)).2,
    SPoly.eq_of_beq _ _ he]

/-- Soundness of the sparse check: the two expressions are equal counts for every value of the variables. -/
theorem eq_of_scheck (W n : Nat) (ρ : Nat → Count) (a b : CExpr) (h : scheck W n a b = true) :
    eval ρ a = eval ρ b := by
  apply Count.toNat_inj
  rw [toNat_eval, toNat_eval, evalNat_eq_of_scheck W n a b h]

end CExpr

/-- How an identity of counts is checked: at points with the radices `Rs` (`CExpr.check`), or by normal forms with
keys in base `W` in `n` variables (`CExpr.scheck`). -/
inductive CheckBy where
  | points (Rs : List Nat)
  | normal (W n : Nat)

namespace CExpr

/-- The check by the method `m`. -/
def verify : CheckBy → CExpr → CExpr → Bool
  | .points Rs, a, b => check Rs a b
  | .normal W n, a, b => scheck W n a b

theorem eq_of_verify (m : CheckBy) (ρ : Nat → Count) (a b : CExpr) (h : verify m a b = true) :
    eval ρ a = eval ρ b := by
  cases m with
  | points Rs => exact eq_of_check Rs ρ a b h
  | normal W n => exact eq_of_scheck W n ρ a b h

end CExpr

end Qpp
