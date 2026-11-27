module

public import QppKernel.BalTactic
public meta import QppKernel.FarkasTactic

/-!
# Pins: the Krawczyk test over the rationals

A pin is a rational box, a rational centre `c` and a map `N` (in use `N u = u - A f(u)`, `A` a rational matrix)
that passes the test of Krawczyk and Moore: on the box, `N u - N v = M(u, v) (u - v)` with every row of `|M|`
summing to at most `q`, and `|N c - c| + q R ≤ R`. Then the iterates `y_L` of `N` from `c` stay in the box, move by
at most `q^L a`, and `|u - N u|` is comparable with `|u - y_L|` up to `q^L`: the locus is read through the rational
iterates, and no real point is named. The test and the contraction argument are classical (Krawczyk 1969,
doi:10.1007/BF02234767; Moore 1977, doi:10.1137/0714040; Neumaier 1990, doi:10.1017/CBO9780511526473, Ch. 5);
here they are derived on pairs of masses.

Distances are read by their bounds: `Near r u v d` says `|u_j - v_j| ≤ d` for every coordinate `j ≤ r`.
-/

@[expose] public section

namespace Qpp

namespace Pin

open Bal

/-- `|u_j - v_j| ≤ d` at every coordinate `j ≤ r`, as two inequalities of pairs. -/
def Near (r : Count) (u v : Count → Bal Mass) (d : Bal Mass) : Prop :=
  ∀ j, j ≤ r → u j ≤ v j + d ∧ v j ≤ u j + d

/-- The iterates of `N` from `y`. -/
def iter (N : (Count → Bal Mass) → Count → Bal Mass) (y : Count → Bal Mass) : Nat → Count → Bal Mass
  | 0 => y
  | L + 1 => N (iter N y L)

theorem iter_zero (N : (Count → Bal Mass) → Count → Bal Mass) (y : Count → Bal Mass) : iter N y 0 = y := rfl
theorem iter_succ (N : (Count → Bal Mass) → Count → Bal Mass) (y : Count → Bal Mass) (L : Nat) :
    iter N y (L + 1) = N (iter N y L) := rfl

theorem near_symm {r : Count} {u v : Count → Bal Mass} {d : Bal Mass} (h : Near r u v d) : Near r v u d :=
  fun j hj => ⟨(h j hj).2, (h j hj).1⟩

theorem near_refl (r : Count) (u : Count → Bal Mass) (d : Bal Mass) (hd : level ≤ d) : Near r u u d := by
  intro j _
  constructor <;> pfarkas [hd]

theorem near_mono {r : Count} {u v : Count → Bal Mass} {d d' : Bal Mass} (h : Near r u v d) (hd : d ≤ d') :
    Near r u v d' := by
  intro j hj
  have h1 := (h j hj).1
  have h2 := (h j hj).2
  exact ⟨by pfarkas [h1, hd], by pfarkas [h2, hd]⟩

theorem near_trans {r : Count} {u v w : Count → Bal Mass} {d e : Bal Mass} (h : Near r u v d) (h' : Near r v w e) :
    Near r u w (d + e) := by
  intro j hj
  have h1 := (h j hj).1
  have h2 := (h j hj).2
  have h3 := (h' j hj).1
  have h4 := (h' j hj).2
  exact ⟨by pfarkas [h1, h3], by pfarkas [h2, h4]⟩

/-- A distance bound is nonnegative. -/
theorem near_nonneg {r : Count} {u v : Count → Bal Mass} {d : Bal Mass} (h : Near r u v d) : level ≤ d := by
  have h1 := (h 1 (Count.one_le r)).1
  have h2 := (h 1 (Count.one_le r)).2
  pfarkas [(1 / 2 : Mass) • h1, (1 / 2 : Mass) • h2]

theorem of_le_of {x y : Mass} (h : x ≤ y) : of x ≤ of y := by
  rcases h with h | h
  · subst h; exact Or.inl rfl
  · exact Or.inr (Mass.bal_of_lt.mpr h)

/-! ## The test of Krawczyk: a contraction from the bounds of the divided differences -/

/-- `|M w| ≤ m d` from `|M| ≤ m` and `|w| ≤ d`: the products of the four bounds. -/
theorem abs_mul_le {M m w d : Bal Mass} (hM1 : M ≤ m) (hM2 : swap M ≤ m) (hw1 : w ≤ d) (hw2 : swap w ≤ d) :
    M * w ≤ m * d ∧ swap (M * w) ≤ m * d := by
  have p1 := mul_nonneg (sub_nonneg hM1) (sub_nonneg hw1)
  have p2 := mul_nonneg (sub_nonneg hM2) (sub_nonneg hw2)
  have p3 := mul_nonneg (sub_nonneg hM1) (sub_nonneg hw2)
  have p4 := mul_nonneg (sub_nonneg hM2) (sub_nonneg hw1)
  constructor
  · pfarkas [(1 / 2 : Mass) • p3, (1 / 2 : Mass) • p4]
  · pfarkas [(1 / 2 : Mass) • p1, (1 / 2 : Mass) • p2]

theorem sumTo_mul_right (f : Count → Bal Mass) (d : Bal Mass) (n : Count) :
    (sumTo f n * d).Tie (sumTo (fun j => f j * d) n) := by
  induction n using Count.ind with
  | h1 => exact rfl
  | hs n ih =>
    show ((sumTo f n + f (.succ n)) * d).Tie (sumTo (fun j => f j * d) n + f (.succ n) * d)
    peq [ih]

theorem sumTo_swap (f : Count → Bal Mass) (n : Count) :
    (sumTo (fun j => swap (f j)) n).Tie (swap (sumTo f n)) := by
  induction n using Count.ind with
  | h1 => exact rfl
  | hs n ih =>
    show (sumTo (fun j => swap (f j)) n + swap (f (.succ n))).Tie (swap (sumTo f n + f (.succ n)))
    peq [ih]

/-- The contraction of the test: on `X`, `N u - N v = M(u, v) (u - v)` row by row, `|M_ij| ≤ m_ij`, and every row of
`m` sums to at most `q`; then `N` moves points `d` apart to points `q d` apart. -/
theorem contract {r : Count} {X : (Count → Bal Mass) → Prop} {N : (Count → Bal Mass) → Count → Bal Mass}
    {M : (Count → Bal Mass) → (Count → Bal Mass) → Count → Count → Bal Mass} {m : Count → Count → Bal Mass}
    {q : Mass}
    (hM : ∀ u v i, X u → X v → i ≤ r →
      (N u i).Tie (N v i + sumTo (fun j => M u v i j * (u j + swap (v j))) r))
    (hb : ∀ u v i j, X u → X v → i ≤ r → j ≤ r → M u v i j ≤ m i j ∧ swap (M u v i j) ≤ m i j)
    (hq : ∀ i, i ≤ r → sumTo (m i) r ≤ of q) :
    ∀ u v d, X u → X v → Near r u v d → Near r (N u) (N v) (of q * d) := by
  intro u v d hu hv h i hi
  have hd := near_nonneg h
  have hterm : ∀ j, j ≤ r → M u v i j * (u j + swap (v j)) ≤ m i j * d ∧
      swap (M u v i j * (u j + swap (v j))) ≤ m i j * d := by
    intro j hj
    have hb1 := (hb u v i j hu hv hi hj).1
    have hb2 := (hb u v i j hu hv hi hj).2
    have hw1 := (h j hj).1
    have hw2 := (h j hj).2
    exact abs_mul_le hb1 hb2 (by pfarkas [hw1]) (by pfarkas [hw2])
  have s1 := sumTo_le_upto (f := fun j => M u v i j * (u j + swap (v j))) (g := fun j => m i j * d) r
    (fun j hj => (hterm j hj).1)
  have s2 := sumTo_le_upto (f := fun j => swap (M u v i j * (u j + swap (v j)))) (g := fun j => m i j * d) r
    (fun j hj => (hterm j hj).2)
  have neg := sumTo_swap (fun j => M u v i j * (u j + swap (v j))) r
  have ht := sumTo_mul_right (m i) d r
  have hq' := mul_nonneg (sub_nonneg (hq i hi)) hd
  have hMi := hM u v i hu hv hi
  have hMs := hMi.symm
  have hts := ht.symm
  have negs := neg.symm
  exact ⟨by pfarkas [hMi, s1, hts, hq'], by pfarkas [hMs, s2, negs, hts, hq']⟩

/-- The box of the test is kept: `|N c - c| ≤ a` and `a + q R ≤ R`. -/
theorem box_inv {r : Count} {N : (Count → Bal Mass) → Count → Bal Mass} {c : Count → Bal Mass} {q a R : Mass}
    (hc : ∀ u v d, Near r u c (of R) → Near r v c (of R) → Near r u v d → Near r (N u) (N v) (of q * d))
    (ha : Near r c (N c) (of a)) (haR : a + q * R ≤ R) :
    ∀ u, Near r u c (of R) → Near r (N u) c (of R) := by
  intro u hu
  have hcc : Near r c c (of R) := near_refl r c _ (Or.inr (of_pos R))
  have h2 := near_trans (hc u c (of R) hu hcc hu) (near_symm ha)
  have h3 := of_le_of haR
  exact near_mono h2 (by pfarkas [h3])

/-! ## The iterates -/

/-- The iterates stay in `X` and the `L`-th step is at most `q^L a`. -/
theorem iter_near {r : Count} {X : (Count → Bal Mass) → Prop} {N : (Count → Bal Mass) → Count → Bal Mass}
    {q a : Mass} {y : Count → Bal Mass}
    (hc : ∀ u v d, X u → X v → Near r u v d → Near r (N u) (N v) (of q * d))
    (hX : ∀ u, X u → X (N u)) (hy : X y) (h1 : Near r y (N y) (of a)) :
    ∀ L : Nat, X (iter N y L) ∧ Near r (iter N y L) (iter N y (L + 1)) (of (q ^ L * a)) := by
  intro L
  induction L with
  | zero =>
    have e : q ^ 0 * a = a := by qeq
    exact ⟨hy, by rw [e]; exact h1⟩
  | succ L ih =>
    refine ⟨hX _ ih.1, ?_⟩
    have h := hc _ _ _ ih.1 (hX _ ih.1) ih.2
    have e : q ^ (L + 1) * a = q * (q ^ L * a) := by rw [show q ^ (L + 1) = q ^ L * q from rfl]; qeq
    rw [e]
    exact near_mono h (by pfarkas)

/-- The distance to the iterates, from below: `|u - y_L| ≤ (e + q^L a) / p + q^L D` when `|u - N u| ≤ e`,
`q + p = 1` and `D` bounds the distances in `X`. -/
theorem near_iter {r : Count} {X : (Count → Bal Mass) → Prop} {N : (Count → Bal Mass) → Count → Bal Mass}
    {q p a D e : Mass} {y u : Count → Bal Mass}
    (hc : ∀ u v d, X u → X v → Near r u v d → Near r (N u) (N v) (of q * d))
    (hX : ∀ u, X u → X (N u)) (hy : X y) (h1 : Near r y (N y) (of a)) (hp : q + p = 1)
    (hD : ∀ v w, X v → X w → Near r v w (of D)) (hu : X u) (he : Near r u (N u) (of e)) (L : Nat) :
    Near r u (iter N y L) (of ((e + q ^ L * a) / p + q ^ L * D)) := by
  have hit := iter_near hc hX hy h1 L
  have i1 : e + q * ((e + q ^ L * a) / p) + q ^ L * a = (q + p) * ((e + q ^ L * a) / p) := by qeq
  rw [hp] at i1
  have i2 : (1 : Mass) * ((e + q ^ L * a) / p) = (e + q ^ L * a) / p := by qeq
  rw [i2] at i1
  have hT : (of (e + q * ((e + q ^ L * a) / p) + q ^ L * a)).Tie (of ((e + q ^ L * a) / p)) := by
    rw [i1]; exact rfl
  have key : ∀ k : Nat, Near r u (iter N y L) (of ((e + q ^ L * a) / p + q ^ k * D)) := by
    intro k
    induction k with
    | zero =>
      have e0 : q ^ 0 * D = D := by qeq
      rw [e0]
      exact near_mono (hD u _ hu hit.1) (by pfarkas)
    | succ k ih =>
      have h3 := near_trans (near_trans he (hc _ _ _ hu hit.1 ih)) (near_symm hit.2)
      rw [show q ^ (k + 1) = q ^ k * q from rfl]
      exact near_mono h3 (by pfarkas [hT])
  exact key L

/-- The distance to the iterates, from above: `|u - N u| ≤ (1 + q) |u - y_L| + q^L a`. -/
theorem near_step {r : Count} {X : (Count → Bal Mass) → Prop} {N : (Count → Bal Mass) → Count → Bal Mass}
    {q a : Mass} {y u : Count → Bal Mass} {d : Bal Mass}
    (hc : ∀ u v d, X u → X v → Near r u v d → Near r (N u) (N v) (of q * d))
    (hX : ∀ u, X u → X (N u)) (hy : X y) (h1 : Near r y (N y) (of a)) (hu : X u) (L : Nat)
    (h : Near r u (iter N y L) d) :
    Near r u (N u) (d + of (q ^ L * a) + of q * d) := by
  have hit := iter_near hc hX hy h1 L
  exact near_trans (near_trans h hit.2) (near_symm (hc _ _ _ hu hit.1 h))

/-! ## The pin -/

/-! ## Completeness: the test at an approximate zero, with explicit constants -/

/-- A sum of `n` equal pairs. -/
theorem sumTo_const (c : Mass) (n : Count) : (sumTo (fun _ => of c) n).Tie (of (Mass.ofCount n * c)) := by
  induction n using Count.ind with
  | h1 => show (of c).Tie (of (Mass.ofCount 1 * c)); rw [show Mass.ofCount 1 = 1 from rfl]; peq
  | hs n ih =>
    show (sumTo (fun _ => of c) n + of c).Tie (of (Mass.ofCount (.succ n) * c))
    rw [Mass.ofCount_succ n]
    peq [ih]

/-- A row of a product: `|sum_k A_k E_k| ≤ r K e` from `|A_k| ≤ K` and `|E_k| ≤ e` for `k ≤ r`. -/
theorem row_le {r : Count} {A E : Count → Bal Mass} {K e : Mass}
    (hA : ∀ k, k ≤ r → A k ≤ of K ∧ swap (A k) ≤ of K)
    (hE : ∀ k, k ≤ r → E k ≤ of e ∧ swap (E k) ≤ of e) :
    sumTo (fun k => A k * E k) r ≤ of (Mass.ofCount r * (K * e)) ∧
      swap (sumTo (fun k => A k * E k) r) ≤ of (Mass.ofCount r * (K * e)) := by
  have ht : (of K * of e).Tie (of (K * e)) := by peq
  have hk : ∀ k, k ≤ r → A k * E k ≤ of (K * e) ∧ swap (A k * E k) ≤ of (K * e) := by
    intro k hk
    have h := abs_mul_le (hA k hk).1 (hA k hk).2 (hE k hk).1 (hE k hk).2
    have h1 := h.1
    have h2 := h.2
    exact ⟨by pfarkas [h1, ht], by pfarkas [h2, ht]⟩
  have s1 := sumTo_le_upto (f := fun k => A k * E k) (g := fun _ => of (K * e)) r (fun k hk' => (hk k hk').1)
  have s2 := sumTo_le_upto (f := fun k => swap (A k * E k)) (g := fun _ => of (K * e)) r (fun k hk' => (hk k hk').2)
  have hc := sumTo_const (K * e) r
  have neg := sumTo_swap (fun k => A k * E k) r
  have negs := neg.symm
  exact ⟨by pfarkas [s1, hc], by pfarkas [negs, s2, hc]⟩

/-- **The test from entry bounds.** With `M(u, v) = A E(u, v)` row by row (in use `E = J - D(u, v)`, `J` the
Jacobian at the centre and `A J = I`), `|A_ik| ≤ K`, `|E_kj| ≤ e` on the box and `r r K e ≤ q`, the bounds
`m_ij := r K e` pass the row test of `pin`. -/
theorem rows_of_bounds {r : Count} {X : (Count → Bal Mass) → Prop}
    {M : (Count → Bal Mass) → (Count → Bal Mass) → Count → Count → Bal Mass}
    {A : Count → Count → Bal Mass} {E : (Count → Bal Mass) → (Count → Bal Mass) → Count → Count → Bal Mass}
    {K e q : Mass}
    (hME : ∀ u v i j, X u → X v → i ≤ r → j ≤ r → (M u v i j).Tie (sumTo (fun k => A i k * E u v k j) r))
    (hA : ∀ i k, i ≤ r → k ≤ r → A i k ≤ of K ∧ swap (A i k) ≤ of K)
    (hE : ∀ u v k j, X u → X v → k ≤ r → j ≤ r → E u v k j ≤ of e ∧ swap (E u v k j) ≤ of e)
    (hq : Mass.ofCount r * (Mass.ofCount r * (K * e)) ≤ q) :
    (∀ u v i j, X u → X v → i ≤ r → j ≤ r →
      M u v i j ≤ of (Mass.ofCount r * (K * e)) ∧ swap (M u v i j) ≤ of (Mass.ofCount r * (K * e))) ∧
    (∀ i, i ≤ r → sumTo (fun _ => of (Mass.ofCount r * (K * e))) r ≤ of q) := by
  refine ⟨fun u v i j hu hv hi hj => ?_, fun i _ => ?_⟩
  · have h := row_le (r := r) (A := fun k => A i k) (E := fun k => E u v k j) (fun k hk => hA i k hi hk)
      (fun k hk => hE u v k j hu hv hk hj)
    have h1 := h.1
    have h2 := h.2
    have hm := hME u v i j hu hv hi hj
    have hms := hm.symm
    exact ⟨by pfarkas [hm, h1], by pfarkas [hms, h2]⟩
  · have hc := sumTo_const (Mass.ofCount r * (K * e)) r
    have hq' := of_le_of hq
    pfarkas [hc, hq']

/-- **The constants of completeness.** With `ρ := 1 / (2 r r W K B)` (in use `K ≥ |A_ik|`, the cofactor bound
`(r-1)! B_1^(r-1) / c_0`, `B = B_2` a bound of the second divided differences and `W = 2r + s`) the entries
`e := W B ρ` of `J - D` on the `ρ`-box give rows of `|I - A D|` at most `1/2`; and a value `|f| ≤ ε` at the centre
with `r K ε ≤ ρ / 4`, together with a change `V` over the free coordinates with `r K V ≤ ρ / 4`, gives
`a := ρ / 2`, so that `a + q ρ = ρ` for `q = 1/2`. -/
theorem constants (r : Count) (W K B : Mass) :
    Mass.ofCount r * (Mass.ofCount r * (K * (W * B * (1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B))))) =
      1 / 2 ∧
    ∀ ε V : Mass, Mass.ofCount r * K * ε ≤ 1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B) / 4 →
      Mass.ofCount r * K * V ≤ 1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B) / 4 →
      of (Mass.ofCount r * (K * (ε + V))) ≤ of (1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B) / 2) ∧
      1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B) / 2 +
        1 / 2 * (1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B)) =
        1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B) := by
  refine ⟨by qeq, fun ε V h1 h2 => ⟨?_, by qeq⟩⟩
  have e1 : Mass.ofCount r * (K * (ε + V)) = Mass.ofCount r * K * ε + Mass.ofCount r * K * V := by qeq
  have e2 : 1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B) / 2 =
      1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B) / 4 +
        1 / (2 * Mass.ofCount r * Mass.ofCount r * W * K * B) / 4 := by qeq
  rw [e1, e2]
  have g1 := of_le_of h1
  have g2 := of_le_of h2
  pfarkas [g1, g2]

/-! ## The chart of a pin -/

/-- A count at most `n + 1` is at most `n` or is `n + 1`. -/
theorem le_succ_cases {j n : Count} (h : j ≤ Count.succ n) : j ≤ n ∨ j = Count.succ n := by
  rcases h with h | ⟨c, hc⟩
  · exact Or.inr h
  · left
    cases c with
    | one => exact Or.inl (Count.succ_inj hc).symm
    | succ c => exact Or.inr ⟨c, Count.succ_inj hc⟩

/-- The distance `max_{j ≤ r} |u_j - v_j|` is attained at a coordinate. -/
theorem near_attained (u v : Count → Bal Mass) (r : Count) :
    ∃ d j, j ≤ r ∧ Near r u v d ∧ (d.Tie (u j + swap (v j)) ∨ d.Tie (v j + swap (u j))) := by
  induction r using Count.ind with
  | h1 =>
    obtain ⟨m, hm⟩ := exists_isMax (u 1 + swap (v 1)) (v 1 + swap (u 1))
    have g1 := IsMax.ge_left hm
    have g2 := IsMax.ge_right hm
    refine ⟨m, 1, Or.inl rfl, fun j hj => ?_, ?_⟩
    · rcases hj with rfl | hj
      · exact ⟨by pfarkas [g1], by pfarkas [g2]⟩
      · exact absurd hj (Count.not_lt_of_le (Count.one_le j))
    · rcases IsMax.cases hm with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
  | hs n ih =>
    obtain ⟨d, j, hj, hn, hd⟩ := ih
    obtain ⟨a, ha⟩ := exists_isMax (u (.succ n) + swap (v (.succ n))) (v (.succ n) + swap (u (.succ n)))
    obtain ⟨m, hm⟩ := exists_isMax d a
    have a1 := IsMax.ge_left ha
    have a2 := IsMax.ge_right ha
    have m1 := IsMax.ge_left hm
    have m2 := IsMax.ge_right hm
    have hnear : Near (.succ n) u v m := by
      intro i hi
      rcases le_succ_cases hi with hi | rfl
      · have h1 := (hn i hi).1
        have h2 := (hn i hi).2
        exact ⟨by pfarkas [h1, m1], by pfarkas [h2, m1]⟩
      · exact ⟨by pfarkas [a1, m2], by pfarkas [a2, m2]⟩
    rcases IsMax.cases hm with ⟨h, _⟩ | ⟨h, _⟩
    · exact ⟨m, j, le_succ_of_le hj, hnear, by
        rcases hd with hd | hd
        · exact Or.inl (by peq [h, hd])
        · exact Or.inr (by peq [h, hd])⟩
    · refine ⟨m, .succ n, Or.inl rfl, hnear, ?_⟩
      rcases IsMax.cases ha with ⟨h', _⟩ | ⟨h', _⟩
      · exact Or.inl (by peq [h, h'])
      · exact Or.inr (by peq [h, h'])

/-- **The chart of a pin.** Where `N` contracts by `q` (`q + p = 1`), the map `u ↦ u - N u` (in use
`A f(u)`) changes distances by a factor between `p` and `1 + q`: `|(u - N u) - (v - N v)| ≤ e` gives
`|u - v| ≤ e / p`, and `|u - v| ≤ d` gives `|(u - N u) - (v - N v)| ≤ d + q d`. -/
theorem chart {r : Count} {X : (Count → Bal Mass) → Prop} {N : (Count → Bal Mass) → Count → Bal Mass} {q p : Mass}
    (hc : ∀ u v d, X u → X v → Near r u v d → Near r (N u) (N v) (of q * d)) (hp : q + p = 1) :
    (∀ u v e, X u → X v →
      Near r (fun j => u j + swap (N u j)) (fun j => v j + swap (N v j)) (of e) → Near r u v (of (e / p))) ∧
    (∀ u v d, X u → X v → Near r u v d →
      Near r (fun j => u j + swap (N u j)) (fun j => v j + swap (N v j)) (d + of q * d)) := by
  refine ⟨fun u v e hu hv he => ?_, fun u v d hu hv h j hj => ?_⟩
  · obtain ⟨d, j0, hj0, hn, hd⟩ := near_attained u v r
    have hNj := hc u v d hu hv hn j0 hj0
    have n1 := hNj.1
    have n2 := hNj.2
    have w1 := (he j0 hj0).1
    have w2 := (he j0 hj0).2
    have hdle : d ≤ of e + of q * d := by
      rcases hd with h | h
      · pfarkas [h, w1, n1]
      · pfarkas [h, w2, n2]
    have hqp : (of q * d + of p * d).Tie (of (q + p) * d) := by peq
    rw [hp] at hqp
    have i : p * (e / p) = e := by qeq
    have t : (of p * of (e / p)).Tie (of (p * (e / p))) := by peq
    rw [i] at t
    have hpos : level ≤ of p * (of (e / p) + swap d) := by pfarkas [t, hdle, hqp]
    have hle := nonneg_of_mul_nonneg (of_pos p) hpos
    exact near_mono hn (by pfarkas [hle])
  · have hN := hc u v d hu hv h j hj
    have n1 := hN.1
    have n2 := hN.2
    have h1 := (h j hj).1
    have h2 := (h j hj).2
    exact ⟨by pfarkas [h1, n2], by pfarkas [h2, n1]⟩

/-- **The pin.** On the box `|u - c| ≤ R`, let `N u - N v = M(u, v) (u - v)` row by row, `|M_ij| ≤ m_ij`, every row
of `m` sum to at most `q`, `q + p = 1`, `|N c - c| ≤ a` and `a + q R ≤ R` (the test of Krawczyk). Then the iterates
`y_L` of `N` from `c` stay in the box and move by at most `q^L a`, and for `u` in the box with `|u - N u| ≤ e`,
`|u - y_L| ≤ (e + q^L a) / p + 2 q^L R` and `|u - N u| ≤ (1 + q) |u - y_L| + q^L a`. -/
theorem pin {r : Count} {N : (Count → Bal Mass) → Count → Bal Mass} {c : Count → Bal Mass}
    {M : (Count → Bal Mass) → (Count → Bal Mass) → Count → Count → Bal Mass} {m : Count → Count → Bal Mass}
    {q p a R : Mass}
    (hM : ∀ u v i, Near r u c (of R) → Near r v c (of R) → i ≤ r →
      (N u i).Tie (N v i + sumTo (fun j => M u v i j * (u j + swap (v j))) r))
    (hb : ∀ u v i j, Near r u c (of R) → Near r v c (of R) → i ≤ r → j ≤ r →
      M u v i j ≤ m i j ∧ swap (M u v i j) ≤ m i j)
    (hq : ∀ i, i ≤ r → sumTo (m i) r ≤ of q) (hp : q + p = 1)
    (ha : Near r c (N c) (of a)) (haR : a + q * R ≤ R) :
    (∀ L : Nat, Near r (iter N c L) c (of R) ∧ Near r (iter N c L) (iter N c (L + 1)) (of (q ^ L * a))) ∧
    (∀ u e, Near r u c (of R) → Near r u (N u) (of e) → ∀ L : Nat,
      Near r u (iter N c L) (of ((e + q ^ L * a) / p + q ^ L * (R + R)))) ∧
    (∀ u d, Near r u c (of R) → ∀ L : Nat, Near r u (iter N c L) d →
      Near r u (N u) (d + of (q ^ L * a) + of q * d)) := by
  have hc := contract (X := fun u => Near r u c (of R)) hM hb hq
  have hX := box_inv hc ha haR
  have hy : Near r c c (of R) := near_refl r c _ (Or.inr (of_pos R))
  have hD : ∀ v w, Near r v c (of R) → Near r w c (of R) → Near r v w (of (R + R)) := by
    intro v w hv hw
    exact near_mono (near_trans hv (near_symm hw)) (by pfarkas)
  refine ⟨iter_near hc hX hy ha, ?_, ?_⟩
  · intro u e hu he L
    exact near_iter hc hX hy ha hp hD hu he L
  · intro u d hu L h
    exact near_step hc hX hy ha hu L h

end Pin

end Qpp
