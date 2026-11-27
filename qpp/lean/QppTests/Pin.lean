module

public import QppKernel

/-! The pin of `y^2 = 2` on the box `|y - 3/2| ≤ 1/10`, with `N y = y - (y^2 - 2) / 3`: the test of Krawczyk passes
with `q = 1/15`, and the rational iterates from `3/2` satisfy `|y_L^2 - 2| ≤ 3 (1/15)^L / 12`. -/

namespace Qpp.PinSmoke

open Bal Pin

/-- `N y = y - (y^2 - 2) / 3`, coordinate by coordinate. -/
def N (u : Count → Bal Mass) (i : Count) : Bal Mass := u i + swap (of (1 / 3) * (u i * u i + swap (of 2)))

/-- The divided difference of `N`: `N u - N v = (1 - (u + v) / 3) (u - v)`. -/
def M (u v : Count → Bal Mass) (i _j : Count) : Bal Mass := of 1 + swap (of (1 / 3) * (u i + v i))

def c (_i : Count) : Bal Mass := of (3 / 2)

theorem le_one {i : Count} (h : i ≤ 1) : i = 1 := by
  rcases h with h | h
  · exact h
  · exact absurd h (Count.not_lt_of_le (Count.one_le i))

theorem sqrt_two :
    (∀ L : Nat, Near 1 (iter N c L) c (of (1 / 10)) ∧
      Near 1 (iter N c L) (iter N c (L + 1)) (of ((1 / 15) ^ L * (1 / 12)))) ∧
    (∀ u e, Near 1 u c (of (1 / 10)) → Near 1 u (N u) (of e) → ∀ L : Nat,
      Near 1 u (iter N c L) (of ((e + (1 / 15) ^ L * (1 / 12)) / (14 / 15) + (1 / 15) ^ L * (1 / 10 + 1 / 10)))) ∧
    (∀ u d, Near 1 u c (of (1 / 10)) → ∀ L : Nat, Near 1 u (iter N c L) d →
      Near 1 u (N u) (d + of ((1 / 15) ^ L * (1 / 12)) + of (1 / 15) * d)) := by
  refine pin (M := M) (m := fun _ _ => of (1 / 15)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro u v i _ _ hi
    obtain rfl := le_one hi
    show (N u 1).Tie (N v 1 + M u v 1 1 * (u 1 + swap (v 1)))
    unfold N M
    peq
  · intro u v i j hu hv hi _
    obtain rfl := le_one hi
    have hu1 := (hu 1 (Or.inl rfl)).1
    have hu2 := (hu 1 (Or.inl rfl)).2
    have hv1 := (hv 1 (Or.inl rfl)).1
    have hv2 := (hv 1 (Or.inl rfl)).2
    unfold M c at *
    exact ⟨by pfarkas [(1 / 3 : Mass) • hu2, (1 / 3 : Mass) • hv2],
      by pfarkas [(1 / 3 : Mass) • hu1, (1 / 3 : Mass) • hv1]⟩
  · intro i _
    exact Or.inl rfl
  · qeq
  · intro j hj
    obtain rfl := le_one hj
    unfold N c
    exact ⟨by pfarkas, by pfarkas⟩
  · exact Or.inr ⟨1 / 100, by qeq⟩

/-- The rational iterates pin `y^2 = 2`: `|y_L^2 - 2| ≤ 3 (1/15)^L / 12`. -/
theorem sqrt_two_level (L : Nat) :
    (iter N c L 1 * iter N c L 1 + swap (of 2)) ≤ of (3 * ((1 / 15) ^ L * (1 / 12))) ∧
    swap (iter N c L 1 * iter N c L 1 + swap (of 2)) ≤ of (3 * ((1 / 15) ^ L * (1 / 12))) := by
  have h := (sqrt_two.1 L).2 1 (Or.inl rfl)
  have h1 := h.1
  have h2 := h.2
  rw [iter_succ] at h1 h2
  unfold N at h1 h2
  exact ⟨by pfarkas [(3 : Mass) • h1], by pfarkas [(3 : Mass) • h2]⟩

/-- Completeness at `3/2`: `K = 1/3` (the inverse of `f' = 3`), `B_2 = 1`, `W = 2r + s = 2` give the a
priori radius `ρ = 1 / (2 r r W K B_2) = 3/4`. -/
theorem sqrt_two_rho : 1 / (2 * Mass.ofCount 1 * Mass.ofCount 1 * 2 * (1 / 3) * 1) = (3 / 4 : Mass) := by
  rw [show Mass.ofCount 1 = 1 from rfl]; qeq

/-- `N u - N v = M(u, v) (u - v)` on the box of radius `3/4`. -/
theorem step_tie : ∀ u v i, Near 1 u c (of (3 / 4)) → Near 1 v c (of (3 / 4)) → i ≤ 1 →
    (N u i).Tie (N v i + sumTo (fun j => M u v i j * (u j + swap (v j))) 1) := by
  intro u v i _ _ hi
  obtain rfl := le_one hi
  show (N u 1).Tie (N v 1 + M u v 1 1 * (u 1 + swap (v 1)))
  unfold N M
  peq

/-- With `ρ = 3/4` the test passes from the entry bounds alone: `|A| = 1/3`, `|J - D(u, v)| = |3 - u - v| ≤ W B_2 ρ
= 3/2` on the box, so the rows are at most `1/2`; `|N c - c| = 1/12 ≤ ρ/2`. The iterates stay in the box and move
by at most `(1/2)^L (3/8)`. -/
theorem sqrt_two_complete (L : Nat) :
    Near 1 (iter N c L) c (of (3 / 4)) ∧ Near 1 (iter N c L) (iter N c (L + 1)) (of ((1 / 2) ^ L * (3 / 8))) := by
  have hrows := rows_of_bounds (r := 1) (X := fun u => Near 1 u c (of (3 / 4))) (M := M)
    (A := fun _ _ => of (1 / 3)) (E := fun u v _ _ => of 3 + swap (u 1 + v 1)) (K := 1 / 3) (e := 3 / 2)
    (q := 1 / 2) ?_ ?_ ?_ ?_
  · have hp : (1 / 2 : Mass) + 1 / 2 = 1 := by qeq
    have haR : (3 / 8 : Mass) + 1 / 2 * (3 / 4) ≤ 3 / 4 := Or.inl (by qeq)
    have ha : Near 1 c (N c) (of (3 / 8)) := by
      intro j hj
      obtain rfl := le_one hj
      unfold N c
      exact ⟨by pfarkas, by pfarkas⟩
    exact (pin (M := M) (q := 1 / 2) (p := 1 / 2) (a := 3 / 8) (R := 3 / 4) step_tie hrows.1 hrows.2 hp ha haR).1 L
  · intro u v i j _ _ hi hj
    obtain rfl := le_one hi
    obtain rfl := le_one hj
    show (M u v 1 1).Tie (of (1 / 3) * (of 3 + swap (u 1 + v 1)))
    unfold M
    peq
  · intro i k _ _
    exact ⟨Or.inl rfl, by pfarkas⟩
  · intro u v k j hu hv _ _
    have hu1 := (hu 1 (Or.inl rfl)).1
    have hu2 := (hu 1 (Or.inl rfl)).2
    have hv1 := (hv 1 (Or.inl rfl)).1
    have hv2 := (hv 1 (Or.inl rfl)).2
    unfold c at *
    exact ⟨by pfarkas [hu2, hv2], by pfarkas [hu1, hv1]⟩
  · rw [show Mass.ofCount 1 = 1 from rfl]; exact Or.inl (by qeq)

/-- The chart of the pin: on the box `|y - 3/2| ≤ 1/10`, `|A f(u) - A f(v)| ≤ e` gives
`|u - v| ≤ 15 e / 14`. -/
theorem sqrt_two_chart (u v : Count → Bal Mass) (e : Mass) (hu : Near 1 u c (of (1 / 10)))
    (hv : Near 1 v c (of (1 / 10)))
    (h : Near 1 (fun j => u j + swap (N u j)) (fun j => v j + swap (N v j)) (of e)) :
    Near 1 u v (of (e / (14 / 15))) := by
  have hc := contract (r := 1) (X := fun u => Near 1 u c (of (1 / 10))) (N := N) (M := M) (m := fun _ _ => of (1 / 15))
    (q := 1 / 15) ?_ ?_ ?_
  · exact (chart hc (p := 14 / 15) (by qeq)).1 u v e hu hv h
  · intro u v i _ _ hi
    obtain rfl := le_one hi
    show (N u 1).Tie (N v 1 + M u v 1 1 * (u 1 + swap (v 1)))
    unfold N M
    peq
  · intro u v i j hu hv hi _
    obtain rfl := le_one hi
    have hu1 := (hu 1 (Or.inl rfl)).1
    have hu2 := (hu 1 (Or.inl rfl)).2
    have hv1 := (hv 1 (Or.inl rfl)).1
    have hv2 := (hv 1 (Or.inl rfl)).2
    unfold M c at *
    exact ⟨by pfarkas [(1 / 3 : Mass) • hu2, (1 / 3 : Mass) • hv2],
      by pfarkas [(1 / 3 : Mass) • hu1, (1 / 3 : Mass) • hv1]⟩
  · intro i _
    exact Or.inl rfl

end Qpp.PinSmoke
