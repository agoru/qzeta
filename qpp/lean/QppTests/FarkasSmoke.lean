module

public import QppKernel

/-!
# Small certificates, replayed by `farkas`
-/

public section

namespace Qpp.Tests

theorem lin_counts (x y z : Count) (h1 : x < y) (h2 : y ≤ z) : x + 1 < z + 1 := by farkas [h1, h2]

/-- Over the counts the slack only knows `x > 0`; `1 ≤ x` is a hypothesis. -/
theorem one_le_counts (x : Count) : 1 ≤ x * x := by farkas [Count.one_le (x * x)]

theorem lin_masses (x y : Mass) (h1 : 2 * x + y < 3) (h2 : x + 3 * y < 4) : 3 * x + 4 * y < 7 := by
  farkas [h1, h2]

theorem lin_coefficients (x y : Mass) (h1 : x + y < 2) (h2 : y = 1) : x / 2 + y < 2 := by
  farkas [(1 / 2) • h1, (1 / 2) • h2]

theorem slack_only (x y : Mass) : x * y < (x + y) * (x + y) := by farkas

/-- `(x - 1)^2 ≥ 0` on `1/2 < x < 2`: split at `1`, then each half is a certificate in the weights of its ends. -/
theorem box_split (x : Mass) (h1 : 1 / 2 < x) (h2 : x < 2) : 2 * x ≤ x ^ 2 + 1 := by
  rcases Mass.split 1 h1 h2 with ⟨h1, h2⟩ | rfl | ⟨h1, h2⟩
  · obtain ⟨c, c', rfl⟩ := Mass.box h1 h2
    farkas
  · farkas
  · obtain ⟨c, c', rfl⟩ := Mass.box h1 h2
    farkas

/-- A finite case split over the counts below `3`. -/
theorem count_cases (x : Count) (h : x < 3) : x * x < 5 := by
  rcases Count.lt_succ_cases h with h | rfl
  · rcases Count.lt_succ_cases h with h | rfl
    · exact absurd h (Count.not_lt_one x)
    · farkas
  · farkas

end Qpp.Tests

end
