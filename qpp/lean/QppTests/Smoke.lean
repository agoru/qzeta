module

public import QppKernel

/-!
# Small identities of counts, checked by `qeq`
-/

public section

namespace Qpp.Tests

theorem square (x y : Count) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by qeq

theorem cube (x y : Count) : (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by qeq

theorem succ_square (x : Count) : Count.succ x * Count.succ x = x * x + 2 * x + 1 := by qeq

/-- An atom that is not a sum, product or power is a variable of its own. -/
theorem atoms (x : Count) (f : Count → Count) : (f x + 1) * (f x + 1) = f x * f x + 2 * f x + 1 := by qeq

end Qpp.Tests

end
