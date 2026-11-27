module

public import QppKernel

/-!
# The sparse check, aliases and cited facts

Identities checked by sparse normal forms (`qeq sparse`), one in sixty variables whose dense size is `2 ^ 60`;
aliases used through their defining equations (`qeq [h, ...]`), never unfolded; the source of a cited fact.
-/

public section

namespace Qpp.Tests

theorem sparse_square (x y : Count) : (x + y) * (x + y) = x * x + 2 * x * y + y * y := by qeq sparse

theorem sparse_succ (x : Count) : Count.succ x ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by qeq sparse

theorem sparse_mass (a b : Mass) : (a + b) / b = a / b + 1 := by qeq sparse

theorem dense_mass (a b : Mass) : (a + b) / b = a / b + 1 := by qeq dense

/-- Sixty variables: the dense size is `2 ^ 60`, so `qeq` checks by normal forms. -/
theorem sixty (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 : Count) :
    1 * (x0 + x1) + 2 * (x1 + x2) + 3 * (x2 + x3) + 4 * (x3 + x4) + 5 * (x4 + x5) + 6 * (x5 + x6) + 7 * (x6 + x7) + 8 * (x7 + x8) + 9 * (x8 + x9) + 10 * (x9 + x10) + 11 * (x10 + x11) + 12 * (x11 + x12) + 13 * (x12 + x13) + 14 * (x13 + x14) + 15 * (x14 + x15) + 16 * (x15 + x16) + 17 * (x16 + x17) + 18 * (x17 + x18) + 19 * (x18 + x19) + 20 * (x19 + x20) + 21 * (x20 + x21) + 22 * (x21 + x22) + 23 * (x22 + x23) + 24 * (x23 + x24) + 25 * (x24 + x25) + 26 * (x25 + x26) + 27 * (x26 + x27) + 28 * (x27 + x28) + 29 * (x28 + x29) + 30 * (x29 + x30) + 31 * (x30 + x31) + 32 * (x31 + x32) + 33 * (x32 + x33) + 34 * (x33 + x34) + 35 * (x34 + x35) + 36 * (x35 + x36) + 37 * (x36 + x37) + 38 * (x37 + x38) + 39 * (x38 + x39) + 40 * (x39 + x40) + 41 * (x40 + x41) + 42 * (x41 + x42) + 43 * (x42 + x43) + 44 * (x43 + x44) + 45 * (x44 + x45) + 46 * (x45 + x46) + 47 * (x46 + x47) + 48 * (x47 + x48) + 49 * (x48 + x49) + 50 * (x49 + x50) + 51 * (x50 + x51) + 52 * (x51 + x52) + 53 * (x52 + x53) + 54 * (x53 + x54) + 55 * (x54 + x55) + 56 * (x55 + x56) + 57 * (x56 + x57) + 58 * (x57 + x58) + 59 * (x58 + x59) + 60 * (x59 + x0) =
    61 * x0 + 3 * x1 + 5 * x2 + 7 * x3 + 9 * x4 + 11 * x5 + 13 * x6 + 15 * x7 + 17 * x8 + 19 * x9 + 21 * x10 + 23 * x11 + 25 * x12 + 27 * x13 + 29 * x14 + 31 * x15 + 33 * x16 + 35 * x17 + 37 * x18 + 39 * x19 + 41 * x20 + 43 * x21 + 45 * x22 + 47 * x23 + 49 * x24 + 51 * x25 + 53 * x26 + 55 * x27 + 57 * x28 + 59 * x29 + 61 * x30 + 63 * x31 + 65 * x32 + 67 * x33 + 69 * x34 + 71 * x35 + 73 * x36 + 75 * x37 + 77 * x38 + 79 * x39 + 81 * x40 + 83 * x41 + 85 * x42 + 87 * x43 + 89 * x44 + 91 * x45 + 93 * x46 + 95 * x47 + 97 * x48 + 99 * x49 + 101 * x50 + 103 * x51 + 105 * x52 + 107 * x53 + 109 * x54 + 111 * x55 + 113 * x56 + 115 * x57 + 117 * x58 + 119 * x59 := by qeq

/-- `s` and `q` are aliases, atoms with their defining equations; the last step uses them without unfolding. -/
theorem alias_square (x y : Count) : (x + y) ^ 4 = x ^ 4 + 4 * x ^ 3 * y + 6 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + y ^ 4 := by
  obtain ⟨s, hs⟩ : ∃ s, s = x + y := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = x ^ 2 + 2 * x * y + y ^ 2 := ⟨_, rfl⟩
  have h2 : s ^ 2 = q := by rw [hs, hq]; qeq
  have h4 : q ^ 2 = x ^ 4 + 4 * x ^ 3 * y + 6 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + y ^ 4 := by rw [hq]; qeq
  have e : (x + y) ^ 4 = s ^ 4 := by rw [hs]
  rw [e]
  qeq [(s ^ 2 + q) • h2, h4]

/-- A combination with masses: `a = b + c` and `b = 2 c` give `a = 3 c`. -/
theorem alias_mass (a b c : Mass) (h₁ : a = b + c) (h₂ : b = 2 * c) : a = 3 * c := by
  qeq [h₁, h₂]

theorem polya_source : polya.source.doi = "10.1016/S0022-4049(00)00155-9" := rfl

end Qpp.Tests
