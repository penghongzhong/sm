import Mathlib.Tactic

/-!
Section 2 explicit coefficient constant check.
Paper choice: C_coeff = 100 * (1 + C_K^2).
-/

namespace SMScattering.Section2

theorem coefficient_constant_dominates
    (C_K : ℝ) (hK : 0 ≤ C_K) :
    4 ≤ 100 * (1 + C_K^2) ∧
    4 * C_K ≤ 100 * (1 + C_K^2) ∧
    20 ≤ 100 * (1 + C_K^2) ∧
    20 + 4 * C_K^2 ≤ 100 * (1 + C_K^2) := by
  constructor
  · nlinarith [sq_nonneg C_K]
  constructor
  · nlinarith [sq_nonneg (5 * C_K - 1)]
  constructor
  · nlinarith [sq_nonneg C_K]
  · nlinarith [sq_nonneg C_K]

#print axioms coefficient_constant_dominates

end SMScattering.Section2
