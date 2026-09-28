import Mathlib.Tactic

/-!
Section 2: cleared-denominator algebra for D_j q_j = tau/g.

The analytic quotient/product rules are separated from the finite algebra:
after multiplying by g^2, this theorem verifies the exact cancellation in
the numerator. No sorry/admit/custom axiom.
-/

namespace SMScattering.Section2

theorem q0_compatibility_numerator
    (g zbar lap sigma : ℂ)
    (hg : g ≠ 0) :
    lap / g - 2 * zbar * sigma / g^2
      =
    (lap - 2 * zbar * sigma / g) / g := by
  field_simp [hg]
  ring

/-- Pure numerator identity used after expanding ∂_j g and i a_j. -/
theorem q0_spatial_numerator
    (z zbar zj zbj : ℂ) :
    zj * (zbar * zj + z * zbj)
      + (zbar * zj - z * zbj) * zj
      =
    2 * zbar * zj^2 := by
  ring

#print axioms q0_compatibility_numerator
#print axioms q0_spatial_numerator

end SMScattering.Section2
