import Mathlib.Tactic

/-!
W20 full-master W2 support kernels.

W2 intentionally retains only the normalized constant-connection algebra and
the obstruction to interchanging a packet sum with an outer supremum.  The
withdrawn local-L4/URS implications are not certified as theorems.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

open scoped BigOperators

/-- Normalized spatial derivative scale when m=k-Lambda. -/
theorem w2_spatial_scale_kernel
    (k Lambda : ℤ) :
    (-2 * k) + 2 * (k - Lambda) = -2 * Lambda := by
  ring

/-- Normalized time derivative scale for the 2^(3m) component. -/
theorem w2_time_scale3_kernel
    (k Lambda : ℤ) :
    (-3 * k) + 3 * (k - Lambda) = -3 * Lambda := by
  ring

/-- Normalized time derivative scale for the 2^k 2^(2m) component. -/
theorem w2_time_scale2_kernel
    (k Lambda : ℤ) :
    (-3 * k) + k + 2 * (k - Lambda) = -2 * Lambda := by
  ring

/--
Finite diagonal obstruction: for each column n the diagonal matrix has column
sum one, while summing the row suprema gives N.
-/
theorem w2_no_sup_sum_finite
    (N : ℕ) :
    (∑ _j : Fin N, (1 : ℝ)) = N := by
  simp

theorem w2_diagonal_column_sum
    {N : ℕ} (n : Fin N) :
    (∑ j : Fin N, (if j = n then (1 : ℝ) else 0)) = 1 := by
  simp

/-- The free conjugation residual is just finite algebra once the product rule is supplied. -/
theorem w2_covariant_split_kernel
    (main db divb b2 b0 rhs : ℂ)
    (h :
      rhs = main + db + divb + b2 - b0) :
    rhs = main + db + divb + b2 - b0 :=
  h

#print axioms w2_spatial_scale_kernel
#print axioms w2_time_scale3_kernel
#print axioms w2_time_scale2_kernel
#print axioms w2_no_sup_sum_finite
#print axioms w2_diagonal_column_sum
#print axioms w2_covariant_split_kernel

end SMScattering.W20Full
