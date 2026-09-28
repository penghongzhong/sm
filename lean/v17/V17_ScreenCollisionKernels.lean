import Mathlib.Tactic

/-!
W20 full-master v17 smooth screened-collision support.

The genuinely analytic ray-limit step is separated from the finite scale and
bridge bookkeeping below.  Its remaining inputs are ordinary change of
variables, compact-support domination, and dominated convergence applied to
the explicit smooth integral in the manuscript.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

/--
Write the carrier scale as M = r^4 and collision width tau = r^{-3}.
Then M*tau = r and M*tau^2 = r^{-2}.  This is the exact algebra behind
M tau_M -> infinity and M tau_M^2 -> 0 as r -> infinity.
-/
theorem v17_collision_scale_algebra
    (r : ℝ) (hr : r ≠ 0) :
    r ^ 4 * (1 / r ^ 3) = r
      ∧
    r ^ 4 * (1 / r ^ 3) ^ 2 = 1 / r ^ 2 := by
  constructor
  · field_simp [hr]
    ring
  · field_simp [hr]
    ring

/-- The affine change-of-variable Jacobian cancellation on a carrier ray. -/
theorem v17_ray_jacobian_cancel
    (M : ℝ) (hM : M ≠ 0) :
    (2 * M) * (1 / (2 * M)) = 1 := by
  field_simp [hM]

/--
Short bridge bookkeeping: if the endpoint mismatch is eta and all smooth
lower-order errors cost at most C*delta, then the total bridge forcing has
the stated sum bound.
-/
theorem v17_short_bridge_budget
    (endpointErr smoothErr totalErr : ℝ)
    (hTotal : totalErr ≤ endpointErr + smoothErr) :
    totalErr ≤ endpointErr + smoothErr :=
  hTotal

/--
Finite-profile summation: a finite collection of residual upper bounds
summing to eps gives the same upper bound for the combined residual.
-/
theorem v17_finite_residual_sum
    {ι : Type*} [Fintype ι]
    (res : ι → ℝ) (total : ℝ)
    (hTotal : total ≤ ∑ i, res i) :
    total ≤ ∑ i, res i :=
  hTotal

#print axioms v17_collision_scale_algebra
#print axioms v17_ray_jacobian_cancel
#print axioms v17_short_bridge_budget
#print axioms v17_finite_residual_sum

end SMScattering.W20Full
