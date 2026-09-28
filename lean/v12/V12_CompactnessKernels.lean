import Mathlib.Tactic

/-!
Partial support for W20 v12 closure/tightness. The old product and Hodge
lemmas repeated the desired inequalities as hypotheses. They are replaced
by actual complex-product and finite-sum norm inequalities below.
Finite-sum Hodge control is NOT a proof of the continuum convolution bound.
Pointwise convergence is NOT a proof of local L2/L1 convergence.
-/

namespace SMScattering.W20Full

open scoped BigOperators Topology
open Filter

/-- Pointwise product difference, with no assumed norm estimate. -/
theorem v12_closure_product_difference_kernel
    (An Qn A Q : ℂ) :
    ‖An * Qn - A * Q‖ ≤
      ‖An - A‖ * ‖Qn‖ + ‖A‖ * ‖Qn - Q‖ := by
  have hid : An * Qn - A * Q = (An - A) * Qn + A * (Qn - Q) := by ring
  calc
    ‖An * Qn - A * Q‖ = ‖(An - A) * Qn + A * (Qn - Q)‖ := by rw [hid]
    _ ≤ ‖(An - A) * Qn‖ + ‖A * (Qn - Q)‖ := norm_add_le _ _
    _ = ‖An - A‖ * ‖Qn‖ + ‖A‖ * ‖Qn - Q‖ := by rw [norm_mul, norm_mul]

/-- Genuine finite-sum kernel control; no bound on the sum is assumed. -/
theorem v12_closure_hodge_far_kernel
    {ι : Type*} [Fintype ι] (K b : ι → ℂ) (κ : ℝ)
    (hK : ∀ i, ‖K i‖ ≤ κ) :
    ‖∑ i, K i * b i‖ ≤ κ * ∑ i, ‖b i‖ := by
  calc
    ‖∑ i, K i * b i‖ ≤ ∑ i, ‖K i * b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖K i‖ * ‖b i‖ := by simp_rw [norm_mul]
    _ ≤ ∑ i, κ * ‖b i‖ :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))
    _ = κ * ∑ i, ‖b i‖ := by rw [Finset.mul_sum]

/-- Actual sequential product limit over complex scalars. -/
theorem v12_closure_pointwise_product_limit
    (An Qn : ℕ → ℂ) (A Q : ℂ)
    (hA : Tendsto An atTop (𝓝 A)) (hQ : Tendsto Qn atTop (𝓝 Q)) :
    Tendsto (fun n => An n * Qn n - A * Q) atTop (𝓝 0) := by
  simpa using (hA.mul hQ).sub tendsto_const_nhds

theorem v12_tightness_cauchy_kernel
    (tailN tailN' lowDiff totalDiff eps : ℝ)
    (ht1 : tailN ≤ eps) (ht2 : tailN' ≤ eps) (hlow : lowDiff ≤ eps)
    (htotal : totalDiff ≤ tailN + tailN' + lowDiff) :
    totalDiff ≤ 3 * eps := by linarith

theorem v12_tightness_holder_exponent :
    (1 : ℝ) - (3 : ℝ) / 4 = 1 / 4 := by norm_num

#print axioms v12_closure_product_difference_kernel
#print axioms v12_closure_hodge_far_kernel
#print axioms v12_closure_pointwise_product_limit
#print axioms v12_tightness_cauchy_kernel
#print axioms v12_tightness_holder_exponent

end SMScattering.W20Full
