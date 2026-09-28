import Mathlib.Tactic

/-!
Partial support for W20 v12 closure/tightness. Replaces goal-as-hypothesis
wrappers by actual complex-product and finite-sum norm proofs.
Finite sums are not continuum convolutions; scalar limits are not L2 limits.
-/

namespace SMScattering.W20Full

open scoped BigOperators Topology
open Filter

theorem v12_closure_product_difference_kernel
    (An Qn A Q : ℂ) :
    ‖An * Qn - A * Q‖ ≤ ‖An - A‖ * ‖Qn‖ + ‖A‖ * ‖Qn - Q‖ := by
  have hid : An * Qn - A * Q = (An - A) * Qn + A * (Qn - Q) := by ring
  calc
    ‖An * Qn - A * Q‖ = ‖(An - A) * Qn + A * (Qn - Q)‖ := by rw [hid]
    _ ≤ ‖(An - A) * Qn‖ + ‖A * (Qn - Q)‖ := norm_add_le _ _
    _ = ‖An - A‖ * ‖Qn‖ + ‖A‖ * ‖Qn - Q‖ := by rw [norm_mul, norm_mul]

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

theorem v12_closure_pointwise_product_limit
    (An Qn : ℕ → ℂ) (A Q : ℂ)
    (hA : Tendsto An atTop (𝓝 A)) (hQ : Tendsto Qn atTop (𝓝 Q)) :
    Tendsto (fun n => An n * Qn n - A * Q) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => A * Q) atTop (𝓝 (A * Q)) :=
    tendsto_const_nhds
  simpa using (hA.mul hQ).sub hconst

theorem v12_tightness_cauchy_kernel
    (tailN tailN' lowDiff totalDiff eps : ℝ)
    (ht1 : tailN ≤ eps) (ht2 : tailN' ≤ eps) (hlow : lowDiff ≤ eps)
    (htotal : totalDiff ≤ tailN + tailN' + lowDiff) :
    totalDiff ≤ 3 * eps := by linarith

theorem v12_tightness_holder_exponent :
    (1 : ℝ) - (3 : ℝ) / 4 = 1 / 4 := by norm_num


/--
Continuum far-field estimate used in v12:thm:closure.
If the kernel is uniformly bounded by κ on the integration region, then the
Bochner integral is bounded by κ times the L1 mass.  This is the exact
continuum analogue of the old finite-sum support kernel.
-/
theorem v12_closure_hodge_far_integral
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (K f : X → ℂ) (κ : ℝ)
    (hκ : 0 ≤ κ)
    (hf : Integrable f μ)
    (hK : ∀ᵐ x ∂μ, ‖K x‖ ≤ κ) :
    ‖∫ x, K x * f x ∂μ‖
      ≤ κ * ∫ x, ‖f x‖ ∂μ := by
  have hg : Integrable (fun x => κ * ‖f x‖) μ := by
    exact hf.norm.const_mul κ
  apply norm_integral_le_of_norm_le hg
  filter_upwards [hK] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/--
Near/far two-error closure: if the near contribution tends to zero at fixed
R' and the far contribution is bounded by C/R', choosing R' first and n
second yields an arbitrary ε bound.  This is the scalar quantifier order used
after Young's inequality.
-/
theorem v12_near_far_epsilon_kernel
    (near far total eps : ℝ)
    (hnear0 : 0 ≤ near) (hfar0 : 0 ≤ far)
    (hnear : near ≤ eps / 2)
    (hfar : far ≤ eps / 2)
    (htotal : total ≤ near + far) :
    total ≤ eps := by
  linarith

#print axioms v12_closure_product_difference_kernel
#print axioms v12_closure_hodge_far_kernel
#print axioms v12_closure_hodge_far_integral
#print axioms v12_near_far_epsilon_kernel
#print axioms v12_closure_pointwise_product_limit
#print axioms v12_tightness_cauchy_kernel
#print axioms v12_tightness_holder_exponent

end SMScattering.W20Full
