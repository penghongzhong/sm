import lean.v12.V12_SourceProducts

/-!
The continuum far-field Hodge estimate for the actual two-dimensional
Biot-Savart kernel. No finite-sum surrogate or assumed kernel estimate.
Near-field Young convergence, HLS bounds and interpolation remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_hodgeRotation (z : V12Spatial) : V12Spatial :=
  WithLp.toLp 2 ![-z 1, z 0]

noncomputable def v12_hodgeKernel (z : V12Spatial) : V12Spatial :=
  (2 * Real.pi * ‖z‖ ^ 2)⁻¹ • v12_hodgeRotation z

theorem v12_hodgeRotation_norm (z : V12Spatial) : ‖v12_hodgeRotation z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, v12_hodgeRotation, Fin.sum_univ_two, add_comm]

theorem v12_hodgeRotation_continuous : Continuous v12_hodgeRotation := by
  change Continuous (fun z : V12Spatial => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-z 1, z 0])
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro j
  fin_cases j <;> simp <;> fun_prop

theorem v12_hodgeKernel_measurable : Measurable v12_hodgeKernel := by
  unfold v12_hodgeKernel
  have hs : Measurable (fun z : V12Spatial => (2 * Real.pi * ‖z‖ ^ 2)⁻¹) := by
    fun_prop
  exact hs.smul v12_hodgeRotation_continuous.measurable

theorem v12_hodgeKernel_norm (z : V12Spatial) :
    ‖v12_hodgeKernel z‖ = (2 * Real.pi * ‖z‖)⁻¹ := by
  by_cases hz : ‖z‖ = 0
  · have hz0 : z = 0 := norm_eq_zero.mp hz
    simp [v12_hodgeKernel, hz0, v12_hodgeRotation]
  · rw [v12_hodgeKernel, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), v12_hodgeRotation_norm]
    field_simp [hz, Real.pi_ne_zero]
    <;> ring

theorem v12_hodgeKernel_far_bound
    (R L : ℝ) (hL : 0 < L) (hRL : 2 * R ≤ L)
    (x y : V12Spatial) (hx : ‖x‖ ≤ R) (hy : L ≤ ‖y‖) :
    ‖v12_hodgeKernel (x-y)‖ ≤ (Real.pi * L)⁻¹ := by
  have htri : ‖y‖ ≤ ‖x-y‖ + ‖x‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_sub_add y x
  have hdist : L / 2 ≤ ‖x-y‖ := by linarith
  have hpos : 0 < Real.pi * L := mul_pos Real.pi_pos hL
  have hden : Real.pi * L ≤ 2 * Real.pi * ‖x-y‖ := by nlinarith [Real.pi_pos]
  rw [v12_hodgeKernel_norm]
  exact inv_anti₀ hpos hden

/-- The actual far-field integral exists and obeys its L1-density bound. -/
theorem v12_hodge_far_integrable_and_bound
    (R L : ℝ) (hL : 0 < L) (hRL : 2 * R ≤ L)
    (x : V12Spatial) (hx : ‖x‖ ≤ R)
    (B : V12Spatial → ℝ) (hB : Integrable B (volume : Measure V12Spatial)) :
    let ν := (volume : Measure V12Spatial).restrict {y | L ≤ ‖y‖}
    Integrable (fun y => B y • v12_hodgeKernel (x-y)) ν ∧
      ‖∫ y, B y • v12_hodgeKernel (x-y) ∂ν‖ ≤
        (Real.pi * L)⁻¹ * ∫ y, ‖B y‖ ∂ν := by
  dsimp only
  let ν := (volume : Measure V12Spatial).restrict {y | L ≤ ‖y‖}
  have hs : MeasurableSet {y : V12Spatial | L ≤ ‖y‖} :=
    measurableSet_le measurable_const measurable_norm
  have hmeas : AEStronglyMeasurable
      (fun y => B y • v12_hodgeKernel (x-y)) ν :=
    hB.aestronglyMeasurable.restrict.smul
      (v12_hodgeKernel_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hdom : Integrable (fun y => (Real.pi * L)⁻¹ * ‖B y‖) ν :=
    hB.norm.restrict.const_mul _
  have hbound : ∀ᵐ y ∂ν,
      ‖B y • v12_hodgeKernel (x-y)‖ ≤ (Real.pi * L)⁻¹ * ‖B y‖ := by
    filter_upwards [ae_restrict_mem hs] with y hy
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (v12_hodgeKernel_far_bound R L hL hRL x y hx hy)
      (norm_nonneg _)
  have hi : Integrable (fun y => B y • v12_hodgeKernel (x-y)) ν :=
    hdom.mono' hmeas hbound
  refine ⟨hi, ?_⟩
  calc
    ‖∫ y, B y • v12_hodgeKernel (x-y) ∂ν‖ ≤
        ∫ y, (Real.pi * L)⁻¹ * ‖B y‖ ∂ν := norm_integral_le_of_norm_le hdom hbound
    _ = _ := integral_const_mul _ _

#print axioms v12_hodgeKernel_measurable
#print axioms v12_hodgeKernel_norm
#print axioms v12_hodgeKernel_far_bound
#print axioms v12_hodge_far_integrable_and_bound
end SMScattering.W20Full
