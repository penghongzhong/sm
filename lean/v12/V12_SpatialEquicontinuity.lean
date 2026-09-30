import lean.v12.V12_FrequencyTightnessLimit

/-! Actual spatial equicontinuity from a uniformly L2-bounded input family.
No spatial modulus, derivative estimate or equicontinuity is an input. -/

set_option autoImplicit false

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology

theorem v12_L2ConvolutionRep_equicontinuous_of_uniform_bound
    {ι : Type*} (k : V12ScalarL2) (f : ι → V12SpatialL2)
    (M : ℝ) (hBound : ∀ i, ‖f i‖ ≤ M) :
    Equicontinuous (fun i => v12_L2ConvolutionRep k (f i)) := by
  intro x₀
  let b : V12Spatial → ℝ := fun x =>
    ‖v12_L2ConvolutionPairing‖ *
      dist (v12_reflectedTranslate k x₀) (v12_reflectedTranslate k x) * M
  have hb : Continuous b := by
    exact (continuous_const.mul
      (continuous_const.dist (v12_continuous_reflectedTranslate k))).mul continuous_const
  have hlim : Tendsto b (𝓝 x₀) (𝓝 0) := by
    simpa [b] using hb.tendsto x₀
  apply Metric.equicontinuousAt_of_continuity_modulus b hlim
    (fun i => v12_L2ConvolutionRep k (f i))
  apply Filter.Eventually.of_forall
  intro x i
  have hnonneg : 0 ≤ ‖v12_L2ConvolutionPairing‖ *
      dist (v12_reflectedTranslate k x₀) (v12_reflectedTranslate k x) := by
    exact mul_nonneg (norm_nonneg v12_L2ConvolutionPairing) dist_nonneg
  exact (v12_L2ConvolutionRep_dist_le k (f i) x₀ x).trans
    (mul_le_mul_of_nonneg_left (hBound i) hnonneg)

/-- The index family may include time after choosing representatives for
which the uniform energy bound holds. An a.e. time bound must not silently
be promoted to a pointwise bound. -/
theorem v12_cutoff_equicontinuous_of_uniform_L2
    {ι : Type*}
    (p : V12Spatial → ℝ) (hp_cpt : HasCompactSupport p)
    (hp_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (N : ℕ) (f : ι → V12SpatialL2)
    (M : ℝ) (hBound : ∀ i, ‖f i‖ ≤ M) :
    Equicontinuous (fun i x =>
      v12_L2ConvolutionBCFCLM (v12_cutoffKernelL2 p hp_cpt hp_smooth N) (f i) x) := by
  exact v12_L2ConvolutionRep_equicontinuous_of_uniform_bound
    (v12_cutoffKernelL2 p hp_cpt hp_smooth N) f M hBound

#print axioms v12_L2ConvolutionRep_equicontinuous_of_uniform_bound
#print axioms v12_cutoff_equicontinuous_of_uniform_L2

end SMScattering.W20Full
