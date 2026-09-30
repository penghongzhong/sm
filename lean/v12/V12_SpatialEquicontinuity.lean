import lean.v12.V12_FrequencyTightnessLimit

/-!
Actual spatial equicontinuity for a bounded family of L2 inputs.
No spatial modulus, derivative bound or equicontinuity is assumed.
The proof uses the already established L2 translation continuity of the
fixed kernel and the actual convolution distance estimate.
-/

set_option autoImplicit false

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology

/-- Every uniformly L2-bounded input family has an equicontinuous family of
actual convolution representatives for one fixed L2 kernel. -/
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
  exact (v12_L2ConvolutionRep_dist_le k (f i) x₀ x).trans
    (mul_le_mul_of_nonneg_left (hBound i)
      (mul_nonneg (norm_nonneg _) dist_nonneg))

/-- Specialization to the exact manuscript cutoff kernel. The indices may
include both the sequence index and time, so a uniform energy bound supplies
the common spatial equicontinuity required on every compact cylinder. -/
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
