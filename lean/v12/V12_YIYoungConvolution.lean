import lean.v12.V12_YHodgeNearKernel
import Mathlib.Analysis.Convolution

/-! Construct the Lp-valued Bochner convolution and prove its Young bound.
The raw pointwise integral representative is a separate tracked step. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_subRightFamily : C(V12Spatial, C(V12Spatial, V12Spatial)) :=
  ContinuousMap.curry ⟨fun z : V12Spatial × V12Spatial => z.2 - z.1, by fun_prop⟩

theorem v12_subRight_measurePreserving (y : V12Spatial) :
    MeasurePreserving (v12_subRightFamily y)
      (volume : Measure V12Spatial) (volume : Measure V12Spatial) := by
  change MeasurePreserving (fun x : V12Spatial => x-y) volume volume
  exact measurePreserving_sub_right (volume : Measure V12Spatial) y

noncomputable def v12_translateKernel (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Lp V12Spatial p (volume : Measure V12Spatial)) (y : V12Spatial) :=
  Lp.compMeasurePreserving (v12_subRightFamily y) (v12_subRight_measurePreserving y) K

theorem v12_translateKernel_continuous (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K : Lp V12Spatial p (volume : Measure V12Spatial)) :
    Continuous (v12_translateKernel p K) := by
  exact Continuous.compMeasurePreservingLp
    (μ := (volume : Measure V12Spatial)) (ν := (volume : Measure V12Spatial))
    (E := V12Spatial) (p := p) (f := fun _ : V12Spatial => K)
    continuous_const v12_subRightFamily.continuous v12_subRight_measurePreserving hp

@[simp] theorem v12_translateKernel_norm (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Lp V12Spatial p (volume : Measure V12Spatial)) (y : V12Spatial) :
    ‖v12_translateKernel p K y‖ = ‖K‖ :=
  Lp.norm_compMeasurePreserving K (v12_subRight_measurePreserving y)

noncomputable def v12_youngConvolutionClass (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (K : Lp V12Spatial p (volume : Measure V12Spatial)) (B : V12Spatial → ℝ) :=
  ∫ y, B y • v12_translateKernel p K y

theorem v12_youngConvolutionClass_integrable_bound
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (K : Lp V12Spatial p (volume : Measure V12Spatial))
    (B : V12Spatial → ℝ) (hB : Integrable B (volume : Measure V12Spatial)) :
    Integrable (fun y => B y • v12_translateKernel p K y) (volume : Measure V12Spatial) ∧
      ‖v12_youngConvolutionClass p K B‖ ≤ (∫ y, ‖B y‖) * ‖K‖ := by
  have hdom : Integrable (fun y => ‖B y‖ * ‖K‖) (volume : Measure V12Spatial) :=
    hB.norm.mul_const ‖K‖
  have hmeas := hB.aestronglyMeasurable.smul
    (v12_translateKernel_continuous p hp K).aestronglyMeasurable
  have hbd : ∀ y, ‖B y • v12_translateKernel p K y‖ ≤ ‖B y‖ * ‖K‖ := by
    intro y
    rw [norm_smul, v12_translateKernel_norm]
  refine ⟨hdom.mono' hmeas (Filter.Eventually.of_forall hbd), ?_⟩
  unfold v12_youngConvolutionClass
  exact (norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hbd)).trans_eq
    (integral_mul_const _ _)


local instance : Fact (1 ≤ (4 : ℝ≥0∞) / 3) := ⟨v12_one_le_fourThirds_ENNReal⟩

noncomputable def v12_truncatedHodgeKernelClass (R : ℝ) :
    Lp V12Spatial ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) :=
  (v12_hodgeKernel_truncated_memLp R).toLp
    ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel)

theorem v12_truncatedHodgeKernelClass_ae (R : ℝ) :
    (v12_truncatedHodgeKernelClass R : V12Spatial → V12Spatial) =ᵐ[volume]
      (Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel :=
  (v12_hodgeKernel_truncated_memLp R).coeFn_toLp

/-- Young's budget instantiated at the actual singular Hodge kernel. -/
theorem v12_truncatedHodge_young_bound
    (R : ℝ) (B : V12Spatial → ℝ) (hB : Integrable B (volume : Measure V12Spatial)) :
    ‖v12_youngConvolutionClass ((4 : ℝ≥0∞) / 3) (v12_truncatedHodgeKernelClass R) B‖ ≤
      (∫ y, ‖B y‖) * ‖v12_truncatedHodgeKernelClass R‖ := by
  exact (v12_youngConvolutionClass_integrable_bound _ (by finiteness)
    (v12_truncatedHodgeKernelClass R) B hB).2

#print axioms v12_truncatedHodgeKernelClass_ae
#print axioms v12_truncatedHodge_young_bound

theorem v12_truncatedHodgeKernel_integrable (R : ℝ) :
    Integrable ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel)
      (volume : Measure V12Spatial) := by
  rw [integrable_indicator_iff measurableSet_ball]
  apply (integrable_norm_iff v12_hodgeKernel_measurable.aestronglyMeasurable.restrict).mp
  simpa [IntegrableOn] using v12_hodgeKernel_ball_power_integrable R 1 (by norm_num)

noncomputable def v12_rawNearHodge (R : ℝ) (B : V12Spatial → ℝ) (x : V12Spatial) :=
  ∫ y, B y • ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel) (x-y)

theorem v12_rawNearHodge_integrable (R : ℝ) (B : V12Spatial → ℝ)
    (hB : Integrable B (volume : Measure V12Spatial)) :
    Integrable (v12_rawNearHodge R B) (volume : Measure V12Spatial) := by
  exact hB.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
    (v12_truncatedHodgeKernel_integrable R)

theorem v12_rawNearHodge_ae_integrand (R : ℝ) (B : V12Spatial → ℝ)
    (hB : Integrable B (volume : Measure V12Spatial)) :
    ∀ᵐ x ∂(volume : Measure V12Spatial), Integrable (fun y =>
      B y • ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel) (x-y))
      (volume : Measure V12Spatial) := by
  exact hB.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ)
    (v12_truncatedHodgeKernel_integrable R)

#print axioms v12_truncatedHodgeKernel_integrable
#print axioms v12_rawNearHodge_integrable
#print axioms v12_rawNearHodge_ae_integrand
#print axioms v12_translateKernel_continuous
#print axioms v12_youngConvolutionClass_integrable_bound
end SMScattering.W20Full
