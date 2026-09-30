import lean.v12.V12_YJYoungRawRepresentative
import lean.v12.V12_YKBoundedTimeUpgrade
import lean.v12.V12_YPGenericLpSections

/-! Actual truncated Hodge convolution tends to zero in spacetime L^(4/3)
from density L1 convergence and a uniform spatial L1 energy budget. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_timeYoungNear (R : ℝ) (D : V12Spacetime → ℝ) (t : ℝ) :=
  v12_youngConvolutionClass ((4 : ℝ≥0∞) / 3) (v12_truncatedHodgeKernelClass R) (fun y => D (t,y))

noncomputable def v12_spacetimeNearHodge (R : ℝ) (D : V12Spacetime → ℝ) (z : V12Spacetime) : V12Spatial :=
  v12_rawNearHodge R (fun y => D (z.1,y)) z.2

theorem v12_spacetimeNearHodge_stronglyMeasurable
    (R : ℝ) (D : V12Spacetime → ℝ) (hD : StronglyMeasurable D) :
    StronglyMeasurable (v12_spacetimeNearHodge R D) := by
  have hd : StronglyMeasurable (fun p : V12Spacetime × V12Spatial => D (p.1.1,p.2)) :=
    hD.comp_measurable (measurable_fst.fst.prodMk measurable_snd)
  have hk : StronglyMeasurable (fun p : V12Spacetime × V12Spatial =>
      ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel) (p.1.2-p.2)) :=
    ((v12_hodgeKernel_measurable.indicator measurableSet_ball).comp
      (measurable_fst.snd.sub measurable_snd)).stronglyMeasurable
  exact (hd.smul hk).integral_prod_right'

theorem v12_actual_nearHodge_spacetime_limit
    (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ) (Dn : ℕ → V12Spacetime → ℝ)
    (hDn : ∀ n, StronglyMeasurable (Dn n))
    (hi : ∀ n, Integrable (Dn n) (μ.prod (volume : Measure V12Spatial)))
    (E : ℝ) (hE : 0 ≤ E)
    (hb : ∀ n, ∀ᵐ t ∂μ, (∫ y : V12Spatial, ‖Dn n (t,y)‖) ≤ E)
    (hlim : Tendsto (fun n => ∫ z, ‖Dn n z‖ ∂(μ.prod (volume : Measure V12Spatial))) atTop (𝓝 0)) :
    (∀ n, MemLp (v12_spacetimeNearHodge R (Dn n)) ((4 : ℝ≥0∞) / 3)
      (μ.prod (volume : Measure V12Spatial))) ∧
    Tendsto (fun n => (eLpNorm (v12_spacetimeNearHodge R (Dn n)) ((4 : ℝ≥0∞) / 3)
      (μ.prod (volume : Measure V12Spatial))).toReal) atTop (𝓝 0) := by
  letI : Fact (((4 : ℝ≥0∞) / 3) ≠ ∞) := ⟨by finiteness⟩
  let Y := fun n => v12_timeYoungNear R (Dn n)
  let K := ‖v12_truncatedHodgeKernelClass R‖
  have hrep : ∀ n, ∀ᵐ t ∂μ, (Y n t : V12Spatial → V12Spatial) =ᵐ[volume]
      fun x => v12_spacetimeNearHodge R (Dn n) (t,x) := by
    intro n
    filter_upwards [(hi n).prod_right_ae] with t ht
    exact v12_youngHodge_raw_ae R (fun y => Dn n (t,y)) ht
  have hYm : ∀ n, AEStronglyMeasurable (Y n) μ := by
    intro n
    exact v12_generic_aestronglyMeasurable_Lp_sections μ ((4 : ℝ≥0∞) / 3)
      (v12_spacetimeNearHodge R (Dn n))
      (v12_spacetimeNearHodge_stronglyMeasurable R (Dn n) (hDn n)).aestronglyMeasurable
      (Y n) (hrep n)
  have hYbd : ∀ n, ∀ᵐ t ∂μ, ‖Y n t‖ ≤ (∫ y : V12Spatial, ‖Dn n (t,y)‖) * K := by
    intro n
    filter_upwards [(hi n).prod_right_ae] with t ht
    exact v12_truncatedHodge_young_bound R (fun y => Dn n (t,y)) ht
  have hYuniform : ∀ n, ∀ᵐ t ∂μ, ‖Y n t‖ ≤ E*K := by
    intro n
    filter_upwards [hYbd n, hb n] with t ht he
    exact ht.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have hYint : ∀ n, Integrable (fun t => ‖Y n t‖) μ := by
    intro n
    exact (((hi n).norm.integral_prod_left).mul_const K).mono'
      (hYm n).norm (by simpa only [norm_norm] using hYbd n)
  have hYlim : Tendsto (fun n => ∫ t, ‖Y n t‖ ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (fun t => norm_nonneg _))
      (fun n => ?_) (by simpa only [zero_mul] using hlim.mul_const K)
    calc
      (∫ t, ‖Y n t‖ ∂μ) ≤ ∫ t, (∫ y : V12Spatial, ‖Dn n (t,y)‖) * K ∂μ :=
        integral_mono_ae (hYint n) (((hi n).norm.integral_prod_left).mul_const K) (hYbd n)
      _ = (∫ z, ‖Dn n z‖ ∂(μ.prod (volume : Measure V12Spatial))) * K := by
        rw [integral_mul_const, ← integral_prod _ (hi n).norm]
  obtain ⟨hY2, hY2lim⟩ := v12_bounded_time_L1_to_L2 μ Y hYm (E*K)
    (mul_nonneg hE (norm_nonneg _)) hYuniform hYlim
  have hY43lim := v12_finite_measure_L2_to_fourThirds_limit μ Y hY2 hY2lim
  have he (n : ℕ) : eLpNorm (Y n) ((4 : ℝ≥0∞) / 3) μ =
      eLpNorm (v12_spacetimeNearHodge R (Dn n)) ((4 : ℝ≥0∞) / 3)
        (μ.prod (volume : Measure V12Spatial)) :=
    v12_generic_eLpNorm_sections_eq_spacetime μ ((4 : ℝ≥0∞) / 3)
      (v12_spacetimeNearHodge R (Dn n))
      (v12_spacetimeNearHodge_stronglyMeasurable R (Dn n) (hDn n)).aestronglyMeasurable
      (Y n) (hrep n)
  refine ⟨?_, ?_⟩
  · intro n
    rw [MemLp, ← he]
    have hp : (4 : ℝ≥0∞) / 3 ≤ 2 := by
      apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
      norm_num
    exact (hY2 n).mono_exponent hp
  · simpa only [he] using hY43lim

#print axioms v12_spacetimeNearHodge_stronglyMeasurable
#print axioms v12_actual_nearHodge_spacetime_limit
end SMScattering.W20Full
