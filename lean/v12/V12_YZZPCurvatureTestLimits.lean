import lean.v12.V12_YSCurvatureCutoffL1
import lean.v12.V12_YZZCCompactDistributionTests

/-! Original curvature B tested against complex compact functions. The
real-to-complex embedding preserves the exact L1 error norm; density
convergence is derived from the SAME raw Q local strong L2 limit. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_curvature_complex_memLp_one
    (μ : Measure V12Spacetime) (q : V12Spacetime → V12Field) (hq : MemLp q 2 μ) :
    MemLp (fun z => (v12_curvatureDensity (q z) : ℂ)) 1 μ := by
  have hq' : MemLp q ((1 : ℝ≥0∞)*2) μ := by simpa only [one_mul] using hq
  exact (v12_curvatureDensity_memLp μ q 1 hq').ofReal

theorem v12_curvature_complex_L1_limit
    (μ : Measure V12Spacetime) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn : ∀ n, MemLp (qn n) 2 μ) (hq : MemLp q 2 μ)
    (hlim : Tendsto (fun n => (eLpNorm (fun z => qn n z-q z) 2 μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm (fun z => (v12_curvatureDensity (qn n z) : ℂ) -
      (v12_curvatureDensity (q z) : ℂ)) 1 μ).toReal) atTop (𝓝 0) := by
  obtain ⟨hi, ht⟩ := v12_raw_curvature_L1_limit μ qn q hn hq hlim
  have he (n : ℕ) : (eLpNorm (fun z => (v12_curvatureDensity (qn n z) : ℂ) -
      (v12_curvatureDensity (q z) : ℂ)) 1 μ).toReal =
      ∫ z, ‖v12_curvatureDensity (qn n z)-v12_curvatureDensity (q z)‖ ∂μ := by
    have hC : MemLp (fun z => (v12_curvatureDensity (qn n z) : ℂ) -
        (v12_curvatureDensity (q z) : ℂ)) 1 μ :=
      (v12_curvature_complex_memLp_one μ (qn n) (hn n)).sub (v12_curvature_complex_memLp_one μ q hq)
    have hR : MemLp (fun z => v12_curvatureDensity (qn n z)-v12_curvatureDensity (q z)) 1 μ :=
      memLp_one_iff_integrable.mpr (hi n)
    have hnorm := eLpNorm_congr_norm_ae (p := (1 : ℝ≥0∞)) hC.aestronglyMeasurable hR.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by rw [← Complex.ofReal_sub]; exact Complex.norm_real _))
    rw [hnorm, ← Lp.norm_toLp _ hR, L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [hR.coeFn_toLp] with z hz
    rw [hz]
  simpa only [he] using ht

theorem v12_actual_curvature_compact_test_limit
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z-q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (ψ : V12Spacetime → ℂ) (hc : HasCompactSupport ψ) (hψ : Continuous ψ) :
    Tendsto (fun n => ∫ z, (v12_curvatureDensity (qn n z) : ℂ) * ψ z ∂v12_slab_measure a b)
      atTop (𝓝 (∫ z, (v12_curvatureDensity (q z) : ℂ) * ψ z ∂v12_slab_measure a b)) := by
  have h := v12_raw_local_L1_compact_test_limit a b
    (fun n z => (v12_curvatureDensity (qn n z) : ℂ))
    (fun z => (v12_curvatureDensity (q z) : ℂ))
    (fun R n => v12_curvature_complex_memLp_one _ (qn n) (hn R n))
    (fun R => v12_curvature_complex_memLp_one _ q (hq R))
    (fun R => v12_curvature_complex_L1_limit _ qn q (hn R) (hq R) (hlim R)) ψ hc hψ
  simpa only [smul_eq_mul, mul_comm] using h

#print axioms v12_curvature_complex_L1_limit
#print axioms v12_actual_curvature_compact_test_limit
end SMScattering.W20Full
