import lean.v12.V12_YSHodgeFractionalDomination
import Mathlib.Analysis.Convolution

/-! Actual vector Hodge L^(4/3)->L4 estimate from the precisely registered
scalar HLS theorem. Kernel identification, integrability, measurability and
norm domination are proved, not included in the external input. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_actual_hodge_HLS (hHLS : V12ExternalHLS2D) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : V12Spatial → ℝ,
      MemLp B ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) →
      (∀ᵐ x ∂(volume : Measure V12Spatial),
        Integrable (fun y => B y • v12_hodgeKernel (x-y)) (volume : Measure V12Spatial)) ∧
      MemLp (v12_rawHodgePotential B) 4 (volume : Measure V12Spatial) ∧
      eLpNorm (v12_rawHodgePotential B) 4 (volume : Measure V12Spatial) ≤
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * C) *
          eLpNorm B ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) := by
  obtain ⟨C, hC, hH⟩ := v12_externalHLS_hodge_exponents hHLS
  refine ⟨C, hC, ?_⟩
  intro B hB
  let f : V12Spatial → ℂ := fun y => (‖B y‖ : ℂ)
  have hfm : AEStronglyMeasurable f (volume : Measure V12Spatial) :=
    Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hB.aestronglyMeasurable.norm
  have hfn : eLpNorm f ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) =
      eLpNorm B ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) := by
    apply eLpNorm_congr_norm_ae hfm hB.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by simp [f, Complex.norm_real])
  have hf : MemLp f ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) := by
    change eLpNorm f _ _ < ∞
    rw [hfn]
    exact hB
  obtain ⟨hI, hF, hFn⟩ := hH f hf
  have hRealI : ∀ᵐ x ∂(volume : Measure V12Spatial),
      Integrable (fun y => ‖B y‖ / ‖x-y‖) (volume : Measure V12Spatial) := by
    filter_upwards [hI] with x hx
    simpa only [f, norm_div, Complex.norm_real, norm_norm] using hx.norm
  have hA : AEStronglyMeasurable (v12_rawHodgePotential B) (volume : Measure V12Spatial) :=
    hB.aestronglyMeasurable.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
      v12_hodgeKernel_measurable.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂(volume : Measure V12Spatial),
      ‖v12_rawHodgePotential B x‖ ≤ (2 * Real.pi)⁻¹ * ‖v12_fractionalPotential 1 f x‖ := by
    filter_upwards [hRealI] with x hx
    have hh := (v12_hodge_integrable_fractional_bound B hB.aestronglyMeasurable x hx).2
    rwa [v12_positiveFractionalPotential_eq_complex_norm B x hx] at hh
  have hnorm : eLpNorm (v12_rawHodgePotential B) 4 (volume : Measure V12Spatial) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * C) *
        eLpNorm B ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) := by
    have hm := eLpNorm_mono_ae_real (p := 4) hA hbound
    have he : eLpNorm (fun x => (2 * Real.pi)⁻¹ * ‖v12_fractionalPotential 1 f x‖)
        4 (volume : Measure V12Spatial) =
        ENNReal.ofReal ((2 * Real.pi)⁻¹) * eLpNorm (v12_fractionalPotential 1 f) 4 volume := by
      change eLpNorm ((2 * Real.pi)⁻¹ • (fun x => ‖v12_fractionalPotential 1 f x‖)) 4 volume = _
      rw [eLpNorm_const_smul, eLpNorm_norm _ hF.aestronglyMeasurable,
        ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    rw [he] at hm
    apply hm.trans
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal ((2 * Real.pi)⁻¹))) hFn
    simpa only [hfn, ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹), mul_assoc] using hh
  refine ⟨?_, ?_, hnorm⟩
  · filter_upwards [hRealI] with x hx
    exact (v12_hodge_integrable_fractional_bound B hB.aestronglyMeasurable x hx).1
  · apply hnorm.trans_lt
    finiteness [hB.eLpNorm_ne_top]

#print axioms v12_actual_hodge_HLS
end SMScattering.W20Full
