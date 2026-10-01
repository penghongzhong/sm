import lean.v12.V12_YZZSCanonicalClosureStatements
import lean.v12.V12_YWSmoothSlabExtension

/-! Closed-slab zero extension preserves the ORIGINAL distributional div,
curl and torsion constraints. Only same-field value/Hodge equality is used;
no smooth connection or additional compact identity is assumed. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_spatial_constraints_extension
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hCompat : V12CanonicalSpatialDistributionalConstraints a b q) :
    V12CanonicalSpatialDistributionalConstraints a b (v12_smoothSlabExtension a b q) := by
  let ext := v12_smoothSlabExtension a b q
  let μ := v12_slab_measure a b
  have he : ext =ᵐ[μ] q := v12_smoothSlabExtension_ae a b q
  have hA (j : Fin 2) : v12_actualCoulombA ext j =ᵐ[μ] v12_actualCoulombA q j := by
    filter_upwards [v12_smoothSlabExtension_Hodge_ae a b q] with z hz
    simp only [v12_actualCoulombA, ext, hz]
  have hQI (j : Fin 2) (ψ : V12Spacetime → ℂ) :
      (∫ z, ext z j * ψ z ∂μ) = ∫ z, q z j * ψ z ∂μ := by
    apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  have hAI (j : Fin 2) (ψ : V12Spacetime → ℂ) :
      (∫ z, v12_actualCoulombA ext j z * ψ z ∂μ) =
      ∫ z, v12_actualCoulombA q j z * ψ z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hA j] with z hz
    rw [hz]
  have hBI (ψ : V12Spacetime → ℂ) :
      (∫ z, (v12_curvatureDensity (ext z) : ℂ) * ψ z ∂μ) =
      ∫ z, (v12_curvatureDensity (q z) : ℂ) * ψ z ∂μ := by
    apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  have hAQI (k j : Fin 2) (ψ : V12Spacetime → ℂ) :
      (∫ z, (v12_actualCoulombA ext k z * ext z j) * ψ z ∂μ) =
      ∫ z, (v12_actualCoulombA q k z * q z j) * ψ z ∂μ := by
    apply integral_congr_ae
    filter_upwards [he, hA k] with z hqz haz
    rw [hqz, haz]
  dsimp only [ext, μ] at hQI hAI hBI hAQI
  intro ψ hψ hc hs
  simpa only [hQI, hAI, hBI, hAQI] using hCompat ψ hψ hc hs

#print axioms v12_original_spatial_constraints_extension
end SMScattering.W20Full
