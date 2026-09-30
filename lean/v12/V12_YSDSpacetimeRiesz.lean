import lean.v12.V12_YQRFubiniSurjective
import lean.v12.V12_YSCoulombRieszTimeOperator

/-! The actual joint spacetime Riesz operator, transported through the
constructed L2 Fubini equivalence. Its sections are the original spatial
Fourier multiplier, and its weak continuity uses the same spacetime input. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

noncomputable def v12_spacetimeCoulombRieszOperator (μ : Measure ℝ) [SFinite μ]
    (j l : Fin 2) : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)) →L[ℂ]
      Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)) :=
  (v12_fubiniL2Equiv μ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((v12_timeCoulombRieszOperator μ j l).comp
      (v12_fubiniL2Equiv μ).toContinuousLinearEquiv.toContinuousLinearMap)

theorem v12_spacetimeCoulombRieszOperator_bound (μ : Measure ℝ) [SFinite μ]
    (j l : Fin 2) (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) :
    ‖v12_spacetimeCoulombRieszOperator μ j l f‖ ≤ ‖f‖ := by
  change ‖(v12_fubiniL2Equiv μ).symm
    (v12_timeCoulombRieszOperator μ j l (v12_fubiniL2Equiv μ f))‖ ≤ ‖f‖
  rw [(v12_fubiniL2Equiv μ).symm.norm_map]
  exact ((v12_timeCoulombRieszOperator μ j l).le_opNorm _).trans
    (by simpa only [one_mul, (v12_fubiniL2Equiv μ).norm_map] using
      mul_le_mul_of_nonneg_right (v12_timeCoulombRieszOperator_bound μ j l)
        (norm_nonneg (v12_fubiniL2Equiv μ f)))

theorem v12_spacetimeCoulombRieszOperator_sections (μ : Measure ℝ) [SFinite μ]
    (j l : Fin 2) (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial))) :
    ∀ᵐ t ∂μ, (fun x => v12_spacetimeCoulombRieszOperator μ j l f (t,x)) =ᵐ[volume]
      (v12_coulombRieszOperator j l (v12_fubiniMap μ f t) : V12Spatial → ℂ) := by
  have he : v12_fubiniMap μ (v12_spacetimeCoulombRieszOperator μ j l f) =
      v12_timeCoulombRieszOperator μ j l (v12_fubiniMap μ f) := by
    change v12_fubiniL2Equiv μ ((v12_fubiniL2Equiv μ).symm _) = _
    exact (v12_fubiniL2Equiv μ).apply_symm_apply _
  filter_upwards [v12_fubiniMap_sections μ (v12_spacetimeCoulombRieszOperator μ j l f),
    v12_timeCoulombRieszOperator_ae μ j l (v12_fubiniMap μ f)] with t ht hrt
  rw [he, hrt] at ht
  exact ht.symm

theorem v12_spacetimeCoulombRieszOperator_weak_limit (μ : Measure ℝ) [SFinite μ]
    (j l : Fin 2) (fn : ℕ → Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)))
    (f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)))
    (hw : ∀ φ : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)) →L[ℂ] ℂ,
      Tendsto (fun n => φ (fn n)) atTop (𝓝 (φ f))) :
    ∀ φ : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)) →L[ℂ] ℂ,
      Tendsto (fun n => φ (v12_spacetimeCoulombRieszOperator μ j l (fn n))) atTop
        (𝓝 (φ (v12_spacetimeCoulombRieszOperator μ j l f))) := by
  intro φ
  exact hw (φ.comp (v12_spacetimeCoulombRieszOperator μ j l))

#print axioms v12_spacetimeCoulombRieszOperator_bound
#print axioms v12_spacetimeCoulombRieszOperator_sections
#print axioms v12_spacetimeCoulombRieszOperator_weak_limit
end SMScattering.W20Full
