import lean.v12.V12_YZZGWOriginalWeightedTimeSource
import lean.v12.V12_ZDETimeResidualUniqueness

/-! Actual source identification from the original weak PDE. Neither a residual
identity nor a time-source identity is assumed. Local integrability of f and
A f must be instantiated from the original MZ estimates downstream; this
internal scalar lemma alone does not certify Theorem 7.2. Pending actual CI. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_PDE_time_source_ae
    (a b : ℝ) (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g : V12Spacetime → ℂ) (ψ : V12Spatial → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hA : ∀ j, LocallyIntegrable (A j) (v12_slab_measure a b))
    (hg : MemLp g ((4 : ℝ≥0∞)/3) (v12_slab_measure a b))
    (hfL : LocallyIntegrable f (v12_slab_measure a b))
    (hAfL : ∀ j, LocallyIntegrable (fun z => A j z * f z) (v12_slab_measure a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hdiv : ∀ φ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, A 0 z * fderiv ℝ φ z (v12_spatialDirection 0) ∂v12_slab_measure a b) +
      (∫ z, A 1 z * fderiv ℝ φ z (v12_spatialDirection 1) ∂v12_slab_measure a b) = 0)
    (hPDE : V12OriginalScalarDistributionalPDE a b f A g
      v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1)) :
    (fun t => ∫ x : V12Spatial, fderiv ℝ f (t,x) v12_timeDirection * ψ x)
      =ᵐ[(volume : Measure ℝ).restrict (Set.Icc a b)]
        v12_scalarSpatialTestSource f A g ψ := by
  have hp : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).mpr
    norm_num
  have hG := v12_scalarSpatialTestSource_integrable a b f A g ψ
    hfL hAfL (hg.locallyIntegrable hp) hψ hcψ
  apply v12_time_source_eq_of_compact_residual_tests a b _ _
    (v12_time_derivative_pairing_continuousOn a b f ψ hf hψ.continuous hcψ) hG
  intro η hη hcη hsη
  let ηC : ℝ → ℂ := Complex.ofRealCLM ∘ η
  have hηC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ηC := by
    dsimp [ηC]
    fun_prop
  have hcηC : HasCompactSupport ηC := hcη.comp_left rfl
  have hsηC : tsupport ηC ⊆ Set.Ioo a b := by
    apply Set.Subset.trans _ hsη
    apply closure_mono
    intro t ht
    change η t ≠ 0
    intro he
    exact ht (by simp [ηC, he])
  have hT := v12_original_PDE_weighted_time_source a b f A g ηC ψ
    hf hA hg hηC hcηC hsηC hψ hcψ hdiv hPDE
  have hGη : Integrable (fun t => ηC t * v12_scalarSpatialTestSource f A g ψ t)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
    simpa only [smul_eq_mul] using
      hG.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hηC.continuous hcηC
  have he : (∫ t, ηC t * ((∫ x : V12Spatial,
        fderiv ℝ f (t,x) v12_timeDirection * ψ x) -
        v12_scalarSpatialTestSource f A g ψ t)
      ∂(volume : Measure ℝ).restrict (Set.Icc a b)) = 0 := by
    simp only [mul_sub]
    rw [integral_sub hT.1 hGη]
    exact sub_eq_zero.mpr hT.2
  simpa only [ηC, Function.comp_apply, Complex.ofRealCLM_apply, Complex.real_smul] using he

#print axioms v12_original_PDE_time_source_ae
end SMScattering.W20Full
