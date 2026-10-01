import lean.v12.V12_YZZGNCompactProductTests

/-! Distributional div A = 0 removes the advective derivative using f ψ as
a genuine compact test. Only local integrability of A is needed; no
space-time derivative of A is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_locally_integrable_weighted_compact_product
    (μ : Measure V12Spacetime) (U : Set V12Spacetime) (hU : IsOpen U)
    (A f ψ : V12Spacetime → ℂ) (hA : LocallyIntegrable A μ)
    (hf : ContinuousOn f U) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun z => A z * (f z * ψ z)) μ := by
  have hcont : Continuous (fun z => f z * ψ z) :=
    (hf.mul hψ.continuousOn).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_right.trans hs)
  have h := hA.integrable_smul_right_of_hasCompactSupport hcont hc.mul_left
  simpa only [smul_eq_mul] using h

theorem v12_distributional_divergence_product
    (a b : ℝ) (A : Fin 2 → V12Spacetime → ℂ)
    (f ψ : V12Spacetime → ℂ) (e₀ e₁ : V12Spacetime)
    (hA : ∀ j, LocallyIntegrable (A j) (v12_slab_measure a b))
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b)
    (hdiv : ∀ φ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, A 0 z * fderiv ℝ φ z e₀ ∂v12_slab_measure a b) +
      (∫ z, A 1 z * fderiv ℝ φ z e₁ ∂v12_slab_measure a b) = 0) :
    (∫ z, A 0 z * (fderiv ℝ f z e₀ * ψ z) ∂v12_slab_measure a b) +
      (∫ z, A 1 z * (fderiv ℝ f z e₁ * ψ z) ∂v12_slab_measure a b) =
    -((∫ z, A 0 z * (f z * fderiv ℝ ψ z e₀) ∂v12_slab_measure a b) +
      (∫ z, A 1 z * (f z * fderiv ℝ ψ z e₁) ∂v12_slab_measure a b)) := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  let μ := v12_slab_measure a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  obtain ⟨hp, hpc, hps⟩ := v12_local_smooth_mul_compact_test U hU f ψ hf hψ hc hs
  have hi (j : Fin 2) (v : V12Spacetime) :
      Integrable (fun z => A j z * (fderiv ℝ f z v * ψ z)) μ :=
    v12_locally_integrable_weighted_compact_product μ U hU (A j) _ ψ (hA j)
      ((hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const)
      hψ.continuous hc hs
  have hi' (j : Fin 2) (v : V12Spacetime) :
      Integrable (fun z => A j z * (f z * fderiv ℝ ψ z v)) μ := by
    obtain ⟨hcv, hsv⟩ := v12_compact_spacetime_test_derivative ψ hψ hc v
    exact v12_locally_integrable_weighted_compact_product μ U hU (A j) f _ (hA j)
      hf.continuousOn hsv.continuous hcv ((tsupport_fderiv_apply_subset ℝ v).trans hs)
  have he (j : Fin 2) (v : V12Spacetime) :
      (∫ z, A j z * fderiv ℝ (fun y => f y * ψ y) z v ∂μ) =
      (∫ z, A j z * (fderiv ℝ f z v * ψ z) ∂μ) +
      (∫ z, A j z * (f z * fderiv ℝ ψ z v) ∂μ) := by
    calc
      _ = (∫ z, A j z * (fderiv ℝ f z v * ψ z) +
          A j z * (f z * fderiv ℝ ψ z v) ∂μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by
          dsimp only
          rw [v12_local_smooth_compact_product_derivative U hU f ψ hf hψ hs z v]
          ring)
      _ = _ := integral_add (hi j v) (hi' j v)
  have h := hdiv (fun z => f z * ψ z) hp hpc hps
  rw [he 0 e₀, he 1 e₁] at h
  linear_combination h

#print axioms v12_distributional_divergence_product
end SMScattering.W20Full
