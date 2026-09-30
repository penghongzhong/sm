import lean.v12.V12_YZZGLocalSmoothIntegration

/-! Original first-order compatibility equations to compact test identities.
This is the common IBP step for torsion, divergence and curvature. Original
pointwise equations and local smoothness are the inputs; integrability and the
integral identity itself are proved. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_first_order_compact_constraint
    (a b : ℝ) (f g r ψ : V12Spacetime → ℂ) (c : ℂ) (v w : V12Spacetime)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Prod.fst ⁻¹' Set.Ioo a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b)
    (hEq : ∀ᵐ z ∂v12_slab_measure a b, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ f z v + c * fderiv ℝ g z w = r z) :
    Integrable (fun z => r z * ψ z) (v12_slab_measure a b) ∧
    -(∫ z, f z * fderiv ℝ ψ z v ∂v12_slab_measure a b) -
      c * (∫ z, g z * fderiv ℝ ψ z w ∂v12_slab_measure a b) =
      ∫ z, r z * ψ z ∂v12_slab_measure a b := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  let μ := v12_slab_measure a b
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hdf : ContinuousOn (fun z => fderiv ℝ f z v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hdg : ContinuousOn (fun z => fderiv ℝ g z w) U :=
    (hg.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hiF : Integrable (fun z => fderiv ℝ f z v * ψ z) μ :=
    v12_local_smooth_compact_product_integrable U hU _ ψ hdf hψ.continuous hc hs
  have hiG : Integrable (fun z => fderiv ℝ g z w * ψ z) μ :=
    v12_local_smooth_compact_product_integrable U hU _ ψ hdg hψ.continuous hc hs
  have hAE : (fun z => (fderiv ℝ f z v + c * fderiv ℝ g z w) * ψ z) =ᵐ[μ]
      (fun z => r z * ψ z) := by
    filter_upwards [hEq] with z hzEq
    by_cases hz : z ∈ U
    · rw [hzEq hz]
    · have hzero : ψ z = 0 := by
        by_contra hne
        exact hz (hs (subset_tsupport ψ hne))
      rw [hzero, mul_zero, mul_zero]
  have hi : Integrable (fun z => (fderiv ℝ f z v + c * fderiv ℝ g z w) * ψ z) μ := by
    simpa only [add_mul, mul_assoc] using hiF.add (hiG.const_mul c)
  refine ⟨hi.congr hAE, ?_⟩
  have he := integral_congr_ae hAE
  simp only [add_mul, mul_assoc] at he
  rw [integral_add hiF (hiG.const_mul c), integral_const_mul] at he
  have hfI := v12_original_slab_compact_IBP a b f ψ hf hψ hc hs v
  have hgI := v12_original_slab_compact_IBP a b g ψ hg hψ hc hs w
  have hdfI : (∫ z, fderiv ℝ f z v * ψ z ∂μ) =
      -(∫ z, f z * fderiv ℝ ψ z v ∂μ) := by rw [hfI, neg_neg]
  have hdgI : (∫ z, fderiv ℝ g z w * ψ z ∂μ) =
      -(∫ z, g z * fderiv ℝ ψ z w ∂μ) := by rw [hgI, neg_neg]
  rw [hdfI, hdgI, mul_neg, ← sub_eq_add_neg] at he
  exact he

#print axioms v12_original_first_order_compact_constraint
end SMScattering.W20Full
