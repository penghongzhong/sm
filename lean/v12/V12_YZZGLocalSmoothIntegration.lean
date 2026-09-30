import lean.v12.V12_YZZCCompactDistributionTests
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Group.Prod

/-! Compact-test integration by parts requires smoothness only on the
open original time domain containing the test support. Integrability of
all weighted derivatives is proved, not supplied as an internal interface. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_local_smooth_compact_product_integrable
    {μ : Measure V12Spacetime} [IsFiniteMeasureOnCompacts μ]
    (U : Set V12Spacetime) (hU : IsOpen U)
    (f ψ : V12Spacetime → ℂ) (hf : ContinuousOn f U) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    Integrable (fun z => f z * ψ z) μ := by
  have hcont : Continuous (fun z => f z * ψ z) :=
    (hf.mul hψ.continuousOn).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_right.trans hs)
  exact hcont.integrable_of_hasCompactSupport hc.mul_left

theorem v12_local_smooth_compact_IBP
    (U : Set V12Spacetime) (hU : IsOpen U)
    (f ψ : V12Spacetime → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) (v : V12Spacetime) :
    (∫ z, f z * fderiv ℝ ψ z v) = -(∫ z, fderiv ℝ f z v * ψ z) := by
  letI : IsAddHaarMeasure (volume : Measure V12Spacetime) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure V12Spatial)
  have hdf : ContinuousOn (fun z => fderiv ℝ f z v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  obtain ⟨hcd, hψd⟩ := v12_compact_spacetime_test_derivative ψ hψ hc v
  have hds : tsupport (fun z => fderiv ℝ ψ z v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hs
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact v12_local_smooth_compact_product_integrable U hU _ ψ hdf hψ.continuous hc hs
  · exact v12_local_smooth_compact_product_integrable U hU f _ hf.continuousOn
      hψd.continuous hcd hds
  · exact v12_local_smooth_compact_product_integrable U hU f ψ hf.continuousOn hψ.continuous hc hs
  · intro z hz
    exact (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hs hz))
  · intro z hz
    exact (hψ.differentiable (by simp)).differentiableAt

theorem v12_slab_compact_integral_eq_full
    (a b : ℝ) (g : V12Spacetime → ℂ)
    (hg : ∀ z, z.1 ∉ Set.Icc a b → g z = 0) :
    (∫ z, g z ∂v12_slab_measure a b) = ∫ z, g z := by
  change (∫ z, g z ∂((volume : Measure ℝ).restrict (Set.Icc a b)).prod
    (volume : Measure V12Spatial)) = _
  rw [Measure.restrict_prod_eq_prod_univ]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  apply hg z
  simpa only [Set.mem_prod, Set.mem_univ, and_true] using hz

theorem v12_original_slab_compact_IBP
    (a b : ℝ) (f ψ : V12Spacetime → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b)
    (v : V12Spacetime) :
    (∫ z, f z * fderiv ℝ ψ z v ∂v12_slab_measure a b) =
      -(∫ z, fderiv ℝ f z v * ψ z ∂v12_slab_measure a b) := by
  have hzero (z : V12Spacetime) (hz : z.1 ∉ Set.Icc a b) : z ∉ tsupport ψ := by
    intro hmem
    exact hz (Set.Ioo_subset_Icc_self (hs hmem))
  rw [v12_slab_compact_integral_eq_full a b _ (by
    intro z hz
    rw [fderiv_of_notMem_tsupport ℝ (hzero z hz)]
    simp), v12_slab_compact_integral_eq_full a b _ (by
    intro z hz
    have hψz : ψ z = 0 := by
      by_contra hh
      exact hzero z hz (subset_tsupport ψ hh)
    rw [hψz, mul_zero])]
  exact v12_local_smooth_compact_IBP _ (isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))) f ψ hf hψ hc hs v

theorem v12_original_slab_compact_second_IBP
    (a b : ℝ) (f ψ : V12Spacetime → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b)
    (v w : V12Spacetime) :
    (∫ z, fderiv ℝ (fun y => fderiv ℝ f y v) z w * ψ z ∂v12_slab_measure a b) =
    ∫ z, f z * fderiv ℝ (fun y => fderiv ℝ ψ y w) z v ∂v12_slab_measure a b := by
  have hU : IsOpen (Prod.fst ⁻¹' Set.Ioo a b) := isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hdf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ f z v)
      (Prod.fst ⁻¹' Set.Ioo a b) :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  obtain ⟨hcd, hdψ⟩ := v12_compact_spacetime_test_derivative ψ hψ hc w
  have hds := (tsupport_fderiv_apply_subset ℝ w (f := ψ)).trans hs
  have hfirst := v12_original_slab_compact_IBP a b _ ψ hdf hψ hc hs w
  have hsecond := v12_original_slab_compact_IBP a b f _ hf hdψ hcd hds v
  rw [hfirst, neg_neg] at hsecond
  exact hsecond.symm

#print axioms v12_local_smooth_compact_product_integrable
#print axioms v12_local_smooth_compact_IBP
#print axioms v12_original_slab_compact_IBP
#print axioms v12_original_slab_compact_second_IBP
end SMScattering.W20Full
