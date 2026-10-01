import lean.v12.V12_YZZGLocalSmoothIntegration
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A continuous residual on the original open time slab vanishes pointwise
if its compact test integrals vanish. Local integrability and the passage
from slab integrals to full-space integrals are proved here. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_continuous_slab_residual_eq_zero
    (a b : ℝ) (f : V12Spacetime → ℂ)
    (hf : ContinuousOn f (Prod.fst ⁻¹' Set.Ioo a b))
    (hTest : ∀ ψ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, f z * ψ z ∂v12_slab_measure a b) = 0) :
    ∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b → f z = 0 := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  letI : Measure.IsAddHaarMeasure (volume : Measure V12Spacetime) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure V12Spatial)
  have hloc : LocallyIntegrableOn f U (volume : Measure V12Spacetime) :=
    hf.locallyIntegrableOn hU.measurableSet
  have hae : ∀ᵐ z ∂(volume : Measure V12Spacetime), z ∈ U → f z = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro φ hφ hc hs
    let ψ : V12Spacetime → ℂ := Complex.ofRealCLM ∘ φ
    have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
      dsimp [ψ]
      fun_prop
    have hcψ : HasCompactSupport ψ := hc.comp_left rfl
    have hsψ : tsupport ψ ⊆ U := by
      apply Set.Subset.trans _ hs
      apply closure_mono
      intro z hz
      change φ z ≠ 0
      intro he
      exact hz (by simp [ψ, he])
    have he := hTest ψ hψ hcψ hsψ
    rw [v12_slab_compact_integral_eq_full a b _ (by
      intro z hz
      have hzero : ψ z = 0 := by
        by_contra hne
        exact hz (Set.Ioo_subset_Icc_self (hsψ (subset_tsupport ψ hne)))
      rw [hzero, mul_zero])] at he
    simpa only [ψ, Function.comp_apply, Complex.ofRealCLM_apply,
      Complex.real_smul, mul_comm] using he
  have haeU : f =ᵐ[(volume : Measure V12Spacetime).restrict U] (fun _ => (0 : ℂ)) :=
    (ae_restrict_iff' hU.measurableSet).mpr hae
  exact Measure.eqOn_open_of_ae_eq haeU hU hf continuousOn_const

#print axioms v12_continuous_slab_residual_eq_zero
end SMScattering.W20Full
