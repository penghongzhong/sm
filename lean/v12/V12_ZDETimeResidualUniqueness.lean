import lean.v12.V12_ZDDOpenDerivativeTimeIdentity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Interior distributional uniqueness identifies an actual integrable time
source on the closed slab, including the measure-zero endpoints. The compact
residual test identity must still be obtained by testing the original PDE;
it is not an allowed assumption of the manuscript's compactness theorem. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
open scoped Topology

theorem v12_time_source_eq_of_compact_residual_tests
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a b : ℝ) (D G : ℝ → E)
    (hD : ContinuousOn D (Set.Ioo a b))
    (hG : IntegrableOn G (Set.Icc a b) volume)
    (hTest : ∀ η : ℝ → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b →
      (∫ t, η t • (D t-G t) ∂(volume : Measure ℝ).restrict (Set.Icc a b)) = 0) :
    D =ᵐ[(volume : Measure ℝ).restrict (Set.Icc a b)] G := by
  have hloc : LocallyIntegrableOn (fun t => D t-G t) (Set.Ioo a b) volume :=
    (hD.locallyIntegrableOn measurableSet_Ioo).sub
      ((hG.mono_set Set.Ioo_subset_Icc_self).locallyIntegrableOn)
  have hz : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo a b → D t-G t=0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro η hη hc hs
    have he := hTest η hη hc hs
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro t ht
      have hzero : η t=0 := by
        by_contra hn
        exact ht (Set.Ioo_subset_Icc_self (hs (subset_tsupport η hn)))
      rw [hzero, zero_smul])] at he
    exact he
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hz] with t ht
  intro htab
  exact sub_eq_zero.mp (ht htab)

#print axioms v12_time_source_eq_of_compact_residual_tests
end SMScattering.W20Full
