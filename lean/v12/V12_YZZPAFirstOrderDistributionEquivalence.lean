import lean.v12.V12_YZZGMContinuousDistributionUniqueness
import lean.v12.V12_YZZOCompactFirstOrderConstraints

/-! The converse first-order IBP bridge: the manuscript's distributional
constraint for smooth fields implies its pointwise version. No pointwise
constraint or vanishing residual is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_first_order_pointwise_of_distributional
    (a b : ℝ) (f g r : V12Spacetime → ℂ) (c : ℂ) (v w : V12Spacetime)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (Prod.fst ⁻¹' Set.Ioo a b))
    (hr : ContinuousOn r (Prod.fst ⁻¹' Set.Ioo a b))
    (hTest : ∀ ψ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      -(∫ z, f z * fderiv ℝ ψ z v ∂v12_slab_measure a b) -
        c * (∫ z, g z * fderiv ℝ ψ z w ∂v12_slab_measure a b) =
        ∫ z, r z * ψ z ∂v12_slab_measure a b) :
    ∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ f z v + c * fderiv ℝ g z w = r z := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  let d := fun z => fderiv ℝ f z v + c * fderiv ℝ g z w
  have hd : ContinuousOn d U :=
    ((hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const).add
      (continuousOn_const.mul
        ((hg.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const))
  have hzero : ∀ z, z ∈ U → d z - r z = 0 := by
    apply v12_continuous_slab_residual_eq_zero a b (fun z => d z-r z) (hd.sub hr)
    intro ψ hψ hc hs
    have hI := v12_original_first_order_compact_constraint a b f g d ψ c v w
      hf hg hψ hc hs (Filter.Eventually.of_forall (fun _ _ => rfl))
    have hir : Integrable (fun z => r z * ψ z) (v12_slab_measure a b) :=
      v12_local_smooth_compact_product_integrable U hU r ψ hr hψ.continuous hc hs
    calc
      (∫ z, (d z-r z)*ψ z ∂v12_slab_measure a b) =
          (∫ z, d z*ψ z ∂v12_slab_measure a b) -
          (∫ z, r z*ψ z ∂v12_slab_measure a b) := by
        simp only [sub_mul]
        exact integral_sub hI.1 hir
      _ = 0 := by rw [← hI.2, hTest ψ hψ hc hs, sub_self]
  intro z hz
  exact sub_eq_zero.mp (hzero z hz)

#print axioms v12_first_order_pointwise_of_distributional
end SMScattering.W20Full
