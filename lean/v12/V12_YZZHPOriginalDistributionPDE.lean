import lean.v12.V12_YZZGMContinuousDistributionUniqueness
import lean.v12.V12_YZZHOriginalCompactPDE

/-! Smooth distributional Coulomb PDE implies the pointwise PDE. Compact
product integrability, reverse integration by parts, and vanishing of the
continuous residual are proved rather than assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_scalar_PDE_pointwise_of_distributional
    (a b : ℝ) (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g : V12Spacetime → ℂ) (vt e₀ e₁ : V12Spacetime)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hA : ∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A j) (Prod.fst ⁻¹' Set.Ioo a b))
    (hg : ContinuousOn g (Prod.fst ⁻¹' Set.Ioo a b))
    (hdiv : ∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (A 0) z e₀ + fderiv ℝ (A 1) z e₁ = 0)
    (hTest : ∀ ψ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
    -Complex.I * (∫ z, f z * fderiv ℝ ψ z vt ∂v12_slab_measure a b) +
      ((∫ z, f z * fderiv ℝ (fun x => fderiv ℝ ψ x e₀) z e₀ ∂v12_slab_measure a b) +
       (∫ z, f z * fderiv ℝ (fun x => fderiv ℝ ψ x e₁) z e₁ ∂v12_slab_measure a b)) =
    -(2 * Complex.I) *
      ((∫ z, (A 0 z * f z) * fderiv ℝ ψ z e₀ ∂v12_slab_measure a b) +
       (∫ z, (A 1 z * f z) * fderiv ℝ ψ z e₁ ∂v12_slab_measure a b)) +
      ∫ z, g z * ψ z ∂v12_slab_measure a b) :
    ∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      Complex.I * fderiv ℝ f z vt +
      (fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ +
       fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁) =
      (2 * Complex.I) * (A 0 z * fderiv ℝ f z e₀ + A 1 z * fderiv ℝ f z e₁) + g z := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  let μ := v12_slab_measure a b
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hdf (v : V12Spacetime) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ f z v) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hddf (v : V12Spacetime) : ContinuousOn
      (fun z => fderiv ℝ (fun x => fderiv ℝ f x v) z v) U :=
    ((hdf v).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hprod (j : Fin 2) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => A j z * f z) U := (hA j).mul hf
  have hdp (j : Fin 2) (v : V12Spacetime) : ContinuousOn
      (fun z => fderiv ℝ (fun x => A j x * f x) z v) U :=
    ((hprod j).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  let r := fun z => Complex.I * fderiv ℝ f z vt +
    (fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ +
     fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁) -
    ((2 * Complex.I) * (fderiv ℝ (fun x => A 0 x * f x) z e₀ +
      fderiv ℝ (fun x => A 1 x * f x) z e₁) + g z)
  have hr : ContinuousOn r U :=
    ((continuousOn_const.mul (hdf vt).continuousOn).add ((hddf e₀).add (hddf e₁))).sub
      ((continuousOn_const.mul ((hdp 0 e₀).add (hdp 1 e₁))).add hg)
  have hzero : ∀ z, z ∈ U → r z = 0 := by
    apply v12_continuous_slab_residual_eq_zero a b r hr
    intro ψ hψ hc hs
    have hint (r : V12Spacetime → ℂ) (hr : ContinuousOn r U) :
        Integrable (fun z => r z * ψ z) μ :=
      v12_local_smooth_compact_product_integrable U hU r ψ hr hψ.continuous hc hs
    have hit := hint _ (hdf vt).continuousOn
    have hi₀ := hint _ (hddf e₀)
    have hi₁ := hint _ (hddf e₁)
    have hp₀ := hint _ (hdp 0 e₀)
    have hp₁ := hint _ (hdp 1 e₁)
    have hig := hint g hg
    have hsleft := integral_add (hit.const_mul Complex.I) (hi₀.add hi₁)
    have hslap := integral_add hi₀ hi₁
    have hsright := integral_add ((hp₀.add hp₁).const_mul (2 * Complex.I)) hig
    have hsdrift := integral_add hp₀ hp₁
    have hswhole := integral_sub ((hit.const_mul Complex.I).add (hi₀.add hi₁))
      (((hp₀.add hp₁).const_mul (2 * Complex.I)).add hig)
    simp only [Pi.add_apply] at hsleft hslap hsright hsdrift hswhole
    have he : (∫ z, r z * ψ z ∂μ) =
        (Complex.I * (∫ z, fderiv ℝ f z vt * ψ z ∂μ) +
          ((∫ z, fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ * ψ z ∂μ) +
           (∫ z, fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁ * ψ z ∂μ))) -
        ((2 * Complex.I) *
          ((∫ z, fderiv ℝ (fun x => A 0 x * f x) z e₀ * ψ z ∂μ) +
           (∫ z, fderiv ℝ (fun x => A 1 x * f x) z e₁ * ψ z ∂μ)) +
          (∫ z, g z * ψ z ∂μ)) := by
      calc
        _ = (∫ z, (Complex.I * (fderiv ℝ f z vt * ψ z) +
            (fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ * ψ z +
             fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁ * ψ z)) -
            ((2 * Complex.I) *
              (fderiv ℝ (fun x => A 0 x * f x) z e₀ * ψ z +
               fderiv ℝ (fun x => A 1 x * f x) z e₁ * ψ z) + g z * ψ z) ∂μ) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun z => by dsimp [r]; ring)
        _ = _ := by
          rw [hswhole, hsleft, hslap, integral_const_mul,
            hsright, integral_const_mul, hsdrift]
    have ht := v12_original_slab_compact_IBP a b f ψ hf hψ hc hs vt
    have h₀ := v12_original_slab_compact_second_IBP a b f ψ hf hψ hc hs e₀ e₀
    have h₁ := v12_original_slab_compact_second_IBP a b f ψ hf hψ hc hs e₁ e₁
    have hp0 := v12_original_slab_compact_IBP a b _ ψ (hprod 0) hψ hc hs e₀
    have hp1 := v12_original_slab_compact_IBP a b _ ψ (hprod 1) hψ hc hs e₁
    have hdt : (∫ z, fderiv ℝ f z vt * ψ z ∂μ) =
        -(∫ z, f z * fderiv ℝ ψ z vt ∂μ) := by rw [ht, neg_neg]
    have hdp0 : (∫ z, fderiv ℝ (fun x => A 0 x * f x) z e₀ * ψ z ∂μ) =
        -(∫ z, (A 0 z * f z) * fderiv ℝ ψ z e₀ ∂μ) := by rw [hp0, neg_neg]
    have hdp1 : (∫ z, fderiv ℝ (fun x => A 1 x * f x) z e₁ * ψ z ∂μ) =
        -(∫ z, (A 1 z * f z) * fderiv ℝ ψ z e₁ ∂μ) := by rw [hp1, neg_neg]
    rw [he, hdt, h₀, h₁, hdp0, hdp1]
    have htst := hTest ψ hψ hc hs
    linear_combination htst
  intro z hz
  have he := sub_eq_zero.mp (hzero z hz)
  dsimp [r] at he
  rw [v12_spacetime_scalar_Coulomb_product_rule A f z e₀ e₁
    (fun j => ((hA j).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz))
    ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)) (hdiv z hz)] at he
  exact he

#print axioms v12_scalar_PDE_pointwise_of_distributional
end SMScattering.W20Full
