import lean.v12.V12_YZZGLocalSmoothIntegration
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Original scalar Coulomb equation to a concrete compact-test identity.
The drift divergence is proved by the product rule and div A=0. Weighted
integrability and every integration-by-parts step are discharged internally. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_spacetime_scalar_Coulomb_product_rule
    (A : Fin 2 → V12Spacetime → ℂ) (f : V12Spacetime → ℂ)
    (z e₀ e₁ : V12Spacetime)
    (hA : ∀ j, DifferentiableAt ℝ (A j) z) (hf : DifferentiableAt ℝ f z)
    (hdiv : fderiv ℝ (A 0) z e₀ + fderiv ℝ (A 1) z e₁ = 0) :
    fderiv ℝ (fun x => A 0 x * f x) z e₀ +
      fderiv ℝ (fun x => A 1 x * f x) z e₁ =
      A 0 z * fderiv ℝ f z e₀ + A 1 z * fderiv ℝ f z e₁ := by
  rw [fderiv_fun_mul (hA 0) hf, fderiv_fun_mul (hA 1) hf]
  change A 0 z * fderiv ℝ f z e₀ + f z * fderiv ℝ (A 0) z e₀ +
    (A 1 z * fderiv ℝ f z e₁ + f z * fderiv ℝ (A 1) z e₁) = _
  calc
    _ = A 0 z * fderiv ℝ f z e₀ + A 1 z * fderiv ℝ f z e₁ +
      f z * (fderiv ℝ (A 0) z e₀ + fderiv ℝ (A 1) z e₁) := by ring
    _ = _ := by rw [hdiv, mul_zero, add_zero]

theorem v12_original_scalar_compact_PDE
    (a b : ℝ) (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g ψ : V12Spacetime → ℂ) (vt e₀ e₁ : V12Spacetime)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hA : ∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A j) (Prod.fst ⁻¹' Set.Ioo a b))
    (hg : ContinuousOn g (Prod.fst ⁻¹' Set.Ioo a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b)
    (hdiv : ∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (A 0) z e₀ + fderiv ℝ (A 1) z e₁ = 0)
    (hPDE : ∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      Complex.I * fderiv ℝ f z vt +
      (fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ +
       fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁) =
      (2 * Complex.I) * (A 0 z * fderiv ℝ f z e₀ + A 1 z * fderiv ℝ f z e₁) + g z) :
    -Complex.I * (∫ z, f z * fderiv ℝ ψ z vt ∂v12_slab_measure a b) +
      ((∫ z, f z * fderiv ℝ (fun x => fderiv ℝ ψ x e₀) z e₀ ∂v12_slab_measure a b) +
       (∫ z, f z * fderiv ℝ (fun x => fderiv ℝ ψ x e₁) z e₁ ∂v12_slab_measure a b)) =
    -(2 * Complex.I) *
      ((∫ z, (A 0 z * f z) * fderiv ℝ ψ z e₀ ∂v12_slab_measure a b) +
       (∫ z, (A 1 z * f z) * fderiv ℝ ψ z e₁ ∂v12_slab_measure a b)) +
      ∫ z, g z * ψ z ∂v12_slab_measure a b := by
  let U := Prod.fst ⁻¹' Set.Ioo a b
  let μ := v12_slab_measure a b
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
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
  have hint (r : V12Spacetime → ℂ) (hr : ContinuousOn r U) :
      Integrable (fun z => r z * ψ z) μ :=
    v12_local_smooth_compact_product_integrable U hU r ψ hr hψ.continuous hc hs
  have hit := hint _ (hdf vt).continuousOn
  have hi₀ := hint _ (hddf e₀)
  have hi₁ := hint _ (hddf e₁)
  have hp₀ := hint _ (hdp 0 e₀)
  have hp₁ := hint _ (hdp 1 e₁)
  have hig := hint g hg
  have he : (∫ z, (Complex.I * fderiv ℝ f z vt +
      (fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ +
       fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁)) * ψ z ∂μ) =
      ∫ z, ((2 * Complex.I) *
        (fderiv ℝ (fun x => A 0 x * f x) z e₀ +
         fderiv ℝ (fun x => A 1 x * f x) z e₁) + g z) * ψ z ∂μ := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ U
    · rw [v12_spacetime_scalar_Coulomb_product_rule A f z e₀ e₁
        (fun j => ((hA j).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz))
        ((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)) (hdiv z hz)]
      rw [hPDE z hz]
    · have hzero : ψ z = 0 := by
        by_contra hne
        exact hz (hs (subset_tsupport ψ hne))
      rw [hzero, mul_zero, mul_zero]
  simp only [add_mul, mul_assoc] at he
  rw [integral_add (hit.const_mul _) (hi₀.add hi₁), integral_add hi₀ hi₁,
    integral_const_mul, integral_add ((hp₀.add hp₁).const_mul _) hig,
    integral_const_mul, integral_add hp₀ hp₁] at he
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
  rw [hdt, h₀, h₁, hdp0, hdp1] at he
  simpa only [mul_neg, neg_mul, ← neg_add] using he

#print axioms v12_spacetime_scalar_Coulomb_product_rule
#print axioms v12_original_scalar_compact_PDE
end SMScattering.W20Full
