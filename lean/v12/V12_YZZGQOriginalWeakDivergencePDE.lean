import lean.v12.V12_YZZGPWeakDivergenceProduct

/-! Original pointwise scalar PDE to concrete compact identities using only
original distributional div A and local integrability of A. Joint smoothness
of the connection is not required. All weighted integrability is proved. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_scalar_compact_PDE_weak_divergence
    (a b : ℝ) (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g ψ : V12Spacetime → ℂ) (vt e₀ e₁ : V12Spacetime)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hA : ∀ j, LocallyIntegrable (A j) (v12_slab_measure a b))
    (hg : MemLp g ((4 : ℝ≥0∞)/3) (v12_slab_measure a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b)
    (hdiv : ∀ φ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, A 0 z * fderiv ℝ φ z e₀ ∂v12_slab_measure a b) +
      (∫ z, A 1 z * fderiv ℝ φ z e₁ ∂v12_slab_measure a b) = 0)
    (hPDE : ∀ᵐ z ∂v12_slab_measure a b, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
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
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  let μ := v12_slab_measure a b
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hdf (v : V12Spacetime) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ f z v) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hddf (v : V12Spacetime) : ContinuousOn
      (fun z => fderiv ℝ (fun x => fderiv ℝ f x v) z v) U :=
    ((hdf v).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hint (r : V12Spacetime → ℂ) (hr : ContinuousOn r U) :
      Integrable (fun z => r z * ψ z) μ :=
    v12_local_smooth_compact_product_integrable U hU r ψ hr hψ.continuous hc hs
  have hit := hint _ (hdf vt).continuousOn
  have hi₀ := hint _ (hddf e₀)
  have hi₁ := hint _ (hddf e₁)
  have hip (j : Fin 2) (v : V12Spacetime) :
      Integrable (fun z => (A j z * fderiv ℝ f z v) * ψ z) μ := by
    have h := v12_locally_integrable_weighted_compact_product μ U hU (A j) _ ψ
      (hA j) (hdf v).continuousOn hψ.continuous hc hs
    simpa only [mul_assoc] using h
  have hp₀ := hip 0 e₀
  have hp₁ := hip 1 e₁
  have hig : Integrable (fun z => g z * ψ z) μ := by
    have hp : (1 : ℝ≥0∞) ≤ 4 / 3 := by
      apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).mpr
      norm_num
    have h := (hg.locallyIntegrable hp).integrable_smul_right_of_hasCompactSupport
      hψ.continuous hc
    simpa only [smul_eq_mul] using h
  have he : (∫ z, (Complex.I * fderiv ℝ f z vt +
      (fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ +
       fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁)) * ψ z ∂μ) =
      ∫ z, ((2 * Complex.I) *
        ((A 0 z * fderiv ℝ f z e₀) +
         (A 1 z * fderiv ℝ f z e₁)) + g z) * ψ z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hPDE] with z hzPDE
    by_cases hz : z ∈ U
    · rw [hzPDE hz]
    · have hzero : ψ z = 0 := by
        by_contra hne
        exact hz (hs (subset_tsupport ψ hne))
      rw [hzero, mul_zero, mul_zero]
  have he' :
      (∫ z, Complex.I * (fderiv ℝ f z vt * ψ z) +
        (fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ * ψ z +
         fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁ * ψ z) ∂μ) =
      ∫ z, (2 * Complex.I) *
        ((A 0 z * fderiv ℝ f z e₀) * ψ z +
         (A 1 z * fderiv ℝ f z e₁) * ψ z) + g z * ψ z ∂μ := by
    calc
      _ = (∫ z, (Complex.I * fderiv ℝ f z vt +
          (fderiv ℝ (fun x => fderiv ℝ f x e₀) z e₀ +
           fderiv ℝ (fun x => fderiv ℝ f x e₁) z e₁)) * ψ z ∂μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by ring)
      _ = (∫ z, ((2 * Complex.I) *
          ((A 0 z * fderiv ℝ f z e₀) +
           (A 1 z * fderiv ℝ f z e₁)) + g z) * ψ z ∂μ) := he
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by ring)
  have hsleft := integral_add (hit.const_mul Complex.I) (hi₀.add hi₁)
  have hslap := integral_add hi₀ hi₁
  have hsright := integral_add ((hp₀.add hp₁).const_mul (2 * Complex.I)) hig
  have hsdrift := integral_add hp₀ hp₁
  simp only [Pi.add_apply] at hsleft hslap hsright hsdrift
  rw [hsleft, hslap, integral_const_mul, hsright, integral_const_mul, hsdrift] at he'
  have ht := v12_original_slab_compact_IBP a b f ψ hf hψ hc hs vt
  have h₀ := v12_original_slab_compact_second_IBP a b f ψ hf hψ hc hs e₀ e₀
  have h₁ := v12_original_slab_compact_second_IBP a b f ψ hf hψ hc hs e₁ e₁
  have hdt : (∫ z, fderiv ℝ f z vt * ψ z ∂μ) =
      -(∫ z, f z * fderiv ℝ ψ z vt ∂μ) := by rw [ht, neg_neg]
  have hd := v12_distributional_divergence_product a b A f ψ e₀ e₁ hA hf hψ hc hs hdiv
  rw [hdt, h₀, h₁] at he'
  simp only [mul_assoc] at he'
  rw [hd] at he'
  simpa only [mul_neg, neg_mul, mul_assoc] using he'

#print axioms v12_original_scalar_compact_PDE_weak_divergence
end SMScattering.W20Full
