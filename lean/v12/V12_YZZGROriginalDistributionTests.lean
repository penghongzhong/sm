import lean.v12.V12_YZZGQOriginalWeakDivergencePDE

/-! Literal compact-test meaning of the ORIGINAL distributional equation
(v12:eq:Q-system), with its advective A times gradient Q term. This is an
original compatibility hypothesis, not the internally derived divergence
identity. The theorem derives that identity by the proved product test.
No regularity of A beyond local integrability is imposed. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

def V12OriginalScalarDistributionalPDE
    (a b : ℝ) (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g : V12Spacetime → ℂ) (vt e₀ e₁ : V12Spacetime) : Prop :=
  ∀ ψ : V12Spacetime → ℂ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
    -Complex.I * (∫ z, f z * fderiv ℝ ψ z vt ∂v12_slab_measure a b) +
      ((∫ z, f z * fderiv ℝ (fun x => fderiv ℝ ψ x e₀) z e₀ ∂v12_slab_measure a b) +
       (∫ z, f z * fderiv ℝ (fun x => fderiv ℝ ψ x e₁) z e₁ ∂v12_slab_measure a b)) =
      ∫ z, ((2 * Complex.I) *
        (A 0 z * fderiv ℝ f z e₀ + A 1 z * fderiv ℝ f z e₁) + g z) * ψ z
          ∂v12_slab_measure a b

theorem v12_compact_PDE_from_original_distribution
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
    (hPDE : V12OriginalScalarDistributionalPDE a b f A g vt e₀ e₁) :
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
  have hsright := integral_add ((hp₀.add hp₁).const_mul (2 * Complex.I)) hig
  have hsdrift := integral_add hp₀ hp₁
  simp only [Pi.add_apply] at hsright hsdrift
  have hraw := hPDE ψ hψ hc hs
  have hnorm :
      (∫ z, ((2 * Complex.I) *
        (A 0 z * fderiv ℝ f z e₀ + A 1 z * fderiv ℝ f z e₁) + g z) * ψ z ∂μ) =
      (2 * Complex.I) *
        ((∫ z, (A 0 z * fderiv ℝ f z e₀) * ψ z ∂μ) +
         (∫ z, (A 1 z * fderiv ℝ f z e₁) * ψ z ∂μ)) +
        (∫ z, g z * ψ z ∂μ) := by
    calc
      _ = (∫ z, (2 * Complex.I) *
          ((A 0 z * fderiv ℝ f z e₀) * ψ z +
           (A 1 z * fderiv ℝ f z e₁) * ψ z) + g z * ψ z ∂μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by ring)
      _ = _ := by rw [hsright, integral_const_mul, hsdrift]
  rw [hnorm] at hraw
  have hd := v12_distributional_divergence_product a b A f ψ e₀ e₁ hA hf hψ hc hs hdiv
  simp only [mul_assoc] at hraw
  rw [hd] at hraw
  simpa only [mul_neg, neg_mul, mul_assoc] using hraw

#print axioms v12_compact_PDE_from_original_distribution
end SMScattering.W20Full
