import lean.v12.V12_YZZGTTensorOriginalPDE
import lean.v12.V12_YZZGVSpatialTestTimeIntegrability

/-! The weighted time identity is derived from the ORIGINAL distributional
PDE, concrete tensor tests, and actual Fubini integrability. No time-source
identity, coefficient smoothness, or derivative endpoint regularity is assumed.
Pending actual CI; this is not yet a certified manuscript theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_PDE_weighted_time_source
    (a b : ℝ) (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g : V12Spacetime → ℂ) (η : ℝ → ℂ) (ψ : V12Spatial → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hA : ∀ j, LocallyIntegrable (A j) (v12_slab_measure a b))
    (hg : MemLp g ((4 : ℝ≥0∞)/3) (v12_slab_measure a b))
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Set.Ioo a b)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hdiv : ∀ φ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, A 0 z * fderiv ℝ φ z (v12_spatialDirection 0) ∂v12_slab_measure a b) +
      (∫ z, A 1 z * fderiv ℝ φ z (v12_spatialDirection 1) ∂v12_slab_measure a b) = 0)
    (hPDE : V12OriginalScalarDistributionalPDE a b f A g
      v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1)) :
    Integrable (fun t => η t * (∫ x : V12Spatial,
      fderiv ℝ f (t,x) v12_timeDirection * ψ x))
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ∧
    (∫ t, η t * (∫ x : V12Spatial, fderiv ℝ f (t,x) v12_timeDirection * ψ x)
      ∂(volume : Measure ℝ).restrict (Set.Icc a b)) =
    ∫ t, η t * v12_scalarSpatialTestSource f A g ψ t
      ∂(volume : Measure ℝ).restrict (Set.Icc a b) := by
  let μ := (volume : Measure ℝ).restrict (Set.Icc a b)
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let d (j : Fin 2) := fun x => fderiv ℝ ψ x (e j)
  let dd (j : Fin 2) := fun x => fderiv ℝ (d j) x (e j)
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hd (j : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (d j) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc (j : Fin 2) : HasCompactSupport (d j) :=
    hcψ.of_isClosed_subset isClosed_closure (tsupport_fderiv_apply_subset ℝ (e j))
  have hdd (j : Fin 2) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dd j) :=
    ((hd j).fderiv_right (by simp)).clm_apply contDiff_const
  have hddc (j : Fin 2) : HasCompactSupport (dd j) :=
    (hdc j).of_isClosed_subset isClosed_closure (tsupport_fderiv_apply_subset ℝ (e j))
  have hint (r : V12Spacetime → ℂ) (hr : ContinuousOn r U)
      (χ : V12Spatial → ℂ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ) :
      Integrable (fun z => r z * (η z.1 * χ z.2)) (v12_slab_measure a b) :=
    v12_local_smooth_compact_product_integrable U hU r (v12_tensorTest η χ)
      hr ((hη.continuous.comp continuous_fst).mul (hχ.comp continuous_snd))
      (v12_tensorTest_compact η χ hcη hcχ)
      (v12_tensorTest_support_in_slab a b η χ hsη)
  have hdf : ContinuousOn (fun z => fderiv ℝ f z v12_timeDirection) U :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hT := v12_tensor_integral_fubini a b _ η ψ
    (hint _ hdf ψ hψ.continuous hcψ)
  have hL (j : Fin 2) := v12_tensor_integral_fubini a b f η (dd j)
    (hint f hf.continuousOn (dd j) (hdd j).continuous (hddc j))
  have hiB (j : Fin 2) : Integrable
      (fun z => (A j z * f z) * (η z.1 * d j z.2)) (v12_slab_measure a b) := by
    have h := v12_locally_integrable_weighted_compact_product
      (v12_slab_measure a b) U hU (A j) f (v12_tensorTest η (d j))
      (hA j) hf.continuousOn
      ((hη.continuous.comp continuous_fst).mul ((hd j).continuous.comp continuous_snd))
      (v12_tensorTest_compact η (d j) hcη (hdc j))
      (v12_tensorTest_support_in_slab a b η (d j) hsη)
    simpa only [mul_assoc, v12_tensorTest] using h
  have hB (j : Fin 2) := v12_tensor_integral_fubini a b _ η (d j) (hiB j)
  have hp : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).mpr
    norm_num
  have hZ := v12_locally_integrable_tensor_fubini a b g η ψ
    (hg.locallyIntegrable hp) hη.continuous hcη hψ.continuous hcψ
  have hn : (∫ t, η t * v12_scalarSpatialTestSource f A g ψ t ∂μ) =
      Complex.I * ((∫ t, η t * (∫ x, f (t,x) * dd 0 x) ∂μ) +
        (∫ t, η t * (∫ x, f (t,x) * dd 1 x) ∂μ)) -
      2 * ((∫ t, η t * (∫ x, (A 0 (t,x) * f (t,x)) * d 0 x) ∂μ) +
        (∫ t, η t * (∫ x, (A 1 (t,x) * f (t,x)) * d 1 x) ∂μ)) -
      Complex.I * (∫ t, η t * (∫ x, g (t,x) * ψ x) ∂μ) := by
    calc
      _ = ∫ t, Complex.I * (η t * (∫ x, f (t,x) * dd 0 x) +
          η t * (∫ x, f (t,x) * dd 1 x)) -
          2 * (η t * (∫ x, (A 0 (t,x) * f (t,x)) * d 0 x) +
          η t * (∫ x, (A 1 (t,x) * f (t,x)) * d 1 x)) -
          Complex.I * (η t * (∫ x, g (t,x) * ψ x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        dsimp [v12_scalarSpatialTestSource, dd, d, e]
        ring
      _ = _ := by
        have hLsum : Integrable (fun t => η t * (∫ x, f (t,x) * dd 0 x) +
            η t * (∫ x, f (t,x) * dd 1 x)) μ := (hL 0).1.add (hL 1).1
        have hBsum : Integrable (fun t => η t * (∫ x, (A 0 (t,x)*f (t,x))*d 0 x) +
            η t * (∫ x, (A 1 (t,x)*f (t,x))*d 1 x)) μ := (hB 0).1.add (hB 1).1
        have hLeft : Integrable (fun t => Complex.I * (η t * (∫ x, f (t,x)*dd 0 x) +
            η t * (∫ x, f (t,x)*dd 1 x))) μ := hLsum.const_mul Complex.I
        have hMid : Integrable (fun t => (2 : ℂ) *
            (η t * (∫ x, (A 0 (t,x)*f (t,x))*d 0 x) +
             η t * (∫ x, (A 1 (t,x)*f (t,x))*d 1 x))) μ := hBsum.const_mul 2
        have hRight : Integrable (fun t => Complex.I *
            (η t * (∫ x, g (t,x)*ψ x))) μ := hZ.1.const_mul Complex.I
        have hSub : Integrable (fun t => Complex.I *
            (η t * (∫ x, f (t,x)*dd 0 x) + η t * (∫ x, f (t,x)*dd 1 x)) -
            2 * (η t * (∫ x, (A 0 (t,x)*f (t,x))*d 0 x) +
             η t * (∫ x, (A 1 (t,x)*f (t,x))*d 1 x))) μ := hLeft.sub hMid
        have hOuter := integral_sub hSub hRight
        have hInner := integral_sub hLeft hMid
        have hLs := integral_add (hL 0).1 (hL 1).1
        have hBs := integral_add (hB 0).1 (hB 1).1
        simp only [Pi.sub_apply, Pi.add_apply] at hOuter hInner hLs hBs
        rw [hOuter, hInner, integral_const_mul, integral_const_mul, integral_const_mul,
          hLs, hBs]
  have he := v12_original_PDE_tensor_time_source a b f A g η ψ
    hf hA hg hη hcη hsη hψ hcψ hdiv hPDE
  dsimp only at he
  change _ = Complex.I *
    ((∫ z, f z * (η z.1 * dd 0 z.2) ∂v12_slab_measure a b) +
     (∫ z, f z * (η z.1 * dd 1 z.2) ∂v12_slab_measure a b)) -
    2 * ((∫ z, (A 0 z * f z) * (η z.1 * d 0 z.2) ∂v12_slab_measure a b) +
     (∫ z, (A 1 z * f z) * (η z.1 * d 1 z.2) ∂v12_slab_measure a b)) -
    Complex.I * (∫ z, g z * (η z.1 * ψ z.2) ∂v12_slab_measure a b) at he
  rw [hT.2, (hL 0).2, (hL 1).2, (hB 0).2, (hB 1).2, hZ.2] at he
  exact ⟨hT.1, he.trans hn.symm⟩

#print axioms v12_original_PDE_weighted_time_source
end SMScattering.W20Full
