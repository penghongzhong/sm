import lean.v12.V12_YZZGUTensorFubini
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! On a finite closed time slab, local integrability of an actual spacetime
source and a continuous compact spatial test prove the time L1 pairing.
This supplies the integrability needed by the weak-time FTC route. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory

theorem v12_spatial_test_joint_integrable
    (a b : ℝ) (r : V12Spacetime → ℂ) (ψ : V12Spatial → ℂ)
    (hr : LocallyIntegrable r (v12_slab_measure a b))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun z => r z * ψ z.2) (v12_slab_measure a b) := by
  let K : Set V12Spacetime := Set.Icc a b ×ˢ tsupport ψ
  have hK : IsCompact K := isCompact_Icc.prod hc
  have hi : IntegrableOn (fun z => r z * ψ z.2) K (v12_slab_measure a b) :=
    (hr.integrableOn_isCompact hK).mul_continuousOn
      (hψ.comp continuous_snd).continuousOn hK
  apply hi.integrable_of_ae_notMem_eq_zero
  rw [v12_slab_measure, Measure.restrict_prod_eq_prod_univ]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
  intro hn
  have hnot : z.2 ∉ tsupport ψ := fun hp => hn ⟨hz.1,hp⟩
  rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]

theorem v12_spatial_test_time_integrable
    (a b : ℝ) (r : V12Spacetime → ℂ) (ψ : V12Spatial → ℂ)
    (hr : LocallyIntegrable r (v12_slab_measure a b))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun t => ∫ x : V12Spatial, r (t,x) * ψ x)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
  exact (v12_spatial_test_joint_integrable a b r ψ hr hψ hc).integral_prod_left

theorem v12_time_derivative_pairing_continuousOn
    (a b : ℝ) (f : V12Spacetime → ℂ) (ψ : V12Spatial → ℂ)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Prod.fst ⁻¹' Set.Ioo a b))
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ContinuousOn (fun t => ∫ x : V12Spatial,
      fderiv ℝ f (t,x) v12_timeDirection * ψ x) (Set.Ioo a b) := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hd : ContinuousOn (fun z => fderiv ℝ f z v12_timeDirection) U :=
    (hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  apply continuousOn_integral_of_compact_support
    (μ := (volume : Measure V12Spatial)) (k := tsupport ψ) hc
  · exact (hd.mul (hψ.comp continuous_snd).continuousOn).mono (fun z hz => hz.1)
  · intro t x _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

#print axioms v12_time_derivative_pairing_continuousOn

noncomputable def v12_scalarSpatialTestSource
    (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g : V12Spacetime → ℂ) (ψ : V12Spatial → ℂ) (t : ℝ) : ℂ :=
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  Complex.I * ((∫ x, f (t,x) * fderiv ℝ (fun y => fderiv ℝ ψ y (e 0)) x (e 0)) +
    (∫ x, f (t,x) * fderiv ℝ (fun y => fderiv ℝ ψ y (e 1)) x (e 1))) -
  2 * ((∫ x, (A 0 (t,x) * f (t,x)) * fderiv ℝ ψ x (e 0)) +
    (∫ x, (A 1 (t,x) * f (t,x)) * fderiv ℝ ψ x (e 1))) -
  Complex.I * (∫ x, g (t,x) * ψ x)

theorem v12_scalarSpatialTestSource_integrable
    (a b : ℝ) (f : V12Spacetime → ℂ) (A : Fin 2 → V12Spacetime → ℂ)
    (g : V12Spacetime → ℂ) (ψ : V12Spatial → ℂ)
    (hf : LocallyIntegrable f (v12_slab_measure a b))
    (hAf : ∀ j, LocallyIntegrable (fun z => A j z * f z) (v12_slab_measure a b))
    (hg : LocallyIntegrable g (v12_slab_measure a b))
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    Integrable (v12_scalarSpatialTestSource f A g ψ)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hd (v : V12Spatial) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => fderiv ℝ ψ x v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdc (v : V12Spatial) : HasCompactSupport (fun x => fderiv ℝ ψ x v) :=
    hc.of_isClosed_subset isClosed_closure (tsupport_fderiv_apply_subset ℝ v)
  have hdd (v : V12Spatial) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => fderiv ℝ (fun y => fderiv ℝ ψ y v) x v) :=
    ((hd v).fderiv_right (by simp)).clm_apply contDiff_const
  have hddc (v : V12Spatial) : HasCompactSupport
      (fun x => fderiv ℝ (fun y => fderiv ℝ ψ y v) x v) :=
    (hdc v).of_isClosed_subset isClosed_closure (tsupport_fderiv_apply_subset ℝ v)
  have hL (j : Fin 2) := v12_spatial_test_time_integrable a b f _ hf
    (hdd (e j)).continuous (hddc (e j))
  have hB (j : Fin 2) := v12_spatial_test_time_integrable a b _ _ (hAf j)
    (hd (e j)).continuous (hdc (e j))
  have hZ := v12_spatial_test_time_integrable a b g ψ hg hψ.continuous hc
  exact (((hL 0).add (hL 1)).const_mul Complex.I).sub
    (((hB 0).add (hB 1)).const_mul 2) |>.sub (hZ.const_mul Complex.I)

#print axioms v12_scalarSpatialTestSource_integrable
#print axioms v12_spatial_test_joint_integrable
#print axioms v12_spatial_test_time_integrable
end SMScattering.W20Full
