import lean.v12.V12_YWWOriginalComponentPDE
import lean.v12.V12_YRActualCurvatureBounds

/-! Original spatial divergence/curl/torsion equations imply the canonical
joint equations for the zero extension. Smoothness and all derivative and
coefficient correspondences are derived locally on the open slab. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace SMScattering.W20Full

theorem v12_original_extended_spatial_constraints
    (a b : ℝ) (q : ℝ → V12Spatial → V12Field)
    (hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry q) (Prod.fst ⁻¹' Set.Ioo a b))
    (hA : ∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (v12_actualCoulombA (Function.uncurry q) k) (Prod.fst ⁻¹' Set.Ioo a b))
    (hdiv : ∀ t, t ∈ Set.Ioo a b → ∀ x,
      fderiv ℝ (fun y => v12_actualCoulombA (Function.uncurry q) 0 (t,y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (fun y => v12_actualCoulombA (Function.uncurry q) 1 (t,y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0)
    (hcurl : ∀ t, t ∈ Set.Ioo a b → ∀ x,
      fderiv ℝ (fun y => v12_actualCoulombA (Function.uncurry q) 1 (t,y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) -
      fderiv ℝ (fun y => v12_actualCoulombA (Function.uncurry q) 0 (t,y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) = (v12_curvatureDensity (q t x) : ℂ))
    (htorsion : ∀ t, t ∈ Set.Ioo a b → ∀ x,
      fderiv ℝ (fun y => q t y 1) x (EuclideanSpace.basisFun (Fin 2) ℝ 0) -
      fderiv ℝ (fun y => q t y 0) x (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      Complex.I * (v12_actualCoulombA (Function.uncurry q) 0 (t,x) * q t x 1 -
        v12_actualCoulombA (Function.uncurry q) 1 (t,x) * q t x 0)) :
    let ext := v12_smoothSlabExtension a b (Function.uncurry q)
    (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ext z j)
      (Prod.fst ⁻¹' Set.Ioo a b)) ∧
    (∀ k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v12_actualCoulombA ext k)
      (Prod.fst ⁻¹' Set.Ioo a b)) ∧
    (∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (v12_actualCoulombA ext 0) z (v12_spatialDirection 0) +
      fderiv ℝ (v12_actualCoulombA ext 1) z (v12_spatialDirection 1) = 0) ∧
    (∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (v12_actualCoulombA ext 1) z (v12_spatialDirection 0) -
      fderiv ℝ (v12_actualCoulombA ext 0) z (v12_spatialDirection 1) =
        (v12_curvatureDensity (ext z) : ℂ)) ∧
    (∀ z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (fun x => ext x 1) z (v12_spatialDirection 0) -
      fderiv ℝ (fun x => ext x 0) z (v12_spatialDirection 1) =
      Complex.I * (v12_actualCoulombA ext 0 z * ext z 1 -
        v12_actualCoulombA ext 1 z * ext z 0)) := by
  let f := Function.uncurry q
  let ext := v12_smoothSlabExtension a b f
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hqc (j : Fin 2) := v12_component_contDiffOn a b f j hq
  have hqs (j : Fin 2) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ext z j) U :=
    v12_component_contDiffOn a b ext j (v12_smoothSlabExtension_contDiffOn a b f hq)
  have hAs (k : Fin 2) := v12_smoothSlabExtension_A_contDiffOn a b f k (hA k)
  have hAd (k : Fin 2) (z : V12Spacetime) (hz : z ∈ U) :=
    v12_smoothSlabExtension_A_fderiv a b f k hz
  have hApoint (k : Fin 2) (z : V12Spacetime) (hz : z ∈ U) :=
    v12_smoothSlabExtension_A_eqOn_interior a b f k hz
  have hAdiff (k : Fin 2) (z : V12Spacetime) (hz : z ∈ U) :
      DifferentiableAt ℝ (v12_actualCoulombA f k) z :=
    ((hA k).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  have hQdiff (j : Fin 2) (z : V12Spacetime) (hz : z ∈ U) :
      DifferentiableAt ℝ (fun x => f x j) z :=
    ((hqc j).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  have hQd (j : Fin 2) : Set.EqOn (fderiv ℝ (fun x => ext x j))
      (fderiv ℝ (fun x => f x j)) U := by
    apply v12_open_eqOn_fderiv U hU
    intro z hz
    exact congrArg (fun u : V12Field => u j) (v12_smoothSlabExtension_eqOn_interior a b f hz)
  refine ⟨hqs, hAs, ?_, ?_, ?_⟩
  · intro z hz
    rw [hAd 0 z hz, hAd 1 z hz,
      v12_joint_fderiv_spatial_slice _ z.1 z.2 _ (hAdiff 0 z hz),
      v12_joint_fderiv_spatial_slice _ z.1 z.2 _ (hAdiff 1 z hz)]
    exact hdiv z.1 hz z.2
  · intro z hz
    rw [hAd 1 z hz, hAd 0 z hz, v12_smoothSlabExtension_eqOn_interior a b f hz,
      v12_joint_fderiv_spatial_slice _ z.1 z.2 _ (hAdiff 1 z hz),
      v12_joint_fderiv_spatial_slice _ z.1 z.2 _ (hAdiff 0 z hz)]
    exact hcurl z.1 hz z.2
  · intro z hz
    rw [hQd 1 hz, hQd 0 hz, hApoint 0 z hz, hApoint 1 z hz,
      v12_smoothSlabExtension_eqOn_interior a b f hz,
      v12_joint_fderiv_spatial_slice _ z.1 z.2 _ (hQdiff 1 z hz),
      v12_joint_fderiv_spatial_slice _ z.1 z.2 _ (hQdiff 0 z hz)]
    exact htorsion z.1 hz z.2

#print axioms v12_original_extended_spatial_constraints
end SMScattering.W20Full
