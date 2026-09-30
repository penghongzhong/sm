import lean.v12.V12_ZBTestSourceIdentification
import lean.v12.V12_ZCSpatialTestIntegrationByParts

/-!
Exact raw-function representatives of the already defined Lp test source.
The a.e. equalities identify the SAME fields and kernels, not merely their
norms. No tested-source or time-integral identity is a hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open MeasureTheory LineDeriv Laplacian
open scoped ContDiff

theorem v12_L2Pairing_eq_raw_integral
    (k : V12ScalarL2) (f : V12SpatialL2)
    (K : V12Spatial → ℂ) (F : V12Spatial → V12Field)
    (hk : (k : V12Spatial → ℂ) =ᵐ[volume] K)
    (hf : (f : V12Spatial → V12Field) =ᵐ[volume] F) :
    v12_L2ConvolutionPairing k f = ∫ y : V12Spatial, K y • F y := by
  rw [v12_L2ConvolutionPairing, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hk, hf] with y hky hfy
  change k y • f y = K y • F y
  rw [hky, hfy]

theorem v12_L4L43Pairing_eq_raw_integral
    (k : V12ScalarL4) (f : V12SpatialLFourThirds)
    (K : V12Spatial → ℂ) (F : V12Spatial → V12Field)
    (hk : (k : V12Spatial → ℂ) =ᵐ[volume] K)
    (hf : (f : V12Spatial → V12Field) =ᵐ[volume] F) :
    v12_L4L43ConvolutionPairing k f = ∫ y : V12Spatial, K y • F y := by
  rw [v12_L4L43ConvolutionPairing, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hk, hf] with y hky hfy
  change k y • f y = K y • F y
  rw [hky, hfy]

/-- The full source class is the exact raw spatial test expression. -/
theorem v12_testSourceFromLpKernels_eq_raw_integrals
    (ψ : SchwartzMap V12Spatial ℂ)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds) (t : ℝ)
    (q g : V12Spatial → V12Field) (f : Fin 2 → V12Spatial → V12Field)
    (hQ : (Q t : V12Spatial → V12Field) =ᵐ[volume] q)
    (hF : ∀ j, (F j t : V12Spatial → V12Field) =ᵐ[volume] f j)
    (hG : (G t : V12Spatial → V12Field) =ᵐ[volume] g) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    v12_testSourceFromLpKernels ((Δ ψ).toLp 2 (volume : Measure V12Spatial))
      (fun j => (∂_{e j} ψ).toLp 2 (volume : Measure V12Spatial))
      (ψ.toLp 4 (volume : Measure V12Spatial)) Q F G t =
      Complex.I • (∫ y : V12Spatial, (Δ ψ) y • q y) +
      (-2 : ℂ) • (∫ y : V12Spatial, (∂_{e 0} ψ) y • f 0 y) +
      (-2 : ℂ) • (∫ y : V12Spatial, (∂_{e 1} ψ) y • f 1 y) +
      (-Complex.I) • (∫ y : V12Spatial, ψ y • g y) := by
  dsimp only
  have hL := v12_L2Pairing_eq_raw_integral
    ((Δ ψ).toLp 2 (volume : Measure V12Spatial)) (Q t)
    (fun y => (Δ ψ) y) q ((Δ ψ).coeFn_toLp 2 (volume : Measure V12Spatial)) hQ
  have hB : ∀ j : Fin 2,
      v12_L2ConvolutionPairing
        ((∂_{EuclideanSpace.basisFun (Fin 2) ℝ j} ψ).toLp 2
          (volume : Measure V12Spatial)) (F j t) =
        ∫ y : V12Spatial, (∂_{EuclideanSpace.basisFun (Fin 2) ℝ j} ψ) y • f j y := by
    intro j
    exact v12_L2Pairing_eq_raw_integral _ _ _ _
      ((∂_{EuclideanSpace.basisFun (Fin 2) ℝ j} ψ).coeFn_toLp 2
        (volume : Measure V12Spatial)) (hF j)
  have hZ := v12_L4L43Pairing_eq_raw_integral
    (ψ.toLp 4 (volume : Measure V12Spatial)) (G t) (fun y => ψ y) g
    (ψ.coeFn_toLp 4 (volume : Measure V12Spatial)) hG
  change Complex.I • v12_L2ConvolutionPairing _ _ +
    (-2 : ℂ) • v12_L2ConvolutionPairing _ _ +
    (-2 : ℂ) • v12_L2ConvolutionPairing _ _ +
    (-Complex.I) • v12_L4L43ConvolutionPairing _ _ = _
  rw [hL, hB 0, hB 1, hZ]

/-- The quotient source equals the tested time derivative of the raw PDE. -/
theorem v12_testSource_eq_raw_pde_derivative
    (ψ : SchwartzMap V12Spatial ℂ) (hc : HasCompactSupport (ψ : V12Spatial → ℂ))
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds) (t : ℝ)
    (q dq g : V12Spatial → V12Field) (f : Fin 2 → V12Spatial → V12Field)
    (hQ : (Q t : V12Spatial → V12Field) =ᵐ[volume] q)
    (hF : ∀ j, (F j t : V12Spatial → V12Field) =ᵐ[volume] f j)
    (hG : (G t : V12Spatial → V12Field) =ᵐ[volume] g)
    (hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q)
    (hf : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j))
    (hg : Continuous g)
    (hPDE : ∀ y, dq y =
      Complex.I • (fderiv ℝ (fun z => fderiv ℝ q z
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)) y (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        fderiv ℝ (fun z => fderiv ℝ q z
        (EuclideanSpace.basisFun (Fin 2) ℝ 1)) y (EuclideanSpace.basisFun (Fin 2) ℝ 1)) +
      (2 : ℂ) • fderiv ℝ (f 0) y (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      (2 : ℂ) • fderiv ℝ (f 1) y (EuclideanSpace.basisFun (Fin 2) ℝ 1) +
      (-Complex.I) • g y) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    v12_testSourceFromLpKernels ((Δ ψ).toLp 2 (volume : Measure V12Spatial))
      (fun j => (∂_{e j} ψ).toLp 2 (volume : Measure V12Spatial))
      (ψ.toLp 4 (volume : Measure V12Spatial)) Q F G t =
      ∫ y : V12Spatial, ψ y • dq y := by
  dsimp only
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  have hi : ∀ j : Fin 2, Integrable
      (fun y : V12Spatial => (∂_{e j} (∂_{e j} ψ)) y • q y) := by
    intro j
    apply ((∂_{e j} (∂_{e j} ψ)).continuous.smul hq.continuous).integrable_of_hasCompactSupport
    exact ((hc.fderiv_apply ℝ (e j)).fderiv_apply ℝ (e j)).smul_right
  have hLap : (∫ y : V12Spatial, (Δ ψ) y • q y) =
      (∫ y : V12Spatial, (∂_{e 0} (∂_{e 0} ψ)) y • q y) +
      (∫ y : V12Spatial, (∂_{e 1} (∂_{e 1} ψ)) y • q y) := by
    rw [SchwartzMap.laplacian_eq_sum e ψ]
    simp only [Fin.sum_univ_two, SchwartzMap.add_apply, add_smul]
    exact integral_add (hi 0) (hi 1)
  rw [v12_testSourceFromLpKernels_eq_raw_integrals ψ Q F G t q g f hQ hF hG, hLap]
  exact (v12_compact_test_raw_pde_source (ψ : V12Spatial → ℂ) hc
    (ψ.smooth (⊤ : ℕ∞)) q dq g f hq hf hg hPDE).symm

#print axioms v12_testSource_eq_raw_pde_derivative
#print axioms v12_L2Pairing_eq_raw_integral
#print axioms v12_L4L43Pairing_eq_raw_integral
#print axioms v12_testSourceFromLpKernels_eq_raw_integrals

end SMScattering.W20Full
