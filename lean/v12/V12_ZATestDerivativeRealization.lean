import lean.v12.V12_TestNormLimits
import lean.v12.V12_YZeroOrderTestLimit

/-!
Concrete derivative-kernel L2 realizations and the complete test-source L1
limit. The kernels are derivatives of the exact compact test; none of their
norm convergence statements is accepted as an input. Limits hold for fixed
x. The original distributional PDE residual is a separate obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory LineDeriv Laplacian
open scoped Topology ENNReal ContDiff

theorem v12_reflectedSchwartzL2_ae
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial) :
    (v12_reflectedTranslate (k.toLp 2 (volume : Measure V12Spatial)) x : V12Spatial → ℂ)
      =ᵐ[volume] fun y => k (x-y) := by
  have h₁ := v12_reflectedTranslate_ae (k.toLp 2 (volume : Measure V12Spatial)) x
  have h₂ := (v12_subLeft_measurePreserving x).quasiMeasurePreserving.ae
    (k.coeFn_toLp 2 (volume : Measure V12Spatial))
  filter_upwards [h₁, h₂] with y h₁y h₂y
  exact h₁y.trans (by simpa only [v12_subLeftFamily_apply] using h₂y)

section Kernels

variable (χ : SchwartzMap V12Spatial ℝ) (hc : HasCompactSupport χ)
  (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
  (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial)

include hχ0 hχb

/-- The exact first derivative of the compact test, as an L2 class. -/
theorem v12_actual_test_first_L2_tendsto (m : V12Spatial) :
    Tendsto (fun R => (∂_{m}
      (v12_compactSpatialTestSchwartz χ hc (χ.smooth (⊤ : ℕ∞)) k R x)).toLp 2 (volume : Measure V12Spatial))
      atTop (𝓝 (v12_reflectedTranslate ((-∂_{m} k).toLp 2 (volume : Measure V12Spatial)) x)) := by
  let Ψ := fun R => v12_compactSpatialTestSchwartz χ hc (χ.smooth (⊤ : ℕ∞)) k R x
  let uR : ℕ → V12ScalarL2 := fun R =>
    (∂_{m} (Ψ R)).toLp 2 (volume : Measure V12Spatial)
  let u : V12ScalarL2 := v12_reflectedTranslate
    ((-∂_{m} k).toLp 2 (volume : Measure V12Spatial)) x
  have hR : ∀ R, (uR R : V12Spatial → ℂ) =ᵐ[volume] (∂_{m} (Ψ R)) := by
    intro R
    exact (∂_{m} (Ψ R)).coeFn_toLp 2 (volume : Measure V12Spatial)
  have hu : (u : V12Spatial → ℂ) =ᵐ[volume] (fun y => (-∂_{m} k) (x-y)) :=
    v12_reflectedSchwartzL2_ae (-∂_{m} k) x
  change Tendsto uR atTop (𝓝 u)
  refine v12_Lp_tendsto_of_ae_eLpNorm_error (volume : Measure V12Spatial) 2
    uR u (fun R y => (∂_{m} (Ψ R)) y) (fun y => (-∂_{m} k) (x-y)) hR hu ?_
  have hid : ∀ R y, (∂_{m} (Ψ R)) y - (-∂_{m} k) (x-y) =
      fderiv ℝ (v12_compactSpatialTest χ k R x) y m + (∂_{m} k) (x-y) := by
    intro R y
    change fderiv ℝ (v12_compactSpatialTest χ k R x) y m - (-(∂_{m} k) (x-y)) = _
    exact sub_neg_eq_add _ _
  simpa only [hid] using v12_compactSpatialTest_fderiv_error_tendsto
    2 (by norm_num) (by norm_num) χ hχ0 hχb k x m

/-- The exact two-coordinate Laplacian, not an assumed L2 approximation. -/
theorem v12_actual_test_laplacian_L2_tendsto :
    Tendsto (fun R => (Δ
      (v12_compactSpatialTestSchwartz χ hc (χ.smooth (⊤ : ℕ∞)) k R x)).toLp 2 (volume : Measure V12Spatial))
      atTop (𝓝 (v12_reflectedTranslate ((Δ k).toLp 2 (volume : Measure V12Spatial)) x)) := by
  let Ψ := fun R => v12_compactSpatialTestSchwartz χ hc (χ.smooth (⊤ : ℕ∞)) k R x
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let H : Fin 2 → ℕ → V12Spatial → ℂ := fun j R y =>
    fderiv ℝ (fun z => fderiv ℝ (v12_compactSpatialTest χ k R x) z (e j)) y (e j) -
      (∂_{e j} (∂_{e j} k)) (x-y)
  have hH : ∀ j, Tendsto (fun R => eLpNorm (H j R) 2 volume) atTop (𝓝 0) := by
    intro j
    exact v12_compactSpatialTest_second_error_tendsto 2 (by norm_num) (by norm_num)
      χ hχ0 hχb k x (e j)
  have hsum := v12_eLpNorm_add_tendsto_zero 2 (by norm_num) (H 0) (H 1) (hH 0) (hH 1)
  have hid : ∀ R y, (Δ (Ψ R)) y - (Δ k) (x-y) = (H 0 R + H 1 R) y := by
    intro R y
    rw [SchwartzMap.laplacian_eq_sum e (Ψ R), SchwartzMap.laplacian_eq_sum e k]
    simp only [Fin.sum_univ_two, SchwartzMap.add_apply]
    change (fderiv ℝ (fun z => fderiv ℝ (v12_compactSpatialTest χ k R x) z (e 0)) y (e 0) +
      fderiv ℝ (fun z => fderiv ℝ (v12_compactSpatialTest χ k R x) z (e 1)) y (e 1)) -
      ((∂_{e 0} (∂_{e 0} k)) (x-y) + (∂_{e 1} (∂_{e 1} k)) (x-y)) = _
    dsimp only [H, Pi.add_apply]
    abel
  let uR : ℕ → V12ScalarL2 := fun R =>
    (Δ (Ψ R)).toLp 2 (volume : Measure V12Spatial)
  let u : V12ScalarL2 := v12_reflectedTranslate
    ((Δ k).toLp 2 (volume : Measure V12Spatial)) x
  have hR : ∀ R, (uR R : V12Spatial → ℂ) =ᵐ[volume] (Δ (Ψ R)) := by
    intro R
    exact (Δ (Ψ R)).coeFn_toLp 2 (volume : Measure V12Spatial)
  have hu : (u : V12Spatial → ℂ) =ᵐ[volume] (fun y => (Δ k) (x-y)) :=
    v12_reflectedSchwartzL2_ae (Δ k) x
  change Tendsto uR atTop (𝓝 u)
  refine v12_Lp_tendsto_of_ae_eLpNorm_error (volume : Measure V12Spatial) 2
    uR u (fun R y => (Δ (Ψ R)) y) (fun y => (Δ k) (x-y)) hR hu ?_
  simpa only [hid] using hsum

end Kernels

/-- The actual compact test source converges in time L1. All its spatial
L2 and L4 kernel convergence statements are conclusions proved above. -/
theorem v12_actual_test_fullSource_L1_tendsto
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (χ : SchwartzMap V12Spatial ℝ) (hc : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : MemLp Q ∞ μ) (hF : ∀ j, MemLp (F j) 2 μ)
    (hG : MemLp G ((4 : ℝ≥0∞) / 3) μ) :
    let Ψ := fun R => v12_compactSpatialTestSchwartz χ hc (χ.smooth (⊤ : ℕ∞)) k R x
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    Tendsto (fun R => ∫ t,
      ‖v12_testSourceFromLpKernels ((Δ (Ψ R)).toLp 2 (volume : Measure V12Spatial))
        (fun j => (∂_{e j} (Ψ R)).toLp 2 (volume : Measure V12Spatial)) ((Ψ R).toLp 4) Q F G t -
      v12_testSourceFromLpKernels (v12_reflectedTranslate ((Δ k).toLp 2 (volume : Measure V12Spatial)) x)
        (fun j => v12_reflectedTranslate ((-∂_{e j} k).toLp 2 (volume : Measure V12Spatial)) x)
        (v12_reflectedTranslateL4 (k.toLp 4) x) Q F G t‖ ∂μ) atTop (𝓝 0) := by
  dsimp only
  exact v12_testSourceFromLpKernels_L1_tendsto_of_MemLp μ _ _ _ _ _ _
    (v12_actual_test_laplacian_L2_tendsto χ hc hχ0 hχb k x)
    (fun j => v12_actual_test_first_L2_tendsto χ hc hχ0 hχb k x
      (EuclideanSpace.basisFun (Fin 2) ℝ j))
    (v12_compactSpatialTestL4_tendsto χ hc (χ.smooth (⊤ : ℕ∞)) hχ0 hχb k x)
    Q F G hQ hF hG

#print axioms v12_reflectedSchwartzL2_ae
#print axioms v12_actual_test_first_L2_tendsto
#print axioms v12_actual_test_laplacian_L2_tendsto
#print axioms v12_actual_test_fullSource_L1_tendsto

end SMScattering.W20Full
