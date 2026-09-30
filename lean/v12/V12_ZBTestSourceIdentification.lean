import lean.v12.V12_ZATestDerivativeRealization

/-!
The limiting compact-test source is identified with the SAME actual cutoff
BCF source. The sign from spatial integration by parts (-2) and the sign
from the reflected kernel derivative (-1) give the PDE drift coefficient
(+2). Neither the source identity nor time-L1 convergence is assumed.
The original weak PDE residual and time-valued Hodge realizations remain
separate application obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory LineDeriv Laplacian
open scoped Topology ENNReal ContDiff

/-- Negation commutes with the actual reflected Schwartz L2 class. -/
theorem v12_reflectedSchwartzL2_neg
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial) :
    v12_reflectedTranslate ((-k).toLp 2) x =
      -v12_reflectedTranslate (k.toLp 2) x := by
  apply Lp.ext_iff.mpr
  filter_upwards [v12_reflectedSchwartzL2_ae (-k) x,
    Lp.coeFn_neg (v12_reflectedTranslate (k.toLp 2) x),
    v12_reflectedSchwartzL2_ae k x] with y hneg hcoe hpos
  rw [hneg, hcoe]
  simp only [Pi.neg_apply, SchwartzMap.neg_apply, hpos]

/-- Both signs are retained until the exact equality is proved. -/
theorem v12_testGradient_reflection_sign
    (k : SchwartzMap V12Spatial ℂ) (f : V12SpatialL2) (x : V12Spatial) :
    v12_testGradientPairing (v12_reflectedTranslate ((-k).toLp 2) x) f =
      (2 : ℂ) • v12_L2ConvolutionRep (k.toLp 2) f x := by
  rw [v12_reflectedSchwartzL2_neg]
  simp only [v12_testGradientPairing, ContinuousLinearMap.smul_apply,
    map_neg, ContinuousLinearMap.neg_apply, smul_neg, neg_smul, neg_neg,
    v12_L2ConvolutionRep]

/-- The limiting test source is the actual cutoff time source, not a new
or merely equinormed source. This is an identity for arbitrary Lp inputs. -/
theorem v12_limitTestSource_eq_cutoffTimeSource
    (p : V12Spatial → ℝ) (hp_cpt : HasCompactSupport p)
    (hp_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds) (t : ℝ) (x : V12Spatial) :
    let k := v12_cutoffKernelSchwartz p hp_cpt hp_smooth N
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    v12_testSourceFromLpKernels (v12_reflectedTranslate ((Δ k).toLp 2) x)
      (fun j => v12_reflectedTranslate ((-∂_{e j} k).toLp 2) x)
      (v12_reflectedTranslateL4 (k.toLp 4) x) Q F G t =
      v12_cutoffTimeSource p hp_cpt hp_smooth N Q F G t x := by
  dsimp only
  unfold v12_testSourceFromLpKernels
  rw [v12_testGradient_reflection_sign, v12_testGradient_reflection_sign]
  rfl

/-- Actual compact-test source convergence to the identified cutoff source.
All spatial kernel limits and the identification are previously proved. -/
theorem v12_actual_test_fullSource_to_cutoff_L1_tendsto
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (χ : SchwartzMap V12Spatial ℝ) (hc : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (p : V12Spatial → ℝ) (hp_cpt : HasCompactSupport p)
    (hp_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (x : V12Spatial)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQ : MemLp Q ∞ μ) (hF : ∀ j, MemLp (F j) 2 μ)
    (hG : MemLp G ((4 : ℝ≥0∞) / 3) μ) :
    let k := v12_cutoffKernelSchwartz p hp_cpt hp_smooth N
    let Ψ := fun R => v12_compactSpatialTestSchwartz χ hc (χ.smooth (⊤ : ℕ∞)) k R x
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    Tendsto (fun R => ∫ t,
      ‖v12_testSourceFromLpKernels ((Δ (Ψ R)).toLp 2)
        (fun j => (∂_{e j} (Ψ R)).toLp 2) ((Ψ R).toLp 4) Q F G t -
        v12_cutoffTimeSource p hp_cpt hp_smooth N Q F G t x‖ ∂μ)
      atTop (𝓝 0) := by
  have h := v12_actual_test_fullSource_L1_tendsto μ χ hc hχ0 hχb
    (v12_cutoffKernelSchwartz p hp_cpt hp_smooth N) x Q F G hQ hF hG
  dsimp only at h ⊢
  simpa only [v12_limitTestSource_eq_cutoffTimeSource] using h

#print axioms v12_reflectedSchwartzL2_neg
#print axioms v12_testGradient_reflection_sign
#print axioms v12_limitTestSource_eq_cutoffTimeSource
#print axioms v12_actual_test_fullSource_to_cutoff_L1_tendsto

end SMScattering.W20Full
