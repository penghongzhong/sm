import lean.v12.V12_ZDHOriginalCompactTimeIdentity
import lean.v12.V12_ZERawSourceRepresentatives

/-! Identify the actual vector source with the previously constructed Lp
source using SAME-field representatives. Every spatial integral commuted
with a component is proved integrable. No source equality is assumed.
Pending actual Lean execution. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace SMScattering.W20Full
open MeasureTheory LineDeriv Laplacian
open scoped ENNReal ContDiff

theorem v12_originalVectorTestSource_eq_Lp
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq4 : MemLp q 4 (v12_slab_measure a b))
    (ψ : SchwartzMap V12Spatial ℂ) (hc : HasCompactSupport (ψ : V12Spatial → ℂ))
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds) (t : ℝ)
    (hQ : (Q t : V12Spatial → V12Field) =ᵐ[volume] (fun x => q (t,x)))
    (hF : ∀ j, (F j t : V12Spatial → V12Field) =ᵐ[volume]
      (fun x => v12_driftProduct (v12_actualCoulombA q) q j (t,x)))
    (hG : (G t : V12Spatial → V12Field) =ᵐ[volume]
      (fun x => v12_zeroOrderProduct (v12_originalReconstructedPotential a b q hq4)
        (fun z => v12_WDensity (q z)) q (t,x))) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    v12_originalVectorTestSource a b q hq4 ψ t =
      v12_testSourceFromLpKernels ((Δ ψ).toLp 2 (volume : Measure V12Spatial))
        (fun j => (∂_{e j} ψ).toLp 2 (volume : Measure V12Spatial))
        (ψ.toLp 4 (volume : Measure V12Spatial)) Q F G t := by
  dsimp only
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let d (j : Fin 2) : SchwartzMap V12Spatial ℂ := ∂_{e j} ψ
  let dd (j : Fin 2) : SchwartzMap V12Spatial ℂ := ∂_{e j} (d j)
  let f (j : Fin 2) := fun x => v12_driftProduct (v12_actualCoulombA q) q j (t,x)
  let g := fun x => v12_zeroOrderProduct (v12_originalReconstructedPotential a b q hq4)
    (fun z => v12_WDensity (q z)) q (t,x)
  have hq2 : MemLp (fun x => q (t,x)) 2 (volume : Measure V12Spatial) :=
    (Lp.memLp (Q t)).ae_eq hQ
  have hf2 (j : Fin 2) : MemLp (f j) 2 (volume : Measure V12Spatial) :=
    (Lp.memLp (F j t)).ae_eq (hF j)
  have hg43 : MemLp g ((4 : ℝ≥0∞)/3) (volume : Measure V12Spatial) :=
    (Lp.memLp (G t)).ae_eq hG
  have hiL (j : Fin 2) : Integrable (fun x => dd j x • q (t,x)) :=
    (hq2.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (dd j).continuous ((hc.fderiv_apply ℝ (e j)).fderiv_apply ℝ (e j))
  have hiB (j : Fin 2) : Integrable (fun x => d j x • f j x) :=
    ((hf2 j).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (d j).continuous (hc.fderiv_apply ℝ (e j))
  have hp : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).mpr
    norm_num
  have hiZ : Integrable (fun x => ψ x • g x) :=
    (hg43.locallyIntegrable hp).integrable_smul_left_of_hasCompactSupport ψ.continuous hc
  have hLap : (∫ x : V12Spatial, (Δ ψ) x • q (t,x)) =
      (∫ x : V12Spatial, dd 0 x • q (t,x)) + (∫ x : V12Spatial, dd 1 x • q (t,x)) := by
    rw [SchwartzMap.laplacian_eq_sum e ψ]
    simp only [Fin.sum_univ_two, add_apply, add_smul]
    exact integral_add (hiL 0) (hiL 1)
  rw [v12_testSourceFromLpKernels_eq_raw_integrals ψ Q F G t
    (fun x => q (t,x)) g f hQ hF hG, hLap]
  apply PiLp.ext
  intro j
  change v12_scalarSpatialTestSource (fun z => q z j)
    (v12_actualCoulombA q) (v12_originalScalarSource a b q hq4 j) ψ t = _
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [eval_integral_piLp (fun i => (hiL 0).eval_piLp i) j,
    eval_integral_piLp (fun i => (hiL 1).eval_piLp i) j,
    eval_integral_piLp (fun i => (hiB 0).eval_piLp i) j,
    eval_integral_piLp (fun i => (hiB 1).eval_piLp i) j,
    eval_integral_piLp (fun i => hiZ.eval_piLp i) j]
  have hswap (r χ : V12Spatial → ℂ) :
      (∫ x, χ x * r x) = ∫ x, r x * χ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
  simp only [v12_scalarSpatialTestSource, d, dd, e, f, g,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, v12_driftProduct,
    v12_zeroOrderProduct, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    v12_conjugateField_apply, ← v12_originalScalarSource, hswap]
  ring

#print axioms v12_originalVectorTestSource_eq_Lp
end SMScattering.W20Full
