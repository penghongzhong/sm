import lean.v12.V12_YZZBUOriginalSourceBudgets
import lean.v12.V12_YWWOriginalComponentPDE

/-! The original curried vector PDE implies the canonical scalar PDE of
the zero-extended same field with the actual reconstructed L2 potential.
No coordinate PDE, derivative-preservation or potential correspondence is
assumed as an internal conclusion. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_extended_scalar_PDE
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (q dq : ℝ → V12Spatial → V12Field) (A0 V : V12Spacetime → ℂ)
    (hc : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry q) (Prod.fst ⁻¹' Set.Ioo a b))
    (h4 : MemLp (Function.uncurry q) 4 (v12_slab_measure a b))
    (M : ℝ)
    (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (q t) 2 volume ≤ ENNReal.ofReal M)
    (hc0 : ContinuousOn A0 (Set.Icc a b ×ˢ Set.univ))
    (hA0 : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      ∀ ht : MemLp (q t) 4 (volume : Measure V12Spatial),
      (fun x => A0 (t,x)) =ᵐ[volume]
      (v12_temporalCoulombClass
        (fun j k => v12_SL2Class volume j k (q t) ht)
        (v12_massComplexL2Class volume (q t) ht) : V12Spatial → ℂ))
    (hV : ∀ z, V z = -A0 z + ((‖v12_spacetimeHodge (Function.uncurry q) z‖^2 : ℝ) : ℂ) -
      (2 : ℂ) * ((‖Function.uncurry q z‖^2 : ℝ) : ℂ))
    (hd : ∀ t, t ∈ Set.Ioo a b → ∀ x, HasDerivAt (fun s => q s x) (dq t x) t)
    (hPDE : ∀ t, t ∈ Set.Ioo a b → ∀ x,
      let e := EuclideanSpace.basisFun (Fin 2) ℝ
      Complex.I • dq t x +
        (fderiv ℝ (fun y => fderiv ℝ (q t) y (e 0)) x (e 0) +
         fderiv ℝ (fun y => fderiv ℝ (q t) y (e 1)) x (e 1)) =
      (2 * Complex.I) •
        (v12_actualCoulombA (Function.uncurry q) 0 (t,x) • fderiv ℝ (q t) x (e 0) +
         v12_actualCoulombA (Function.uncurry q) 1 (t,x) • fderiv ℝ (q t) x (e 1)) +
      v12_zeroOrderProduct V (fun z => v12_WDensity (Function.uncurry q z))
        (Function.uncurry q) (t,x)) :
    let ext := v12_smoothSlabExtension a b (Function.uncurry q)
    let hm := v12_smoothSlabExtension_stronglyMeasurable a b (Function.uncurry q) hc
    let he4 := v12_smoothSlabExtension_memLp a b (Function.uncurry q) 4 h4
    let hEe := v12_smoothSlabExtension_energy a b (Function.uncurry q) M hE
    ∀ j, ∀ᵐ z ∂v12_slab_measure a b, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      Complex.I * fderiv ℝ (fun x => ext x j) z v12_timeDirection +
        (fderiv ℝ (fun x => fderiv ℝ (fun y => ext y j) x (v12_spatialDirection 0))
            z (v12_spatialDirection 0) +
         fderiv ℝ (fun x => fderiv ℝ (fun y => ext y j) x (v12_spatialDirection 1))
            z (v12_spatialDirection 1)) =
      (2 * Complex.I) *
        (v12_actualCoulombA ext 0 z * fderiv ℝ (fun x => ext x j) z (v12_spatialDirection 0) +
         v12_actualCoulombA ext 1 z * fderiv ℝ (fun x => ext x j) z (v12_spatialDirection 1)) +
      (v12_actualPotentialL2Class hHLS a b ext hm he4 M hEe z * ext z j +
        v12_WDensity (ext z) * star (ext z j)) := by
  let f := Function.uncurry q
  let ext := v12_smoothSlabExtension a b f
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hm := v12_smoothSlabExtension_stronglyMeasurable a b f hc
  have he4 := v12_smoothSlabExtension_memLp a b f 4 h4
  have hEe := v12_smoothSlabExtension_energy a b f M hE
  have ha := v12_original_A0_joint_representative a b f h4 A0 hc0 hA0
  have hv := v12_original_V_extended_representative hHLS a b f hc h4 M hEe A0 V ha hV
  intro j
  have hje : Set.EqOn (fun z => ext z j) (fun z => f z j) U :=
    fun z hz => congrArg (fun u : V12Field => u j) (v12_smoothSlabExtension_eqOn_interior a b f hz)
  have hjd := v12_open_eqOn_fderiv U hU _ _ hje
  have hjdd (v : V12Spacetime) := v12_open_eqOn_second_directional_derivative U hU _ _ hje v v
  filter_upwards [hv] with z hzV
  intro hz
  have hqz := v12_smoothSlabExtension_eqOn_interior a b f hz
  have hAz (k : Fin 2) := v12_smoothSlabExtension_A_eqOn_interior a b f k hz
  rw [hjd hz, hjdd (v12_spatialDirection 0) hz, hjdd (v12_spatialDirection 1) hz,
    hAz 0, hAz 1, hqz, ← hzV]
  exact v12_original_curried_scalar_PDE a b q dq (v12_actualCoulombA f) V
    (fun z => v12_WDensity (f z)) hs z.1 hz z.2 (hd z.1 hz z.2) (hPDE z.1 hz z.2) j

#print axioms v12_original_extended_scalar_PDE
end SMScattering.W20Full
