import lean.v12.V12_ZDFOriginalTimeSourceIdentification
import lean.v12.V12_YZZKTOriginalDistributionExtension
import lean.v12.V12_YWWOriginalComponentPDE

/-! Instantiate the weak-time source theorem on the ORIGINAL closed-slab
field. Every coefficient/source local-integrability premise is derived from
the same field's L4 membership, energy bound, and actual Hodge/Riesz formulas.
No global smooth extension, A0 continuity, source budget, hIntegral or hCompact
is a premise. Pending actual CI and downstream vector/cutoff application. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_original_time_source_from_MZ
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hc : ContinuousOn q (Set.Icc a b ×ˢ Set.univ))
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q (Prod.fst ⁻¹' Set.Ioo a b))
    (hq : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hdiv : ∀ φ : V12Spacetime → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, v12_actualCoulombA q 0 z * fderiv ℝ φ z (v12_spatialDirection 0)
        ∂v12_slab_measure a b) +
      (∫ z, v12_actualCoulombA q 1 z * fderiv ℝ φ z (v12_spatialDirection 1)
        ∂v12_slab_measure a b) = 0)
    (j : Fin 2)
    (hPDE : V12OriginalScalarDistributionalPDE a b (fun z => q z j)
      (v12_actualCoulombA q) (v12_originalScalarSource a b q hq j)
      v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1))
    (ψ : V12Spatial → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (v12_scalarSpatialTestSource (fun z => q z j)
      (v12_actualCoulombA q) (v12_originalScalarSource a b q hq j) ψ)
        ((volume : Measure ℝ).restrict (Set.Icc a b)) ∧
    (fun t => ∫ x : V12Spatial, fderiv ℝ (fun z => q z j) (t,x) v12_timeDirection * ψ x)
      =ᵐ[(volume : Measure ℝ).restrict (Set.Icc a b)]
        v12_scalarSpatialTestSource (fun z => q z j)
          (v12_actualCoulombA q) (v12_originalScalarSource a b q hq j) ψ := by
  let μ := v12_slab_measure a b
  let ext := v12_smoothSlabExtension a b q
  have hm := v12_smoothSlabExtension_stronglyMeasurable a b q hc
  have he4 := v12_smoothSlabExtension_memLp a b q 4 hq
  have heE := v12_smoothSlabExtension_energy a b q M hE
  obtain ⟨CA, hCA, hAB⟩ := v12_actual_hodge_spacetime_MZ hHLS
  have hH4 : MemLp (v12_spacetimeHodge ext) 4 μ :=
    (hAB a b ext hm he4 (ENNReal.ofReal M) (by finiteness) heE).1
  have hA4 (k : Fin 2) : MemLp (v12_actualCoulombA q k) 4 μ := by
    have h4 : MemLp (v12_actualCoulombA ext k) 4 μ :=
      (v12_actualCoulombA_eLpNorm_le μ ext hm 4 k).trans_lt hH4
    apply h4.ae_eq
    filter_upwards [v12_smoothSlabExtension_Hodge_ae a b q] with z hz
    simp only [v12_actualCoulombA, ext, hz]
  have hqj : MemLp (fun z => q z j) 4 μ :=
    (v12_raw_component_eLpNorm_le μ 4 q hq.aestronglyMeasurable j).trans_lt hq
  letI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := v12_holderTriple_four_four_two
  have hAf (k : Fin 2) : MemLp (fun z => v12_actualCoulombA q k z * q z j) 2 μ :=
    (hA4 k).mul hqj
  have hg : MemLp (v12_originalScalarSource a b q hq j) ((4 : ℝ≥0∞)/3) μ :=
    (v12_actualScalarZeroOrder_memLp hHLS a b ext hm he4 M heE j).ae_eq
      (Filter.EventuallyEq.symm (v12_originalScalarSource_extension_ae hHLS a b q hc hq M hE j))
  have hp : (1 : ℝ≥0∞) ≤ 4 / 3 := by
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).mpr
    norm_num
  have hfL := hqj.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hAfL (k : Fin 2) := (hAf k).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨v12_scalarSpatialTestSource_integrable a b _ _ _ ψ
    hfL hAfL (hg.locallyIntegrable hp) hψ hcψ, ?_⟩
  exact v12_original_PDE_time_source_ae a b _ _ _ ψ
    (v12_component_contDiffOn a b q j hs)
    (fun k => (hA4 k).locallyIntegrable (by norm_num)) hg hfL hAfL hψ hcψ hdiv hPDE

#print axioms v12_original_time_source_from_MZ
end SMScattering.W20Full
