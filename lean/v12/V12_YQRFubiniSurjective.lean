import lean.v12.V12_YQFubiniIsometry
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-! Surjectivity of the actual L2 Fubini isometry by Mathlib's proved
Lp simple-function density, giving measurable raw representatives for all
Bochner L2 outputs. No extra external foundation is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_fubini_indicator_in_range (μ : Measure ℝ) [SFinite μ]
    (s : Set ℝ) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : V12ScalarL2) :
    ∃ f : Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)),
      v12_fubiniL2Isometry μ f = indicatorConstLp 2 hs hμs c := by
  let cm := Lp.aestronglyMeasurable c
  let cr := cm.mk (c : V12Spatial → ℂ)
  have hcr : StronglyMeasurable cr := cm.stronglyMeasurable_mk
  have hcr2 : MemLp cr 2 (volume : Measure V12Spatial) := by
    change eLpNorm cr 2 volume < ∞
    rw [← eLpNorm_congr_ae cm.ae_eq_mk]
    exact Lp.memLp c
  let raw : V12Spacetime → ℂ := (Prod.fst ⁻¹' s).indicator (fun z => cr z.2)
  have hraw : StronglyMeasurable raw :=
    (hcr.comp_measurable measurable_snd).indicator (hs.preimage measurable_fst)
  have ht : Integrable (s.indicator (fun _ : ℝ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hs).2 (integrableOn_const hμs)
  have hx : Integrable (fun x => ‖cr x‖ ^ (2 : ℕ)) (volume : Measure V12Spatial) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      hcr2.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
  have hr2 : MemLp raw 2 (μ.prod (volume : Measure V12Spatial)) := by
    apply (integrable_norm_rpow_iff hraw.aestronglyMeasurable
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
    convert ht.mul_prod hx using 1
    funext z
    by_cases hz : z.1 ∈ s <;>
      simp [raw, Set.indicator_apply, hz, Real.rpow_two]
  let f := hr2.toLp raw
  refine ⟨f, ?_⟩
  apply Lp.ext_iff.mpr
  have htarget : (indicatorConstLp 2 hs hμs c : ℝ → V12ScalarL2) =ᵐ[μ]
      s.indicator (fun _ => c) := indicatorConstLp_coeFn
  filter_upwards [v12_fubiniMap_sections μ f,
    Measure.ae_ae_of_ae_prod hr2.coeFn_toLp, htarget] with t hft hrt hct
  change v12_fubiniMap μ f t = (indicatorConstLp 2 hs hμs c) t
  rw [hct]
  by_cases htS : t ∈ s
  · rw [Set.indicator_of_mem htS]
    apply Lp.ext_iff.mpr
    filter_upwards [hft, hrt, cm.ae_eq_mk] with x hfx hrx hcx
    change f (t,x) = raw (t,x) at hrx
    rw [hfx, hrx]
    simpa only [raw, Set.indicator_of_mem (show (t,x) ∈ Prod.fst ⁻¹' s from htS)] using hcx.symm
  · rw [Set.indicator_of_notMem htS]
    apply Lp.ext_iff.mpr
    filter_upwards [hft, hrt, Lp.coeFn_zero (E := ℂ) (p := 2)
      (μ := (volume : Measure V12Spatial))] with x hfx hrx h0
    change f (t,x) = raw (t,x) at hrx
    rw [hfx, hrx, h0]
    simp only [raw, Set.indicator_of_notMem (show (t,x) ∉ Prod.fst ⁻¹' s from htS), Pi.zero_apply]

theorem v12_fubiniL2Isometry_surjective (μ : Measure ℝ) [SFinite μ] :
    Function.Surjective (v12_fubiniL2Isometry μ) := by
  intro F
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (motive := fun g => g ∈ Set.range (v12_fubiniL2Isometry μ)) _ _ _ F
  · intro c s hs hμs
    exact v12_fubini_indicator_in_range μ s hs hμs.ne c
  · intro f g hf hg hdis hfR hgR
    obtain ⟨x, hx⟩ := hfR
    obtain ⟨y, hy⟩ := hgR
    exact ⟨x+y, by rw [map_add, hx, hy]⟩
  · exact (v12_fubiniL2Isometry μ).isometry.antilipschitz.isClosed_range
      (v12_fubiniL2Isometry μ).isometry.uniformContinuous

noncomputable def v12_fubiniL2Equiv (μ : Measure ℝ) [SFinite μ] :
    Lp ℂ 2 (μ.prod (volume : Measure V12Spatial)) ≃ₗᵢ[ℂ] Lp V12ScalarL2 2 μ :=
  LinearIsometryEquiv.ofSurjective (v12_fubiniL2Isometry μ) (v12_fubiniL2Isometry_surjective μ)

#print axioms v12_fubini_indicator_in_range
#print axioms v12_fubiniL2Isometry_surjective
#print axioms v12_fubiniL2Equiv
end SMScattering.W20Full
