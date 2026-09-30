import lean.v12.V12_YIYoungConvolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Identify the constructed Young L^(4/3) class with the actual singular
truncated-kernel convolution, using finite-measure tests and Fubini. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open MeasureTheory
open scoped Topology ENNReal
local instance : Fact (1 ≤ (4 : ℝ≥0∞) / 3) := ⟨v12_one_le_fourThirds_ENNReal⟩

noncomputable def v12_hodgeSetIntegralCLM
    (s : Set V12Spatial) (hs : MeasurableSet s) (hfin : (volume : Measure V12Spatial) s ≠ ∞) :
    Lp V12Spatial ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) →L[ℝ] V12Spatial :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing volume 4 ((4 : ℝ≥0∞) / 3)
    (indicatorConstLp 4 hs hfin (1 : ℝ))

theorem v12_hodgeSetIntegralCLM_apply
    (s : Set V12Spatial) (hs : MeasurableSet s) (hfin : (volume : Measure V12Spatial) s ≠ ∞)
    (f : Lp V12Spatial ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial)) :
    v12_hodgeSetIntegralCLM s hs hfin f = ∫ x in s, f x := by
  rw [v12_hodgeSetIntegralCLM, ContinuousLinearMap.lpPairing_eq_integral]
  calc
    (∫ x, (ContinuousLinearMap.lsmul ℝ ℝ) (indicatorConstLp 4 hs hfin (1 : ℝ) x) (f x)) =
        ∫ x, s.indicator (fun x => f x) x := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 4) (hs := hs) (hμs := hfin) (c := (1 : ℝ))] with x hx
      simp only [ContinuousLinearMap.lsmul_apply, hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = _ := integral_indicator hs

theorem v12_translateHodgeKernel_raw_ae (R : ℝ) (y : V12Spatial) :
    (v12_translateKernel ((4 : ℝ≥0∞) / 3) (v12_truncatedHodgeKernelClass R) y :
      V12Spatial → V12Spatial) =ᵐ[volume] fun x =>
      ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel) (x-y) := by
  have ht := Lp.coeFn_compMeasurePreserving (v12_truncatedHodgeKernelClass R)
    (v12_subRight_measurePreserving y)
  have hk := (v12_subRight_measurePreserving y).quasiMeasurePreserving.ae
    (v12_truncatedHodgeKernelClass_ae R)
  filter_upwards [ht, hk] with x hx hkx
  exact hx.trans hkx

theorem v12_youngHodge_setIntegral_eq_raw
    (R : ℝ) (B : V12Spatial → ℝ) (hB : Integrable B (volume : Measure V12Spatial))
    (s : Set V12Spatial) (hs : MeasurableSet s) (hfin : (volume : Measure V12Spatial) s ≠ ∞) :
    (∫ x in s, v12_youngConvolutionClass ((4 : ℝ≥0∞) / 3) (v12_truncatedHodgeKernelClass R) B x) =
      ∫ x in s, v12_rawNearHodge R B x := by
  let K := v12_truncatedHodgeKernelClass R
  let L := v12_hodgeSetIntegralCLM s hs hfin
  have hi := (v12_youngConvolutionClass_integrable_bound _ (by finiteness) K B hB).1
  have hswap := hB.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ)
    (v12_truncatedHodgeKernel_integrable R)
  have hswapS : Integrable (fun z : V12Spatial × V12Spatial => B z.2 •
      ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel) (z.1-z.2))
      (((volume : Measure V12Spatial).restrict s).prod (volume : Measure V12Spatial)) :=
    hswap.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  calc
    (∫ x in s, v12_youngConvolutionClass ((4 : ℝ≥0∞) / 3) K B x) =
        L (v12_youngConvolutionClass ((4 : ℝ≥0∞) / 3) K B) :=
      (v12_hodgeSetIntegralCLM_apply s hs hfin _).symm
    _ = ∫ y, L (B y • v12_translateKernel ((4 : ℝ≥0∞) / 3) K y) :=
      (L.integral_comp_comm hi).symm
    _ = ∫ y, ∫ x in s, B y •
        ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel) (x-y) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change L (B y • v12_translateKernel ((4 : ℝ≥0∞) / 3) K y) =
        ∫ x in s, B y • ((Metric.ball (0 : V12Spatial) R).indicator v12_hodgeKernel) (x-y)
      rw [map_smul]
      change B y • (v12_hodgeSetIntegralCLM s hs hfin
        (v12_translateKernel ((4 : ℝ≥0∞) / 3) K y)) = _
      rw [v12_hodgeSetIntegralCLM_apply, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [(v12_translateHodgeKernel_raw_ae R y).restrict] with x hx
      rw [hx]
    _ = ∫ x in s, v12_rawNearHodge R B x := by
      exact (integral_integral_swap hswapS).symm

theorem v12_youngHodge_raw_ae
    (R : ℝ) (B : V12Spatial → ℝ) (hB : Integrable B (volume : Measure V12Spatial)) :
    (v12_youngConvolutionClass ((4 : ℝ≥0∞) / 3) (v12_truncatedHodgeKernelClass R) B :
      V12Spatial → V12Spatial) =ᵐ[volume] v12_rawNearHodge R B := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hfin
    letI : IsFiniteMeasure ((volume : Measure V12Spatial).restrict s) :=
      ⟨by simpa using hfin⟩
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp (v12_youngConvolutionClass ((4 : ℝ≥0∞) / 3)
        (v12_truncatedHodgeKernelClass R) B)).restrict s |>.mono_exponent v12_one_le_fourThirds_ENNReal)
  · intro s hs hfin
    exact (v12_rawNearHodge_integrable R B hB).restrict
  · intro s hs hfin
    exact v12_youngHodge_setIntegral_eq_raw R B hB s hs hfin.ne


/-- Young's inequality for the actual near Hodge integral, not merely a
separately constructed Banach-space object. -/
theorem v12_rawNearHodge_memLp_bound
    (R : ℝ) (B : V12Spatial → ℝ) (hB : Integrable B (volume : Measure V12Spatial)) :
    MemLp (v12_rawNearHodge R B) ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) ∧
      (eLpNorm (v12_rawNearHodge R B) ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial)).toReal ≤
        (∫ y, ‖B y‖) * ‖v12_truncatedHodgeKernelClass R‖ := by
  have hae := v12_youngHodge_raw_ae R B hB
  have hm : MemLp (v12_rawNearHodge R B) ((4 : ℝ≥0∞) / 3) (volume : Measure V12Spatial) := by
    change eLpNorm (v12_rawNearHodge R B) ((4 : ℝ≥0∞) / 3) volume < ∞
    rw [← eLpNorm_congr_ae hae]
    exact Lp.memLp _
  refine ⟨hm, ?_⟩
  have hn := v12_truncatedHodge_young_bound R B hB
  rwa [Lp.norm_def, eLpNorm_congr_ae hae] at hn

#print axioms v12_rawNearHodge_memLp_bound
#print axioms v12_youngHodge_setIntegral_eq_raw
#print axioms v12_youngHodge_raw_ae
end SMScattering.W20Full
