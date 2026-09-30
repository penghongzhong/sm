import lean.v12.V12_YVGlobalCutoffRepresentative
import lean.v12.V12_YTBochnerSectionNorm

/-!
The actual spatial Fourier cutoff is realized on spacetime and every local
cylinder using its SAME continuous convolution representative. Neither the
joint measurability nor the local representative equality is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SMScattering.W20Full

open MeasureTheory
open scoped ENNReal

theorem v12_spacetime_cutoff_memLp
    (μ : Measure ℝ) [SFinite μ]
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (Q : ℝ → V12SpatialL2) (hQ : MemLp Q 2 μ) :
    let r : V12Spacetime → V12Field := fun z =>
      v12_L2ConvolutionRep (v12_cutoffKernelL2 p hpc hps N) (Q z.1) z.2
    MemLp r 2 (μ.prod (volume : Measure V12Spatial)) ∧
      eLpNorm r 2 (μ.prod (volume : Measure V12Spatial)) ≤
        ENNReal.ofReal ‖v12_cutoffN p hpc hps N‖ * eLpNorm Q 2 μ := by
  dsimp only
  let L := v12_L2ConvolutionBCFCLM (v12_cutoffKernelL2 p hpc hps N)
  let r : V12Spacetime → V12Field := fun z => L (Q z.1) z.2
  have hcurve : AEStronglyMeasurable (fun t => L (Q t)) μ :=
    L.continuous.comp_aestronglyMeasurable hQ.aestronglyMeasurable
  have hprod : AEStronglyMeasurable (fun z : V12Spacetime => L (Q z.1))
      (μ.prod (volume : Measure V12Spatial)) := hcurve.comp_fst
  have hx : AEStronglyMeasurable (fun z : V12Spacetime => z.2)
      (μ.prod (volume : Measure V12Spatial)) := measurable_snd.aestronglyMeasurable
  have heval : Continuous (fun z : (BoundedContinuousFunction V12Spatial V12Field) × V12Spatial =>
      z.1 z.2) := continuous_eval
  have hr : AEStronglyMeasurable r (μ.prod (volume : Measure V12Spatial)) :=
    heval.comp_aestronglyMeasurable (hprod.prodMk hx)
  let P := v12_cutoffN p hpc hps N
  have hPQ : MemLp (fun t => P (Q t)) 2 μ := hQ.continuousLinearMap_comp P
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hrep : ∀ᵐ t ∂μ, (P (Q t) : V12Spatial → V12Field) =ᵐ[volume] fun y => r (t,y) :=
    Filter.Eventually.of_forall (fun t => v12_cutoffN_ae_continuousRep p hpc hps N (Q t))
  have hn := v12_eLpNorm_sections_eq_spacetime μ 2 r hr (fun t => P (Q t)) hrep
  refine ⟨hn.symm.trans_lt hPQ, ?_⟩
  change eLpNorm r 2 (μ.prod (volume : Measure V12Spatial)) ≤ _
  rw [← hn]
  exact v12_eLpNorm_compCLM_le μ P Q 2 hQ.aestronglyMeasurable

/-- Global and local L2 representatives of the actual cutoff are constructed. -/
theorem v12_exists_spacetime_cutoff_realization
    (a b : ℝ)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b))) :
    ∃ v : V12SlabL2 a b,
      ((v : V12Spacetime → V12Field) =ᵐ[v12_slab_measure a b]
        fun z => v12_L2ConvolutionRep (v12_cutoffKernelL2 p hpc hps N) (Q z.1) z.2) ∧
      ∀ R, (v12_localize a b R v : V12Spacetime → V12Field)
        =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)]
        fun z => v12_L2ConvolutionRep (v12_cutoffKernelL2 p hpc hps N) (Q z.1) z.2 := by
  have hQ2 : MemLp Q 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
    hQ.mono_exponent le_top
  have hraw := (v12_spacetime_cutoff_memLp
    ((volume : Measure ℝ).restrict (Set.Icc a b)) p hpc hps N Q hQ2).1
  let r : V12Spacetime → V12Field := fun z =>
    v12_L2ConvolutionRep (v12_cutoffKernelL2 p hpc hps N) (Q z.1) z.2
  let v : V12SlabL2 a b := hraw.toLp r
  have hv : (v : V12Spacetime → V12Field) =ᵐ[v12_slab_measure a b] r := hraw.coeFn_toLp
  refine ⟨v, hv, ?_⟩
  intro R
  exact (v12_localize_coeFn a b R v).trans (ae_restrict_of_ae hv)

/-- The actual slab cutoff class; its representative is fixed by the convolution. -/
noncomputable def v12_spacetimeCutoffClass
    (a b : ℝ)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b))) : V12SlabL2 a b :=
  Classical.choose (v12_exists_spacetime_cutoff_realization a b p hpc hps N Q hQ)

theorem v12_spacetimeCutoffClass_ae
    (a b : ℝ)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b))) :
    (v12_spacetimeCutoffClass a b p hpc hps N Q hQ : V12Spacetime → V12Field)
      =ᵐ[v12_slab_measure a b] fun z =>
        v12_L2ConvolutionRep (v12_cutoffKernelL2 p hpc hps N) (Q z.1) z.2 :=
  (Classical.choose_spec
    (v12_exists_spacetime_cutoff_realization a b p hpc hps N Q hQ)).1

theorem v12_spacetimeCutoffClass_norm_le
    (a b : ℝ)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b))) :
    ‖v12_spacetimeCutoffClass a b p hpc hps N Q hQ‖ ≤
      ‖v12_cutoffN p hpc hps N‖ *
        (eLpNorm Q 2 ((volume : Measure ℝ).restrict (Set.Icc a b))).toReal := by
  let μ : Measure ℝ := volume.restrict (Set.Icc a b)
  have hQ2 : MemLp Q 2 μ := hQ.mono_exponent le_top
  have hfinite := hQ2.eLpNorm_ne_top
  have hbound := (v12_spacetime_cutoff_memLp μ p hpc hps N Q hQ2).2
  rw [Lp.norm_def, eLpNorm_congr_ae (v12_spacetimeCutoffClass_ae a b p hpc hps N Q hQ)]
  have h := ENNReal.toReal_mono
    (show ENNReal.ofReal ‖v12_cutoffN p hpc hps N‖ * eLpNorm Q 2 μ ≠ ∞ by finiteness)
    hbound
  simpa only [v12_slab_measure, μ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] using h

#print axioms v12_spacetimeCutoffClass_ae
#print axioms v12_spacetimeCutoffClass_norm_le

#print axioms v12_spacetime_cutoff_memLp
#print axioms v12_exists_spacetime_cutoff_realization

end SMScattering.W20Full
