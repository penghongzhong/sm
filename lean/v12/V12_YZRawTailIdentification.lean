import lean.v12.V12_YWSpacetimeCutoffRealization
import lean.v12.V12_YXRawSlabRealization
import lean.v12.V12_KernelConvolutionIdentity

/-!
The canonical slab cutoff tail is exactly the raw Fourier-convolution tail.
This removes any dependence of the frequency-tightness hypothesis on a choice
of time-Lp representatives. No tail bound or tightness conclusion is proved
or assumed here: only the exact same-field identity is established.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_rawCutoffField
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (q : ℝ → V12Spatial → V12Field) (z : V12Spacetime) : V12Field :=
  ∫ y : V12Spatial, v12_cutoffKernelSchwartz p hpc hps N (z.2-y) • q z.1 y

noncomputable def v12_rawFrequencyTail
    (a b : ℝ) (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (q : ℝ → V12Spatial → V12Field) : ℝ :=
  (eLpNorm (fun z : V12Spacetime => q z.1 z.2 - v12_rawCutoffField p hpc hps N q z)
    2 (v12_slab_measure a b)).toReal

theorem v12_spacetimeCutoffClass_raw_ae
    (a b : ℝ) (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (q : ℝ → V12Spatial → V12Field) (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hrep : ∀ t ∈ Set.Icc a b, (Q t : V12Spatial → V12Field) =ᵐ[volume] q t) :
    (v12_spacetimeCutoffClass a b p hpc hps N Q hQ : V12Spacetime → V12Field)
      =ᵐ[v12_slab_measure a b] v12_rawCutoffField p hpc hps N q := by
  have ht : ∀ᵐ z ∂v12_slab_measure a b, z.1 ∈ Set.Icc a b := by
    rw [v12_slab_measure, Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod MeasurableSet.univ)] with z hz
    exact hz.1
  filter_upwards [v12_spacetimeCutoffClass_ae a b p hpc hps N Q hQ, ht] with z hz hzt
  rw [hz]
  exact v12_L2ConvolutionRep_eq_integral_of_ae
    (v12_cutoffKernelL2 p hpc hps N) (Q z.1)
    (v12_cutoffKernelSchwartz p hpc hps N) (q z.1)
    ((v12_cutoffKernelSchwartz p hpc hps N).coeFn_toLp 2 (volume : Measure V12Spatial))
    (hrep z.1 hzt) z.2

theorem v12_rawFrequencyTail_eq_class_norm
    (a b : ℝ) (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (q : ℝ → V12Spatial → V12Field)
    (hq : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (Q : ℝ → V12SpatialL2)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hrep : ∀ t ∈ Set.Icc a b, (Q t : V12Spatial → V12Field) =ᵐ[volume] q t) :
    v12_rawFrequencyTail a b p hpc hps N q =
      ‖v12_rawSlabClass a b q hq Q hQ hrep - v12_spacetimeCutoffClass a b p hpc hps N Q hQ‖ := by
  rw [Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (v12_rawSlabClass a b q hq Q hQ hrep)
      (v12_spacetimeCutoffClass a b p hpc hps N Q hQ),
    v12_rawSlabClass_ae a b q hq Q hQ hrep,
    v12_spacetimeCutoffClass_raw_ae a b p hpc hps N q Q hQ hrep] with z hsub hraw hcut
  change q z.1 z.2 - v12_rawCutoffField p hpc hps N q z = _
  rw [hsub, Pi.sub_apply, hraw, hcut]
  rfl

#print axioms v12_spacetimeCutoffClass_raw_ae
#print axioms v12_rawFrequencyTail_eq_class_norm
end SMScattering.W20Full
