import lean.v12.V12_ZDGOriginalTimeSourceFromMZ
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! The compact spatial pairing of the original vector field satisfies its
actual time integral identity. All source integrability and identification
premises of the internal FTC lemma are discharged from the original PDE and
MZ assumptions; Q's derivative is required continuous only in the interior.
Pending CI; source-Lp/cutoff matching remains downstream. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

noncomputable def v12_originalVectorTestSource
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) (ψ : V12Spatial → ℂ) (t : ℝ) : V12Field :=
  WithLp.toLp 2 (fun j => v12_scalarSpatialTestSource (fun z => q z j)
    (v12_actualCoulombA q) (v12_originalScalarSource a b q hq j) ψ t)

theorem v12_original_compact_test_time_identity
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
    (hPDE : ∀ j, V12OriginalScalarDistributionalPDE a b (fun z => q z j)
      (v12_actualCoulombA q) (v12_originalScalarSource a b q hq j)
      v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1))
    (ψ : V12Spatial → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    {s t : ℝ} (hsi : s ∈ Set.Icc a b) (hti : t ∈ Set.Icc a b) (hst : s ≤ t) :
    (∫ x : V12Spatial, ψ x • q (t,x)) - (∫ x : V12Spatial, ψ x • q (s,x)) =
      ∫ τ in s..t, v12_originalVectorTestSource a b q hq ψ τ := by
  let U : Set V12Spacetime := Prod.fst ⁻¹' Set.Ioo a b
  have hU : IsOpen U := isOpen_Ioo.preimage
    (continuous_fst : Continuous (Prod.fst : V12Spacetime → ℝ))
  have hdiff (τ : ℝ) (hτ : τ ∈ Set.Ioo a b) (x : V12Spatial) :
      DifferentiableAt ℝ q (τ,x) :=
    (hs.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hτ)
  have hd : ContinuousOn (fun z => fderiv ℝ q z v12_timeDirection) U :=
    (hs.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hder (τ : ℝ) (hτ : τ ∈ Set.Ioo a b) (x : V12Spatial) :
      HasDerivAt (fun σ => q (σ,x)) (fderiv ℝ q (τ,x) v12_timeDirection) τ := by
    have hi : HasDerivAt (fun σ : ℝ => (σ,x)) (1,0) τ :=
      (hasDerivAt_id' τ).prodMk (hasDerivAt_const τ x)
    exact (hdiff τ hτ x).hasFDerivAt.comp_hasDerivAt τ hi
  have hS (j : Fin 2) := v12_original_time_source_from_MZ hHLS a b q hc hs hq M hE
    hdiv j (hPDE j) ψ hψ hcψ
  have hG : Integrable (v12_originalVectorTestSource a b q hq ψ)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
    apply Integrable.of_eval_piLp
    intro j
    exact (hS j).1
  have hsource : (fun τ => ∫ x : V12Spatial, ψ x • fderiv ℝ q (τ,x) v12_timeDirection)
      =ᵐ[(volume : Measure ℝ).restrict (Set.Icc a b)]
        v12_originalVectorTestSource a b q hq ψ := by
    have hI : ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b), τ ∈ Set.Ioo a b := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [ae_all_iff.mpr (fun j => (hS j).2), hI] with τ hτ hτI
    have hslice : Continuous (fun x : V12Spatial => fderiv ℝ q (τ,x) v12_timeDirection) := by
      have hm : Set.MapsTo (fun x : V12Spatial => (τ,x)) Set.univ U := fun _ _ => hτI
      simpa only [continuousOn_univ, Function.comp_def] using
        hd.comp (continuous_const.prodMk continuous_id).continuousOn hm
    have hi : Integrable (fun x : V12Spatial => ψ x • fderiv ℝ q (τ,x) v12_timeDirection) :=
      (hψ.continuous.smul hslice).integrable_of_hasCompactSupport hcψ.smul_right
    apply PiLp.ext
    intro j
    rw [eval_integral_piLp (fun i => hi.eval_piLp i) j]
    change (∫ x : V12Spatial, ψ x * (fderiv ℝ q (τ,x) v12_timeDirection) j) = _
    change _ = v12_scalarSpatialTestSource (fun z => q z j)
      (v12_actualCoulombA q) (v12_originalScalarSource a b q hq j) ψ τ
    rw [← hτ j]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [v12_component_fderiv q (τ,x) v12_timeDirection j (hdiff τ hτI x)]
    exact mul_comm _ _
  apply v12_compact_pairing_time_identity_of_integrable_source a b ψ hψ.continuous hcψ
    (fun τ x => q (τ,x)) (fun τ x => fderiv ℝ q (τ,x) v12_timeDirection)
    (v12_originalVectorTestSource a b q hq ψ) hc _ hder hG hsource hsi hti hst
  exact hd.mono (fun z hz => hz.1)

#print axioms v12_original_compact_test_time_identity
end SMScattering.W20Full
