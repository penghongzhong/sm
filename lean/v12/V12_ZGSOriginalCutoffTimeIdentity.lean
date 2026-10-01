import lean.v12.V12_ZFSOriginalTestTimeIdentity
import lean.v12.V12_ZGCutoffIdentityFromRawPDE

/-! Removal of the concrete compact spatial tests starting with the original
advective distributional equation, weak Coulomb divergence and same-field
Lp representatives. Test identities, source limit, endpoint limit and BCF
identity are proved internally. Pending CI; representatives and uniform MZ
budgets are instantiated in the final compactness application. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace SMScattering.W20Full
open Filter MeasureTheory LineDeriv Laplacian
open scoped Topology ENNReal ContDiff

theorem v12_cutoff_time_identity_from_original_distribution
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
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hQr : ∀ τ ∈ Set.Icc a b, (Q τ : V12Spatial → V12Field) =ᵐ[volume] (fun x => q (τ,x)))
    (hFr : ∀ j, ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (F j τ : V12Spatial → V12Field) =ᵐ[volume]
        (fun x => v12_driftProduct (v12_actualCoulombA q) q j (τ,x)))
    (hGr : ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (G τ : V12Spatial → V12Field) =ᵐ[volume]
        (fun x => v12_zeroOrderProduct (v12_originalReconstructedPotential a b q hq)
          (fun z => v12_WDensity (q z)) q (τ,x)))
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hF : ∀ j, MemLp (F j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hG : MemLp G ((4 : ℝ≥0∞)/3) ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (χ : SchwartzMap V12Spatial ℝ) (hcχ : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    {s t : ℝ} (hsi : s ∈ Set.Icc a b) (hti : t ∈ Set.Icc a b) (hst : s ≤ t) :
    v12_cutoffTimeField p hpc hps N Q t - v12_cutoffTimeField p hpc hps N Q s =
      ∫ τ in s..t, v12_cutoffTimeSource p hpc hps N Q F G τ := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc s t)
  have hsub : μ ≤ (volume : Measure ℝ).restrict (Set.Icc a b) := by
    apply Measure.restrict_mono _ le_rfl
    intro τ hτ
    exact ⟨hsi.1.trans hτ.1.le, hτ.2.trans hti.2⟩
  have hQμ := MemLp.mono_measure hsub hQ
  have hFμ := fun j => MemLp.mono_measure hsub (hF j)
  have hGμ := MemLp.mono_measure hsub hG
  let S := v12_cutoffTimeSource p hpc hps N Q F G
  have hSLp : MemLp S ((4 : ℝ≥0∞) / 3) μ :=
    v12_cutoffTimeSource_memLp p hpc hps N μ Q F G hQμ hFμ hGμ
  have hSint : IntervalIntegrable S volume s t := by
    apply intervalIntegrable_iff.mpr
    rw [Set.uIoc_of_le hst]
    exact memLp_one_iff_integrable.mp (hSLp.mono_exponent v12_one_le_fourThirds_ENNReal)
  apply v12_BCF_time_identity_of_pointwise
    (v12_cutoffTimeField p hpc hps N Q) S s t hSint
  intro x
  let k := v12_cutoffKernelSchwartz p hpc hps N
  let Ψ : ℕ → SchwartzMap V12Spatial ℂ := fun R =>
    v12_compactSpatialTestSchwartz χ hcχ (χ.smooth (⊤ : ℕ∞)) k R x
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let vR : ℕ → ℝ → V12Field := fun R τ => ∫ y : V12Spatial, Ψ R y • q (τ,y)
  let gR : ℕ → ℝ → V12Field := fun R =>
    v12_testSourceFromLpKernels ((Δ (Ψ R)).toLp 2 (volume : Measure V12Spatial))
      (fun j => (∂_{e j} (Ψ R)).toLp 2 (volume : Measure V12Spatial))
      ((Ψ R).toLp 4 (volume : Measure V12Spatial)) Q F G
  have htest : ∀ R, IntervalIntegrable (gR R) volume s t ∧
      vR R t - vR R s = ∫ τ in s..t, gR R τ := by
    intro R
    exact v12_original_test_Lp_time_identity hHLS a b q hc hs hq M hE hdiv hPDE
      (Ψ R) (v12_compactSpatialTest_compactSupport χ hcχ k R x)
      Q F G hQr hFr hGr hQ hF hG hsi hti hst
  have hend : ∀ τ ∈ Set.Icc a b, Tendsto (fun R => vR R τ) atTop
      (𝓝 (v12_cutoffTimeField p hpc hps N Q τ x)) := by
    intro τ hτ
    have heq : ∀ R, vR R τ =
        ∫ y : V12Spatial, v12_compactSpatialTest χ k R x y • (Q τ : V12Spatial → V12Field) y := by
      intro R
      apply integral_congr_ae
      filter_upwards [hQr τ hτ] with y hy
      change v12_compactSpatialTest χ k R x y • q (τ,y) = _
      rw [hy]
    simp_rw [heq]
    exact v12_compactSpatialTest_endpoint_to_BCF χ χ.continuous hχ0 hχb k x (Q τ)
  have hSx : IntervalIntegrable (fun τ => S τ x) volume s t := by
    constructor
    · exact (BoundedContinuousFunction.evalCLM ℝ x).integrable_comp hSint.1
    · exact (BoundedContinuousFunction.evalCLM ℝ x).integrable_comp hSint.2
  have hlim : Tendsto (fun R => ∫ τ in Set.Ioc s t, ‖gR R τ - S τ x‖) atTop (𝓝 0) :=
    v12_actual_test_fullSource_to_cutoff_L1_tendsto μ χ hcχ hχ0 hχb
      p hpc hps N x Q F G hQμ hFμ hGμ
  exact v12_time_identity_of_test_limit
    (fun τ => v12_cutoffTimeField p hpc hps N Q τ x) (fun τ => S τ x)
    vR gR s t hst hSx (fun R => (htest R).1) (fun R => (htest R).2)
    (hend s hsi) (hend t hti) hlim

#print axioms v12_cutoff_time_identity_from_original_distribution
end SMScattering.W20Full
