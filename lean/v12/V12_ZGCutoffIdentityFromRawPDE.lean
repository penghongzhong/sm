import lean.v12.V12_ZFActualTestPDETimeIdentity

/-!
Removal of the concrete compact spatial tests. The actual cutoff BCF time
identity follows from the raw smooth PDE, exact same-field representatives
and time-Lp hypotheses. No hIntegral, hFTC, derivative-kernel limit or
source-limit hypothesis is accepted by this theorem.
Hodge reconstruction and the original M/Z coefficient bounds remain upstream.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SMScattering.W20Full

open Filter MeasureTheory LineDeriv Laplacian
open scoped Topology ENNReal ContDiff

theorem v12_cutoff_time_identity_from_raw_pde
    (a b : ℝ)
    (χ : SchwartzMap V12Spatial ℝ) (hc : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (q dq g : ℝ → V12Spatial → V12Field)
    (f : Fin 2 → ℝ → V12Spatial → V12Field)
    (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
    (G : ℝ → V12SpatialLFourThirds)
    (hqcont : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (hdqcont : ContinuousOn (Function.uncurry dq) (Set.Icc a b ×ˢ Set.univ))
    (hder : ∀ τ ∈ Set.Ioo a b, ∀ y, HasDerivAt (fun σ => q σ y) (dq τ y) τ)
    (hPDE : ∀ τ ∈ Set.Ioo a b, ∀ y,
      dq τ y = v12_rawDivergenceRHS (q τ) (fun j => f j τ) (g τ) y)
    (hq : ∀ τ ∈ Set.Ioo a b, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q τ))
    (hf : ∀ τ ∈ Set.Ioo a b, ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j τ))
    (hg : ∀ τ ∈ Set.Ioo a b, Continuous (g τ))
    (hQr : ∀ τ ∈ Set.Icc a b, (Q τ : V12Spatial → V12Field) =ᵐ[volume] q τ)
    (hFr : ∀ j, ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (F j τ : V12Spatial → V12Field) =ᵐ[volume] f j τ)
    (hGr : ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (G τ : V12Spatial → V12Field) =ᵐ[volume] g τ)
    (hQ : MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hF : ∀ j, MemLp (F j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hG : MemLp G ((4 : ℝ≥0∞) / 3) ((volume : Measure ℝ).restrict (Set.Icc a b)))
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    v12_cutoffTimeField p hpc hps N Q t - v12_cutoffTimeField p hpc hps N Q s =
      ∫ τ in s..t, v12_cutoffTimeSource p hpc hps N Q F G τ := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc s t)
  have hsub : μ ≤ (volume : Measure ℝ).restrict (Set.Icc a b) := by
    apply Measure.restrict_mono _ le_rfl
    intro τ hτ
    exact ⟨hs.1.trans hτ.1.le, hτ.2.trans ht.2⟩
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
    v12_compactSpatialTestSchwartz χ hc (χ.smooth (⊤ : ℕ∞)) k R x
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let vR : ℕ → ℝ → V12Field := fun R τ => ∫ y : V12Spatial, Ψ R y • q τ y
  let gR : ℕ → ℝ → V12Field := fun R =>
    v12_testSourceFromLpKernels ((Δ (Ψ R)).toLp 2 (volume : Measure V12Spatial))
      (fun j => (∂_{e j} (Ψ R)).toLp 2 (volume : Measure V12Spatial))
      ((Ψ R).toLp 4 (volume : Measure V12Spatial)) Q F G
  have htest : ∀ R, IntervalIntegrable (gR R) volume s t ∧
      vR R t - vR R s = ∫ τ in s..t, gR R τ := by
    intro R
    exact v12_actual_test_pde_time_identity a b (Ψ R)
      (v12_compactSpatialTest_compactSupport χ hc k R x)
      q dq g f Q F G hqcont hdqcont hder hPDE hq hf hg
      (ae_restrict_of_forall_mem measurableSet_Icc (fun τ hτ => hQr τ hτ))
      hFr hGr hs ht hst
  have hend : ∀ τ ∈ Set.Icc a b, Tendsto (fun R => vR R τ) atTop
      (𝓝 (v12_cutoffTimeField p hpc hps N Q τ x)) := by
    intro τ hτ
    have heq : ∀ R, vR R τ =
        ∫ y : V12Spatial, v12_compactSpatialTest χ k R x y • (Q τ : V12Spatial → V12Field) y := by
      intro R
      apply integral_congr_ae
      filter_upwards [hQr τ hτ] with y hy
      change v12_compactSpatialTest χ k R x y • q τ y = _
      rw [hy]
    simp_rw [heq]
    exact v12_compactSpatialTest_endpoint_to_BCF χ χ.continuous hχ0 hχb k x (Q τ)
  have hSx : IntervalIntegrable (fun τ => S τ x) volume s t := by
    constructor
    · exact (BoundedContinuousFunction.evalCLM ℝ x).integrable_comp hSint.1
    · exact (BoundedContinuousFunction.evalCLM ℝ x).integrable_comp hSint.2
  have hlim : Tendsto (fun R => ∫ τ in Set.Ioc s t, ‖gR R τ - S τ x‖) atTop (𝓝 0) :=
    v12_actual_test_fullSource_to_cutoff_L1_tendsto μ χ hc hχ0 hχb
      p hpc hps N x Q F G hQμ hFμ hGμ
  exact v12_time_identity_of_test_limit
    (fun τ => v12_cutoffTimeField p hpc hps N Q τ x) (fun τ => S τ x)
    vR gR s t hst hSx (fun R => (htest R).1) (fun R => (htest R).2)
    (hend s hs) (hend t ht) hlim

#print axioms v12_cutoff_time_identity_from_raw_pde

end SMScattering.W20Full
