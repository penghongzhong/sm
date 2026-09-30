import lean.v12.V12_YTestSourcePairingLimit

/-!
Actual zero-order spatial tests as L4 classes, and their time-L1 source
limit. This instantiates kernel convergence rather than assuming it.
Limits are for fixed x; no uniform-in-x limit is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal ContDiff

/-- Turn a proved raw eLpNorm error into convergence of the exact Lp
classes using their a.e. representatives. -/
theorem v12_Lp_tendsto_of_ae_eLpNorm_error
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (uR : ℕ → Lp E p μ) (u : Lp E p μ)
    (fR : ℕ → Ω → E) (f : Ω → E)
    (hR : ∀ R, (uR R : Ω → E) =ᵐ[μ] fR R)
    (hu : (u : Ω → E) =ᵐ[μ] f)
    (hlim : Tendsto (fun R => eLpNorm (fun y => fR R y - f y) p μ)
      atTop (𝓝 0)) :
    Tendsto uR atTop (𝓝 u) := by
  have hnorm : ∀ R, ‖uR R - u‖ =
      (eLpNorm (fun y => fR R y - f y) p μ).toReal := by
    intro R
    have hae : ((uR R - u : Lp E p μ) : Ω → E) =ᵐ[μ] fun y => fR R y - f y := by
      filter_upwards [Lp.coeFn_sub (uR R) u, hR R, hu] with y hy hRy huy
      rw [hy]
      simp only [Pi.sub_apply, hRy, huy]
    rw [Lp.norm_def, eLpNorm_congr_ae hae]
  have ht := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, ENNReal.toReal_zero, hnorm] using ht

/-- The same concrete compact test, now as a Schwartz function. -/
noncomputable def v12_compactSpatialTestSchwartz
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x : V12Spatial) :
    SchwartzMap V12Spatial ℂ :=
  (v12_compactSpatialTest_compactSupport χ hc k R x).toSchwartzMap
    (v12_compactSpatialTest_smooth χ hs k R x)

@[simp] theorem v12_compactSpatialTestSchwartz_apply
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x y : V12Spatial) :
    v12_compactSpatialTestSchwartz χ hc hs k R x y =
      v12_compactSpatialTest χ k R x y := rfl

noncomputable def v12_compactSpatialTestL4
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x : V12Spatial) : V12ScalarL4 :=
  (v12_compactSpatialTestSchwartz χ hc hs k R x).toLp 4 (volume : Measure V12Spatial)

theorem v12_compactSpatialTestL4_ae
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x : V12Spatial) :
    (v12_compactSpatialTestL4 χ hc hs k R x : V12Spatial → ℂ)
      =ᵐ[volume] v12_compactSpatialTest χ k R x :=
  (v12_compactSpatialTestSchwartz χ hc hs k R x).coeFn_toLp
    4 (volume : Measure V12Spatial)

theorem v12_reflectedSchwartzL4_ae
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial) :
    (v12_reflectedTranslateL4 (k.toLp 4 (volume : Measure V12Spatial)) x : V12Spatial → ℂ)
      =ᵐ[volume] fun y => k (x-y) := by
  have hc : (v12_reflectedTranslateL4 (k.toLp 4 (volume : Measure V12Spatial)) x : V12Spatial → ℂ)
      =ᵐ[volume] fun y => (k.toLp 4 (volume : Measure V12Spatial) : V12Spatial → ℂ) (x-y) := by
    simpa [v12_reflectedTranslateL4, Function.comp_def] using
      Lp.coeFn_compMeasurePreserving (k.toLp 4 (volume : Measure V12Spatial))
        (v12_subLeft_measurePreserving x)
  have hk := (v12_subLeft_measurePreserving x).quasiMeasurePreserving.ae
    (k.coeFn_toLp 4 (volume : Measure V12Spatial))
  filter_upwards [hc, hk] with y hcy hky
  exact hcy.trans (by simpa only [v12_subLeftFamily_apply] using hky)

/-- The actual compact test converges to K(x-·) in spatial L4. -/
theorem v12_compactSpatialTestL4_tendsto
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial) :
    Tendsto (fun R => v12_compactSpatialTestL4 χ hc hs k R x) atTop
      (𝓝 (v12_reflectedTranslateL4 (k.toLp 4 (volume : Measure V12Spatial)) x)) := by
  exact v12_Lp_tendsto_of_ae_eLpNorm_error volume 4
    (fun R => v12_compactSpatialTestL4 χ hc hs k R x)
    (v12_reflectedTranslateL4 (k.toLp 4 (volume : Measure V12Spatial)) x)
    (fun R => v12_compactSpatialTest χ k R x) (fun y => k (x-y))
    (fun R => v12_compactSpatialTestL4_ae χ hc hs k R x)
    (v12_reflectedSchwartzL4_ae k x)
    (v12_compactSpatialTest_error_tendsto 4 (by norm_num) (by norm_num)
      χ hs.continuous hχ0 hχb k x)

/-- Identify the actual L4/L43 pairing with its unreflected integral. -/
theorem v12_L4L43Pairing_eq_integral_of_ae
    (k : V12ScalarL4) (f : V12SpatialLFourThirds) (K : V12Spatial → ℂ)
    (hk : (k : V12Spatial → ℂ) =ᵐ[volume] K) :
    v12_L4L43ConvolutionPairing k f = ∫ y : V12Spatial, K y • f y := by
  rw [v12_L4L43ConvolutionPairing, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hk] with y hy
  change k y • f y = K y • f y
  rw [hy]

/-- Actual zero-order compact-test source limit. The spatial L4 limit and
the time-L1 error are both conclusions, not assumptions. -/
theorem v12_actual_zeroOrder_test_source_L1_tendsto
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (k : SchwartzMap V12Spatial ℂ) (x : V12Spatial)
    (G : ℝ → V12SpatialLFourThirds) (hG : MemLp G ((4 : ℝ≥0∞) / 3) μ) :
    Tendsto (fun R => ∫ t,
      ‖(∫ y, v12_compactSpatialTest χ k R x y • G t y) -
        v12_L4L43ConvolutionBCFCLM (k.toLp 4 (volume : Measure V12Spatial)) (G t) x‖ ∂μ)
      atTop (𝓝 0) := by
  have hk := v12_compactSpatialTestL4_tendsto χ hc hs hχ0 hχb k x
  have h := v12_pairing_norm_L1_tendsto μ v12_L4L43ConvolutionPairing
    (fun R => v12_compactSpatialTestL4 χ hc hs k R x)
    (v12_reflectedTranslateL4 (k.toLp 4 (volume : Measure V12Spatial)) x) hk G
    (memLp_one_iff_integrable.mp (hG.mono_exponent v12_one_le_fourThirds_ENNReal))
  have heq : ∀ R t,
      v12_L4L43ConvolutionPairing (v12_compactSpatialTestL4 χ hc hs k R x) (G t) =
        ∫ y, v12_compactSpatialTest χ k R x y • G t y := by
    intro R t
    exact v12_L4L43Pairing_eq_integral_of_ae
      (v12_compactSpatialTestL4 χ hc hs k R x) (G t)
      (v12_compactSpatialTest χ k R x) (v12_compactSpatialTestL4_ae χ hc hs k R x)
  change Tendsto (fun R => ∫ t,
    ‖(∫ y, v12_compactSpatialTest χ k R x y • G t y) -
      v12_L4L43ConvolutionPairing
        (v12_reflectedTranslateL4 (k.toLp 4 (volume : Measure V12Spatial)) x) (G t)‖ ∂μ)
    atTop (𝓝 0)
  simpa only [heq] using h

#print axioms v12_Lp_tendsto_of_ae_eLpNorm_error
#print axioms v12_compactSpatialTestSchwartz_apply
#print axioms v12_compactSpatialTestL4_ae
#print axioms v12_reflectedSchwartzL4_ae
#print axioms v12_compactSpatialTestL4_tendsto
#print axioms v12_L4L43Pairing_eq_integral_of_ae
#print axioms v12_actual_zeroOrder_test_source_L1_tendsto

end SMScattering.W20Full
