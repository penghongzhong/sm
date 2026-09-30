import lean.v12.V12_ZCSpatialTestIntegrationByParts

/-!
Continuity and the time integral identity of the actual compact test curve.
Both the endpoint continuity and derivative integral are derived from the
raw field. No hIntegral, hFTC, hCompact or weak-test residual is assumed.
The identification with the Lp cutoff source is a subsequent obligation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open MeasureTheory
open scoped ContDiff

theorem v12_compact_pairing_continuousOn
    (J : Set ℝ) (ψ : V12Spatial → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (Q : ℝ → V12Spatial → V12Field)
    (hQ : ContinuousOn (Function.uncurry Q) (J ×ˢ Set.univ)) :
    ContinuousOn (fun t => ∫ y : V12Spatial, ψ y • Q t y) J := by
  apply continuousOn_integral_of_compact_support
    (μ := (volume : Measure V12Spatial)) (k := tsupport ψ) hc
  · exact (hψ.comp continuous_snd).continuousOn.smul hQ
  · intro t y _ hy
    have hzero : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp only [hzero, zero_smul]

/-- Compact-test FTC, with endpoint continuity proved from the raw field. -/
theorem v12_compact_pairing_time_identity
    (a b : ℝ) (ψ : V12Spatial → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (Q DQ : ℝ → V12Spatial → V12Field)
    (hQ : ContinuousOn (Function.uncurry Q) (Set.Icc a b ×ˢ Set.univ))
    (hDQ : ContinuousOn (Function.uncurry DQ) (Set.Icc a b ×ˢ Set.univ))
    (hder : ∀ t ∈ Set.Ioo a b, ∀ y, HasDerivAt (fun s => Q s y) (DQ t y) t)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    (∫ y : V12Spatial, ψ y • Q t y) - (∫ y : V12Spatial, ψ y • Q s y) =
      ∫ τ in s..t, (∫ y : V12Spatial, ψ y • DQ τ y) := by
  have hcont := v12_compact_pairing_continuousOn (Set.Icc a b) ψ hψ hc Q hQ
  have hdcont := v12_compact_pairing_continuousOn (Set.Icc a b) ψ hψ hc DQ hDQ
  have hsub : Set.Icc s t ⊆ Set.Icc a b := by
    intro τ hτ
    exact ⟨hs.1.trans hτ.1, hτ.2.trans ht.2⟩
  have hslice : ∀ τ ∈ Set.Ioo a b, Continuous (Q τ) := by
    intro τ hτ
    have hmap : Set.MapsTo (fun y : V12Spatial => (τ,y)) Set.univ
        (Set.Icc a b ×ˢ Set.univ) := fun y _ =>
      ⟨⟨hτ.1.le,hτ.2.le⟩, Set.mem_univ y⟩
    simpa only [continuousOn_univ, Function.comp_def, Function.uncurry, id_eq] using
      hQ.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hDQopen : ContinuousOn (Function.uncurry DQ) (Set.Ioo a b ×ˢ Set.univ) :=
    hDQ.mono (Set.prod_mono Set.Ioo_subset_Icc_self Set.Subset.rfl)
  have hclassical : ∀ τ ∈ Set.Ioo s t,
      HasDerivAt (fun σ => ∫ y : V12Spatial, ψ y • Q σ y)
        (∫ y : V12Spatial, ψ y • DQ τ y) τ := by
    intro τ hτ
    exact v12_compact_pairing_hasDerivAt (Set.Ioo a b) isOpen_Ioo ψ hψ hc
      Q DQ hslice hDQopen hder ⟨hs.1.trans_lt hτ.1, hτ.2.trans_le ht.2⟩
  have hint : IntervalIntegrable (fun τ => ∫ y : V12Spatial, ψ y • DQ τ y)
      volume s t := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hst] using hdcont.mono hsub
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (hcont.mono hsub) hclassical hint).symm

/-- The same chi(y/(R+1)) K(x-y) family, without an integral-identity input. -/
theorem v12_actual_compact_test_time_identity
    (a b : ℝ) (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x : V12Spatial)
    (Q DQ : ℝ → V12Spatial → V12Field)
    (hQ : ContinuousOn (Function.uncurry Q) (Set.Icc a b ×ˢ Set.univ))
    (hDQ : ContinuousOn (Function.uncurry DQ) (Set.Icc a b ×ˢ Set.univ))
    (hder : ∀ t ∈ Set.Ioo a b, ∀ y, HasDerivAt (fun s => Q s y) (DQ t y) t)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    (∫ y : V12Spatial, v12_compactSpatialTest χ k R x y • Q t y) -
      (∫ y : V12Spatial, v12_compactSpatialTest χ k R x y • Q s y) =
      ∫ τ in s..t, (∫ y : V12Spatial, v12_compactSpatialTest χ k R x y • DQ τ y) :=
  v12_compact_pairing_time_identity a b _
    (v12_compactSpatialTest_smooth χ hsmooth k R x).continuous
    (v12_compactSpatialTest_compactSupport χ hc k R x)
    Q DQ hQ hDQ hder hs ht hst

#print axioms v12_compact_pairing_continuousOn
#print axioms v12_compact_pairing_time_identity
#print axioms v12_actual_compact_test_time_identity

end SMScattering.W20Full
