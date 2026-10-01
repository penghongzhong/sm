import lean.v12.V12_ZDCompactTestTimeIdentity

/-! An internal FTC step allowing only interior continuity of the original
partial derivative. Endpoint continuity is required solely for Q. The source
identification premise here must be DERIVED from the original distributional
PDE before this lemma can certify a whole-paper application. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open MeasureTheory
open scoped Topology

theorem v12_compact_pairing_time_identity_of_integrable_source
    (a b : ℝ) (ψ : V12Spatial → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (Q DQ : ℝ → V12Spatial → V12Field) (G : ℝ → V12Field)
    (hQ : ContinuousOn (Function.uncurry Q) (Set.Icc a b ×ˢ Set.univ))
    (hDQ : ContinuousOn (Function.uncurry DQ) (Set.Ioo a b ×ˢ Set.univ))
    (hder : ∀ t ∈ Set.Ioo a b, ∀ y, HasDerivAt (fun s => Q s y) (DQ t y) t)
    (hG : IntegrableOn G (Set.Icc a b) volume)
    (hsource : (fun τ => ∫ y : V12Spatial, ψ y • DQ τ y)
      =ᵐ[(volume : Measure ℝ).restrict (Set.Icc a b)] G)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) :
    (∫ y : V12Spatial, ψ y • Q t y) - (∫ y : V12Spatial, ψ y • Q s y) =
      ∫ τ in s..t, G τ := by
  have hsub : Set.Icc s t ⊆ Set.Icc a b := by
    intro τ hτ
    exact ⟨hs.1.trans hτ.1, hτ.2.trans ht.2⟩
  have hoc : Set.uIoc s t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hst]
    exact Set.Ioc_subset_Icc_self.trans hsub
  have he : (fun τ => ∫ y : V12Spatial, ψ y • DQ τ y)
      =ᵐ[(volume : Measure ℝ).restrict (Set.uIoc s t)] G :=
    ae_restrict_of_ae_restrict_of_subset hoc hsource
  have hGi : IntervalIntegrable G volume s t :=
    intervalIntegrable_iff.mpr (hG.mono_set hoc)
  have hDi := hGi.congr_ae (Filter.EventuallyEq.symm he)
  have hslice : ∀ τ ∈ Set.Ioo a b, Continuous (Q τ) := by
    intro τ hτ
    have hmap : Set.MapsTo (fun y : V12Spatial => (τ,y)) Set.univ
        (Set.Icc a b ×ˢ Set.univ) := fun y _ =>
      ⟨⟨hτ.1.le,hτ.2.le⟩, Set.mem_univ y⟩
    simpa only [continuousOn_univ, Function.comp_def, Function.uncurry, id_eq] using
      hQ.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hd : ∀ τ ∈ Set.Ioo s t,
      HasDerivAt (fun σ => ∫ y : V12Spatial, ψ y • Q σ y)
        (∫ y : V12Spatial, ψ y • DQ τ y) τ := by
    intro τ hτ
    exact v12_compact_pairing_hasDerivAt (Set.Ioo a b) isOpen_Ioo ψ hψ hc Q DQ
      hslice hDQ hder ⟨hs.1.trans_lt hτ.1,hτ.2.trans_le ht.2⟩
  calc
    _ = ∫ τ in s..t, (∫ y : V12Spatial, ψ y • DQ τ y) :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
        ((v12_compact_pairing_continuousOn (Set.Icc a b) ψ hψ hc Q hQ).mono hsub)
        hd hDi).symm
    _ = _ := intervalIntegral.integral_congr_ae_restrict he

#print axioms v12_compact_pairing_time_identity_of_integrable_source
end SMScattering.W20Full
