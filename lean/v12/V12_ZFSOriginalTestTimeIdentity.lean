import lean.v12.V12_ZESOriginalSourceClassMatch

/-! Original distributional PDE to the existing actual Lp compact-test time
identity. Source correspondence is proved by same-field representatives;
all time integrability is proved from time Lp membership. Those objects and
memberships must still be constructed from original MZ data in the final
compactness application. Pending CI. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace SMScattering.W20Full
open MeasureTheory LineDeriv Laplacian
open scoped ENNReal ContDiff

theorem v12_original_test_Lp_time_identity
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
    (ψ : SchwartzMap V12Spatial ℂ) (hcψ : HasCompactSupport (ψ : V12Spatial → ℂ))
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
    {s t : ℝ} (hsi : s ∈ Set.Icc a b) (hti : t ∈ Set.Icc a b) (hst : s ≤ t) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    let S := v12_testSourceFromLpKernels ((Δ ψ).toLp 2 (volume : Measure V12Spatial))
      (fun j => (∂_{e j} ψ).toLp 2 (volume : Measure V12Spatial))
      (ψ.toLp 4 (volume : Measure V12Spatial)) Q F G
    IntervalIntegrable S volume s t ∧
      (∫ x : V12Spatial, ψ x • q (t,x)) - (∫ x : V12Spatial, ψ x • q (s,x)) =
        ∫ τ in s..t, S τ := by
  dsimp only
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let S := v12_testSourceFromLpKernels ((Δ ψ).toLp 2 (volume : Measure V12Spatial))
    (fun j => (∂_{e j} ψ).toLp 2 (volume : Measure V12Spatial))
    (ψ.toLp 4 (volume : Measure V12Spatial)) Q F G
  have hi : Integrable S ((volume : Measure ℝ).restrict (Set.Icc a b)) :=
    v12_testSourceFromLpKernels_integrable _ _ _ _ Q F G
      (memLp_one_iff_integrable.mp (hQ.mono_exponent le_top))
      (fun j => memLp_one_iff_integrable.mp ((hF j).mono_exponent (by norm_num)))
      (memLp_one_iff_integrable.mp (hG.mono_exponent v12_one_le_fourThirds_ENNReal))
  have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hst]
    intro τ hτ
    exact ⟨hsi.1.trans hτ.1.le, hτ.2.trans hti.2⟩
  have he : v12_originalVectorTestSource a b q hq ψ
      =ᵐ[(volume : Measure ℝ).restrict (Set.Icc a b)] S := by
    filter_upwards [ae_all_iff.mpr hFr, hGr, ae_restrict_mem measurableSet_Icc]
      with τ hf hg hτ
    exact v12_originalVectorTestSource_eq_Lp a b q hq ψ hcψ Q F G τ (hQr τ hτ) hf hg
  have heI : v12_originalVectorTestSource a b q hq ψ
      =ᵐ[(volume : Measure ℝ).restrict (Set.uIoc s t)] S :=
    ae_restrict_of_ae_restrict_of_subset hsub he
  refine ⟨intervalIntegrable_iff.mpr (hi.mono_measure (Measure.restrict_mono hsub le_rfl)), ?_⟩
  exact (v12_original_compact_test_time_identity hHLS a b q hc hs hq M hE hdiv hPDE
    ψ (ψ.smooth (⊤ : ℕ∞)) hcψ hsi hti hst).trans
      (intervalIntegral.integral_congr_ae_restrict heI)

#print axioms v12_original_test_Lp_time_identity
end SMScattering.W20Full
