import lean.v12.V12_ZGSOriginalCutoffTimeIdentity
import lean.v12.V12_ZIRawPDECompactness

/-! Fixed-frequency compactness from the original distributional equation.
The time identity, source budget and concrete representatives are proved,
not premises. Raw MZ-to-time-representative construction is downstream.
Pending actual CI. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_fixed_frequency_compactness_original_distribution
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (hab : a ≤ b)
    (χ : SchwartzMap V12Spatial ℝ) (hcχ : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (q : ℕ → V12Spacetime → V12Field)
    (hc : ∀ n, ContinuousOn (q n) (Set.Icc a b ×ˢ Set.univ))
    (hs : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q n) (Prod.fst ⁻¹' Set.Ioo a b))
    (hq4 : ∀ n, MemLp (q n) 4 (v12_slab_measure a b))
    (M : ℝ)
    (hE : ∀ n, ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q n (τ,x)) 2 volume ≤ ENNReal.ofReal M)
    (hdiv : ∀ n (φ : V12Spacetime → ℂ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, v12_actualCoulombA (q n) 0 z * fderiv ℝ φ z (v12_spatialDirection 0)
        ∂v12_slab_measure a b) +
      (∫ z, v12_actualCoulombA (q n) 1 z * fderiv ℝ φ z (v12_spatialDirection 1)
        ∂v12_slab_measure a b) = 0)
    (hPDE : ∀ n j, V12OriginalScalarDistributionalPDE a b (fun z => q n z j)
      (v12_actualCoulombA (q n)) (v12_originalScalarSource a b (q n) (hq4 n) j)
      v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1))
    (Q : ℕ → ℝ → V12SpatialL2) (F : ℕ → Fin 2 → ℝ → V12SpatialL2)
    (G : ℕ → ℝ → V12SpatialLFourThirds)
    (hQr : ∀ n τ, τ ∈ Set.Icc a b → (Q n τ : V12Spatial → V12Field) =ᵐ[volume]
      (fun x => q n (τ,x)))
    (hFr : ∀ n j, ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (F n j τ : V12Spatial → V12Field) =ᵐ[volume]
        (fun x => v12_driftProduct (v12_actualCoulombA (q n)) (q n) j (τ,x)))
    (hGr : ∀ n, ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (G n τ : V12Spatial → V12Field) =ᵐ[volume]
        (fun x => v12_zeroOrderProduct (v12_originalReconstructedPotential a b (q n) (hq4 n))
          (fun z => v12_WDensity (q n z)) (q n) (τ,x)))
    (hQ : ∀ n, MemLp (Q n) ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hF : ∀ n j, MemLp (F n j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hG : ∀ n, MemLp (G n) ((4 : ℝ≥0∞)/3) ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (CF CG : ℝ≥0∞) (hCF : CF ≠ ∞) (hCG : CG ≠ ∞)
    (hEnergy : ∀ n τ, τ ∈ Set.Icc a b → ‖Q n τ‖ ≤ M)
    (hFnorm : ∀ n j, eLpNorm (F n j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ CF)
    (hGnorm : ∀ n, eLpNorm (G n) ((4 : ℝ≥0∞)/3)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ CG) :
    ∀ R, IsCompact (closure (Set.range (fun n => v12_localize a b R
      (v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n))))) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc a b)
  let C : ℝ≥0∞ :=
    ENNReal.ofReal ‖v12_timeLaplacianCLM p hpc hps N‖ *
      (ENNReal.ofReal M * μ Set.univ ^ ((3 : ℝ) / 4)) +
    ENNReal.ofReal ‖v12_timeGradientCLM p hpc hps N 0‖ *
      (CF * μ Set.univ ^ ((1 : ℝ) / 4)) +
    ENNReal.ofReal ‖v12_timeGradientCLM p hpc hps N 1‖ *
      (CF * μ Set.univ ^ ((1 : ℝ) / 4)) +
    ENNReal.ofReal ‖v12_timeZeroOrderCLM p hpc hps N‖ * CG
  have hμ : μ Set.univ ≠ ∞ := (measure_lt_top μ Set.univ).ne
  have hC : C ≠ ∞ := by
    dsimp only [C]
    finiteness
  have hQnorm : ∀ n, eLpNorm (Q n) ∞ μ ≤ ENNReal.ofReal M := by
    intro n
    rw [eLpNorm_exponent_top (hQ n).aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_bound
    exact ae_restrict_of_forall_mem measurableSet_Icc (fun τ hτ => hEnergy n τ hτ)
  have hBudget : ∀ n, v12_cutoffSourceBudget p hpc hps N μ (Q n) (F n) (G n) ≤ C := by
    intro n
    dsimp only [v12_cutoffSourceBudget, C]
    gcongr
    · exact hQnorm n
    · exact hFnorm n 0
    · exact hFnorm n 1
    · exact hGnorm n
  have hIntegral : ∀ n s, s ∈ Set.Icc a b → ∀ t, t ∈ Set.Icc a b → s ≤ t →
      v12_cutoffTimeField p hpc hps N (Q n) t -
        v12_cutoffTimeField p hpc hps N (Q n) s =
        ∫ τ in s..t, v12_cutoffTimeSource p hpc hps N (Q n) (F n) (G n) τ := by
    intro n s hsI t htI hst
    exact v12_cutoff_time_identity_from_original_distribution hHLS a b (q n)
      (hc n) (hs n) (hq4 n) M (hE n) (hdiv n) (hPDE n)
      (Q n) (F n) (G n) (hQr n) (hFr n) (hGr n) (hQ n) (hF n) (hG n)
      χ hcχ hχ0 hχb p hpc hps N hsI htI hst
  let v : ℕ → V12SlabL2 a b := fun n =>
    v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n)
  have hlocal : ∀ n R, (v12_localize a b R (v n) : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)]
        fun z => v12_cutoffTimeField p hpc hps N (Q n) z.1 z.2 := by
    intro n R
    exact (v12_localize_coeFn a b R (v n)).trans
      (ae_restrict_of_ae (v12_spacetimeCutoffClass_ae a b p hpc hps N (Q n) (hQ n)))
  intro R
  exact v12_cutoff_local_compact_from_source_integrals a b R hab p hpc hps N Q F G
    M C hC hEnergy hQ hF hG hBudget hIntegral
    (fun n => v12_localize a b R (v n)) (fun n => hlocal n R)

#print axioms v12_fixed_frequency_compactness_original_distribution
end SMScattering.W20Full
