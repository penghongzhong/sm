import lean.v12.V12_ZGCutoffIdentityFromRawPDE
import lean.v12.V12_ZCylinderCompactness
import lean.v12.V12_YWSpacetimeCutoffRealization

/-!
Fixed-frequency compactness from the raw smooth PDE and concrete time-source
bounds. The actual global/local cutoff representatives, time integral identity,
and operator-weighted source budget are constructed. No hIntegral, hRep,
hCompact, or precomputed cutoff budget is an input.
The raw Hodge coefficient/MZ estimates and original-field instantiation remain
upstream and are not certified by this application theorem alone.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_fixed_frequency_compactness_from_raw_pde
    (a b : ℝ) (hab : a ≤ b)
    (χ : SchwartzMap V12Spatial ℝ) (hc : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (q dq g : ℕ → ℝ → V12Spatial → V12Field)
    (f : ℕ → Fin 2 → ℝ → V12Spatial → V12Field)
    (Q : ℕ → ℝ → V12SpatialL2) (F : ℕ → Fin 2 → ℝ → V12SpatialL2)
    (G : ℕ → ℝ → V12SpatialLFourThirds)
    (hqcont : ∀ n, ContinuousOn (Function.uncurry (q n)) (Set.Icc a b ×ˢ Set.univ))
    (hdqcont : ∀ n, ContinuousOn (Function.uncurry (dq n)) (Set.Icc a b ×ˢ Set.univ))
    (hder : ∀ n τ, τ ∈ Set.Ioo a b → ∀ y, HasDerivAt (fun σ => q n σ y) (dq n τ y) τ)
    (hPDE : ∀ n τ, τ ∈ Set.Ioo a b → ∀ y,
      dq n τ y = v12_rawDivergenceRHS (q n τ) (fun j => f n j τ) (g n τ) y)
    (hq : ∀ n τ, τ ∈ Set.Ioo a b → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q n τ))
    (hf : ∀ n τ, τ ∈ Set.Ioo a b → ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f n j τ))
    (hg : ∀ n τ, τ ∈ Set.Ioo a b → Continuous (g n τ))
    (hQr : ∀ n τ, τ ∈ Set.Icc a b → (Q n τ : V12Spatial → V12Field) =ᵐ[volume] q n τ)
    (hFr : ∀ n j, ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (F n j τ : V12Spatial → V12Field) =ᵐ[volume] f n j τ)
    (hGr : ∀ n, ∀ᵐ τ ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (G n τ : V12Spatial → V12Field) =ᵐ[volume] g n τ)
    (hQ : ∀ n, MemLp (Q n) ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hF : ∀ n j, MemLp (F n j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hG : ∀ n, MemLp (G n) ((4 : ℝ≥0∞) / 3) ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (M : ℝ) (CF CG : ℝ≥0∞) (hCF : CF ≠ ∞) (hCG : CG ≠ ∞)
    (hEnergy : ∀ n τ, τ ∈ Set.Icc a b → ‖Q n τ‖ ≤ M)
    (hFnorm : ∀ n j, eLpNorm (F n j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ CF)
    (hGnorm : ∀ n, eLpNorm (G n) ((4 : ℝ≥0∞) / 3)
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
    intro n s hs t ht hst
    exact v12_cutoff_time_identity_from_raw_pde a b χ hc hχ0 hχb p hpc hps N
      (q n) (dq n) (g n) (f n) (Q n) (F n) (G n)
      (hqcont n) (hdqcont n) (hder n) (hPDE n) (hq n) (hf n) (hg n)
      (hQr n) (hFr n) (hGr n) (hQ n) (hF n) (hG n) hs ht hst
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

#print axioms v12_fixed_frequency_compactness_from_raw_pde

end SMScattering.W20Full
