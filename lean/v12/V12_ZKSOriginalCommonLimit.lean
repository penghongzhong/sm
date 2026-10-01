import lean.v12.V12_ZISOriginalFixedFrequencyCompactness
import lean.v12.V12_YZZCAOriginalReconstructedBudgets
import lean.v12.V12_ZKRawSourceCommonLimit

/-! Original MZ, original weak PDE/divergence and actual raw Fourier tightness
produce a common subsequence and one strongly measurable local limit. All
Q/F/G classes, source budgets, time identities, fixed-frequency compact sets,
common diagonal extraction and measurable gluing are constructed internally.
Nonlinear/spatial closure on that SAME subsequence remains downstream.
Pending CI; not a full Theorem7.2 certificate, including degenerate slabs. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_common_limit_original_distribution
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (hab : a < b)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (q : ℕ → V12Spacetime → V12Field)
    (hc : ∀ n, ContinuousOn (q n) (Set.Icc a b ×ˢ Set.univ))
    (hs : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q n) (Prod.fst ⁻¹' Set.Ioo a b))
    (hq4 : ∀ n, MemLp (q n) 4 (v12_slab_measure a b))
    (M : ℝ) (hM : 0 ≤ M) (Z : ℝ≥0∞) (hZ : Z ≠ ∞)
    (hqbound : ∀ n, eLpNorm (q n) 4 (v12_slab_measure a b) ≤ Z)
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
    (hTight : Tendsto (fun N => sSup (Set.range (fun n =>
      v12_rawFrequencyTail a b p hpc hps N (fun τ x => q n (τ,x))))) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (u : V12Spacetime → V12Field), StrictMono σ ∧
      StronglyMeasurable u ∧ ∀ R,
        MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)) ∧
        (∀ n, MemLp (q (σ n)) 2
          ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))) ∧
        Tendsto (fun n => (eLpNorm (fun z => q (σ n) z-u z) 2
          ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
  classical
  let rawq := fun n τ x => q n (τ,x)
  obtain ⟨CA, hCA, CV, hCV, hBudget⟩ := v12_original_reconstructed_coefficient_budgets hHLS
  have hB (n : ℕ) := hBudget a b (q n) (hc n) (hq4 n) M hM (hE n) Z hZ (hqbound n)
  choose Q F G hQr hEnergy hQ hFr hGr hF hG hFn hGn using fun n =>
    v12_actual_raw_time_realizations a b hab (rawq n) (hc n)
      (v12_actualCoulombA (q n)) (v12_originalReconstructedPotential a b (q n) (hq4 n))
      (fun z => v12_WDensity (q n z))
      (fun j => ((hB n).1 j).1) (hB n).2.1.1 (hB n).2.2.1 (hq4 n) M hM (hE n)
  let CF := (CA * ENNReal.ofReal M * Z) * Z
  let CG := (ENNReal.ofReal ((24+CV*M^2)*Z.toReal^2) + 2*Z^2) * Z
  have hCF : CF ≠ ∞ := by dsimp [CF]; finiteness
  have hCG : CG ≠ ∞ := by dsimp [CG]; finiteness
  have hFnorm (n : ℕ) (j : Fin 2) : eLpNorm (F n j) 2
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ CF :=
    (hFn n j).trans (mul_le_mul' ((hB n).1 j).2 (hqbound n))
  have hGnorm (n : ℕ) : eLpNorm (G n) ((4 : ℝ≥0∞)/3)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ CG :=
    (hGn n).trans (mul_le_mul' (add_le_add (hB n).2.1.2 (hB n).2.2.2) (hqbound n))
  have hT : Tendsto (fun N => sSup (Set.range (fun n =>
      ‖v12_rawSlabClass a b (rawq n) (hc n) (Q n) (hQ n) (hQr n) -
        v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n)‖))) atTop (𝓝 0) := by
    have heq (N n : ℕ) :
        ‖v12_rawSlabClass a b (rawq n) (hc n) (Q n) (hQ n) (hQr n) -
          v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n)‖ =
        v12_rawFrequencyTail a b p hpc hps N (rawq n) :=
      (v12_rawFrequencyTail_eq_class_norm a b p hpc hps N (rawq n) (hc n)
        (Q n) (hQ n) (hQr n)).symm
    simp_rw [heq]
    exact hTight
  obtain ⟨χ, hcχ, hχ0, hχb⟩ := v12_exists_compact_test_cutoff
  let raw : ℕ → V12SlabL2 a b := fun n =>
    v12_rawSlabClass a b (rawq n) (hc n) (Q n) (hQ n) (hQr n)
  let cut : ℕ → ℕ → V12SlabL2 a b := fun N n =>
    v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n)
  let err : ℕ → ℝ := fun N => sSup (Set.range (fun n => ‖raw n - cut N n‖))
  obtain ⟨B, hB⟩ := v12_timeL2_uniform_bound a b M Q hQ hEnergy
  have hraw : ∀ n, ‖raw n‖ ≤ B := by
    intro n
    exact (v12_rawSlabClass_norm_eq a b (rawq n) (hc n) (Q n) (hQ n) (hQr n)).le.trans (hB n)
  have hcut : ∀ N n, ‖cut N n‖ ≤ ‖v12_cutoffN p hpc hps N‖ * B := by
    intro N n
    apply (v12_spacetimeCutoffClass_norm_le a b p hpc hps N (Q n) (hQ n)).trans
    gcongr
    exact hB n
  have hbounded : ∀ N, BddAbove (Set.range (fun n => ‖raw n - cut N n‖)) := by
    intro N
    refine ⟨B + ‖v12_cutoffN p hpc hps N‖ * B, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (hraw n) (hcut N n))
  have hApprox : ∀ R N n,
      dist (v12_localize a b R (raw n)) (v12_localize a b R (cut N n)) ≤ err N := by
    intro R N n
    apply (v12_localize_dist_le a b R (raw n) (cut N n)).trans
    rw [dist_eq_norm]
    exact le_csSup (hbounded N) (Set.mem_range_self n)
  have hCompact : ∀ R N, IsCompact
      (closure (Set.range (fun n => v12_localize a b R (cut N n)))) := by
    intro R N
    exact v12_fixed_frequency_compactness_original_distribution hHLS a b hab.le
      χ hcχ hχ0 hχb p hpc hps N q hc hs hq4 M hE hdiv hPDE
      Q F G hQr hFr hGr hQ hF hG CF CG hCF hCG hEnergy hFnorm hGnorm R
  obtain ⟨σ, hσ, hlim⟩ := v12_countable_cutoff_limits (V12CylinderL2 a b)
    (fun R n => v12_localize a b R (raw n))
    (fun R N n => v12_localize a b R (cut N n)) err hT hApprox
    (fun R N => closure (Set.range (fun n => v12_localize a b R (cut N n))))
    hCompact (fun R N n => subset_closure (Set.mem_range_self n))
  choose u hu using hlim
  obtain ⟨u, hu, hlocal⟩ := v12_stronglyMeasurable_local_limit_from_common_sequence a b
    (fun n => raw (σ n)) u hu

  refine ⟨σ, u, hσ, hu, ?_⟩
  intro R
  obtain ⟨huR, hconv⟩ := hlocal R
  let c : ℕ → V12CylinderL2 a b R := fun n => v12_localize a b R
    (v12_rawSlabClass a b (rawq (σ n)) (hc (σ n)) (Q (σ n)) (hQ (σ n)) (hQr (σ n)))
  have hcr : ∀ n, (c n : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] Function.uncurry (rawq (σ n)) := by
    intro n
    exact (v12_localize_coeFn a b R _).trans (ae_restrict_of_ae
      (v12_rawSlabClass_ae a b (rawq (σ n)) (hc (σ n)) (Q (σ n)) (hQ (σ n)) (hQr (σ n))))
  refine ⟨huR, (fun n => MemLp.ae_eq (hcr n) (Lp.memLp (c n))), ?_⟩
  have heq : ∀ n, dist (c n) (huR.toLp u) =
      (eLpNorm (fun z : V12Spacetime => q (σ n) z - u z) 2
        ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal := by
    intro n
    rw [Lp.dist_def]
    apply congrArg ENNReal.toReal
    exact eLpNorm_congr_ae ((hcr n).sub huR.coeFn_toLp)
  have hd := tendsto_iff_dist_tendsto_zero.mp hconv
  change Tendsto (fun n => dist (c n) (huR.toLp u)) atTop (𝓝 0) at hd
  simpa only [heq] using hd

#print axioms v12_common_limit_original_distribution

theorem v12_common_limit_original_distribution_all_slabs
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (q : ℕ → V12Spacetime → V12Field)
    (hc : ∀ n, ContinuousOn (q n) (Set.Icc a b ×ˢ Set.univ))
    (hs : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q n) (Prod.fst ⁻¹' Set.Ioo a b))
    (hq4 : ∀ n, MemLp (q n) 4 (v12_slab_measure a b))
    (M : ℝ) (hM : 0 ≤ M) (Z : ℝ≥0∞) (hZ : Z ≠ ∞)
    (hqbound : ∀ n, eLpNorm (q n) 4 (v12_slab_measure a b) ≤ Z)
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
    (hTight : Tendsto (fun N => sSup (Set.range (fun n =>
      v12_rawFrequencyTail a b p hpc hps N (fun τ x => q n (τ,x))))) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (u : V12Spacetime → V12Field), StrictMono σ ∧
      StronglyMeasurable u ∧ ∀ R,
        MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)) ∧
        (∀ n, MemLp (q (σ n)) 2
          ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))) ∧
        Tendsto (fun n => (eLpNorm (fun z => q (σ n) z-u z) 2
          ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
  by_cases hab : a < b
  · exact v12_common_limit_original_distribution hHLS a b hab p hpc hps q hc hs hq4
      M hM Z hZ hqbound hE hdiv hPDE hTight
  · have htime : (volume : Measure ℝ).restrict (Set.Icc a b) = 0 := by
      apply Measure.restrict_eq_zero.mpr
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (le_of_not_gt hab))
    have hμ : v12_slab_measure a b = 0 := by
      simp only [v12_slab_measure, htime, Measure.zero_prod]
    refine ⟨id, 0, strictMono_id, stronglyMeasurable_zero, ?_⟩
    intro R
    simp only [hμ, Measure.restrict_zero, memLp_measure_zero, eLpNorm_measure_zero,
      ENNReal.toReal_zero, forall_const, true_and]
    exact tendsto_const_nhds

#print axioms v12_common_limit_original_distribution_all_slabs

end SMScattering.W20Full
