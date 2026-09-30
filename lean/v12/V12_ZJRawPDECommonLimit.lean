import lean.v12.V12_ZIRawPDECompactness
import lean.v12.V12_YCompactTestCutoff
import lean.v12.V12_YXRawSlabRealization
import lean.v12.V12_YMeasurableLocalLimitGluing

/-!
The common subsequence and a single strongly measurable local limit follow
from the smooth raw PDE and the actual Fourier frequency-tail condition.
Fixed-frequency compactness, compatibility, and measurable gluing are proved,
not inputs. Hodge/MZ instantiation and the nonlinear closure theorem remain open.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_common_measurable_limit_from_raw_pde
    (a b : ℝ) (hab : a ≤ b)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
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
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ CG)
    (hTight : Tendsto (fun N => sSup (Set.range (fun n =>
      ‖v12_rawSlabClass a b (q n) (hqcont n) (Q n) (hQ n) (hQr n) -
        v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n)‖))) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (u : V12Spacetime → V12Field), StrictMono σ ∧
      StronglyMeasurable u ∧
      ∀ R, ∃ hu : MemLp u 2
          ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)),
        Tendsto (fun n => v12_localize a b R
          (v12_rawSlabClass a b (q (σ n)) (hqcont (σ n)) (Q (σ n))
            (hQ (σ n)) (hQr (σ n)))) atTop (𝓝 (hu.toLp u)) := by
  classical
  obtain ⟨χ, hc, hχ0, hχb⟩ := v12_exists_compact_test_cutoff
  let raw : ℕ → V12SlabL2 a b := fun n =>
    v12_rawSlabClass a b (q n) (hqcont n) (Q n) (hQ n) (hQr n)
  let cut : ℕ → ℕ → V12SlabL2 a b := fun N n =>
    v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n)
  let err : ℕ → ℝ := fun N => sSup (Set.range (fun n => ‖raw n - cut N n‖))
  obtain ⟨B, hB⟩ := v12_timeL2_uniform_bound a b M Q hQ hEnergy
  have hraw : ∀ n, ‖raw n‖ ≤ B := by
    intro n
    exact (v12_rawSlabClass_norm_eq a b (q n) (hqcont n) (Q n) (hQ n) (hQr n)).le.trans (hB n)
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
    exact v12_fixed_frequency_compactness_from_raw_pde a b hab χ hc hχ0 hχb p hpc hps N
      q dq g f Q F G hqcont hdqcont hder hPDE hq hf hg hQr hFr hGr hQ hF hG
      M CF CG hCF hCG hEnergy hFnorm hGnorm R
  obtain ⟨σ, hσ, hlim⟩ := v12_countable_cutoff_limits (V12CylinderL2 a b)
    (fun R n => v12_localize a b R (raw n))
    (fun R N n => v12_localize a b R (cut N n)) err hTight hApprox
    (fun R N => closure (Set.range (fun n => v12_localize a b R (cut N n))))
    hCompact (fun R N n => subset_closure (Set.mem_range_self n))
  choose u hu using hlim
  obtain ⟨v, hv, hvlim⟩ := v12_stronglyMeasurable_local_limit_from_common_sequence a b
    (fun n => raw (σ n)) u hu
  exact ⟨σ, v, hσ, hv, hvlim⟩

#print axioms v12_common_measurable_limit_from_raw_pde
end SMScattering.W20Full
