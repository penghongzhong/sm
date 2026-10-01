import lean.v12.V12_ZKUOriginalStrongTightnessClosure
import lean.v12.V12_YZZYLimitBochnerEnergy

/-! Full function-space form of the original-data tightness candidate:
actual Bochner Linfinity-L2, actual L4 with the original bound, actual local
L2 quotient convergence, reconstructed distributional PDE/constraints, and
all real-radius coefficient limits on ONE subsequence. All source/compactness
obligations remain internal. Pending actual CI and manuscript audit. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_original_frequency_tightness_full_spaces
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (qn : ℕ → V12Spacetime → V12Field)
    (hc : ∀ n, ContinuousOn (qn n) (Set.Icc a b ×ˢ Set.univ))
    (hs : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qn n) (Prod.fst ⁻¹' Set.Ioo a b))
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (M : ℝ) (hM : 0 ≤ M) (Z : ℝ≥0∞) (hZ : Z ≠ ∞)
    (hEn : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn n (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z)
    (hCompat : ∀ n, V12CanonicalSpatialDistributionalConstraints a b (qn n))
    (hPDE : ∀ n j, V12OriginalScalarDistributionalPDE a b (fun z => qn n z j)
      (v12_actualCoulombA (qn n)) (v12_originalScalarSource a b (qn n) (hn4 n) j)
      v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1))
    (hTight : Tendsto (fun N => sSup (Set.range (fun n =>
      v12_rawFrequencyTail a b p hpc hps N (fun τ x => qn n (τ,x))))) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ), StrictMono σ ∧
    ∃ (v : V12Spacetime → V12Field) (hmv : StronglyMeasurable v)
      (hv4 : MemLp v 4 (v12_slab_measure a b))
      (hEv : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => v (t,x)) 2 volume ≤ ENNReal.ofReal M),
      V12MixedEnergyBound a b v M ∧
      eLpNorm v 4 (v12_slab_measure a b) ≤ Z ∧
      V12CanonicalCoulombDistributionalEquation hHLS a b v hmv hv4 M hEv ∧
      V12CanonicalSpatialDistributionalConstraints a b v ∧
      V12SameFieldRealCoefficientConvergence a b (fun n => qn (σ n)) v ∧
      V12StrongLocalL2Convergence a b (fun n => qn (σ n)) v := by
  obtain ⟨σ, hσ, v, hmv, hv4, hEv, hbV, hP, hC, hCoeff, hQ⟩ :=
    v12_original_frequency_tightness_strong_L2_closure hHLS a b p hpc hps qn hc hs hn4
      M hM Z hZ hEn hb hCompat hPDE hTight
  exact ⟨σ, hσ, v, hmv, hv4, hEv, v12_mixed_energy_bound_of_slices a b v hmv M hM hEv,
    hbV, hP, hC, hCoeff, hQ⟩

#print axioms v12_original_frequency_tightness_full_spaces
end SMScattering.W20Full
