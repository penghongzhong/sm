import lean.v12.V12_ZKSOriginalCommonLimit
import lean.v12.V12_YZZWClosedSlabLocalClosure

/-! Candidate for the full 7.2 dependency chain: original smooth compatible
sequence, original MZ bounds and raw frequency tightness -> a single common
subsequence, measurable local limit, inherited MZ, original distributional
PDE/constraints and all-real-radius coefficient/field convergence. The SAME
subsequence is passed to 7.1. Degenerate/empty slabs are included upstream.
No hIntegral, hCompact, source budget or local-limit hypothesis is an input.
NOT CERTIFIED until every dependency compiles and literal paper audit closes. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_original_frequency_tightness_with_closure
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
      eLpNorm v 4 (v12_slab_measure a b) ≤ Z ∧
      V12CanonicalCoulombDistributionalEquation hHLS a b v hmv hv4 M hEv ∧
      V12CanonicalSpatialDistributionalConstraints a b v ∧
      V12SameFieldRealCoefficientConvergence a b (fun n => qn (σ n)) v ∧
      ∀ r : ℝ, MemLp v 2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)) ∧
        Tendsto (fun n => (eLpNorm (fun z => qn (σ n) z-v z) 2
          ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal) atTop (𝓝 0) := by
  have hdiv (n : ℕ) (φ : V12Spacetime → ℂ)
      (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hcφ : HasCompactSupport φ)
      (hsφ : tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b) :
      (∫ z, v12_actualCoulombA (qn n) 0 z * fderiv ℝ φ z (v12_spatialDirection 0)
        ∂v12_slab_measure a b) +
      (∫ z, v12_actualCoulombA (qn n) 1 z * fderiv ℝ φ z (v12_spatialDirection 1)
        ∂v12_slab_measure a b) = 0 := by
    have he := (hCompat n φ hφ hcφ hsφ).1
    linear_combination -1 * he
  obtain ⟨σ, u, hσ, hu, hlocal⟩ := v12_common_limit_original_distribution_all_slabs
    hHLS a b p hpc hps qn hc hs hn4 M hM Z hZ hb hEn hdiv hPDE hTight
  obtain ⟨v, hmv, hvu, hv4, hEv, hZb, hP, hC, hCoeff, hQ⟩ :=
    v12_closed_slab_original_local_closure hHLS a b (fun n => qn (σ n)) u
      (fun n => hc (σ n)) (fun n => hs (σ n)) (fun n => hn4 (σ n)) M hM Z hZ
      (fun n => hEn (σ n)) (fun n => hb (σ n)) (fun n => hCompat (σ n))
      (fun n => hPDE (σ n)) (fun R => (hlocal R).1) (fun R => (hlocal R).2.2)
  exact ⟨σ, hσ, v, hmv, hv4, hEv, hZb, hP, hC, hCoeff, hQ⟩

#print axioms v12_original_frequency_tightness_with_closure
end SMScattering.W20Full
