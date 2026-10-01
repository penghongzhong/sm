import lean.v12.V12_YZZSDRealCoefficientConvergence
import lean.v12.V12_YZZNEOriginalDistributionClosure
import lean.v12.V12_YZZUOriginalConstraintClosure
import lean.v12.V12_YNRealCylinderRestriction

/-! Same-field local closure from the ORIGINAL advective distributional PDE
and spatial compatibility. No joint smoothness or continuous representative
of A/A0/V is required. The limit's strong measurability is constructed.
This core uses globally measurable representatives of the original sequence;
the closed-slab representative application remains a separate proof obligation.
No derived compact PDE identity or coefficient convergence is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_same_field_distributional_local_closure
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (qn : ℕ → V12Spacetime → V12Field) (u : V12Spacetime → V12Field)
    (hmn : ∀ n, StronglyMeasurable (qn n))
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hu2 : ∀ R, MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z-u z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn n (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z)
    (hqSmooth : ∀ n j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => qn n z j) (Prod.fst ⁻¹' Set.Ioo a b))
    (hCompat : ∀ n, V12CanonicalSpatialDistributionalConstraints a b (qn n))
    (hPDE : ∀ n j, V12OriginalScalarDistributionalPDE a b (fun z => qn n z j)
      (v12_actualCoulombA (qn n))
      (v12_actualScalarZeroOrder hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n) j)
      v12_timeDirection (v12_spatialDirection 0) (v12_spatialDirection 1)) :
    ∃ (v : V12Spacetime → V12Field) (hmv : StronglyMeasurable v),
      v =ᵐ[v12_slab_measure a b] u ∧
      ∃ (hv4 : MemLp v 4 (v12_slab_measure a b))
        (hEv : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
          eLpNorm (fun x => v (t,x)) 2 volume ≤ ENNReal.ofReal M),
        eLpNorm v 4 (v12_slab_measure a b) ≤ Z ∧
        V12CanonicalCoulombDistributionalEquation hHLS a b v hmv hv4 M hEv ∧
        V12CanonicalSpatialDistributionalConstraints a b v ∧
        V12SameFieldLocalCoefficientConvergence a b qn v ∧
        V12SameFieldRealCoefficientConvergence a b qn v ∧
        ∀ r : ℝ, MemLp v 2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)) ∧
          Tendsto (fun n => (eLpNorm (fun z => qn n z-v z) 2
            ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal) atTop (𝓝 0) := by
  let μ := v12_slab_measure a b
  have hmu : AEStronglyMeasurable u μ := by
    have h := AEStronglyMeasurable.iUnion (fun R => (hu2 R).aestronglyMeasurable)
    rw [v12_spatial_cylinder_iUnion, Measure.restrict_univ] at h
    exact h
  let v := hmu.mk u
  have hmv : StronglyMeasurable v := hmu.stronglyMeasurable_mk
  have huv : u =ᵐ[μ] v := hmu.ae_eq_mk
  have hv2 (R : ℕ) : MemLp v 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (hu2 R).ae_eq (huv.restrict)
  have hnorm (R n : ℕ) : eLpNorm (fun z => qn n z-v z) 2
      (μ.restrict (v12_spatial_cylinder R)) = eLpNorm (fun z => qn n z-u z) 2
      (μ.restrict (v12_spatial_cylinder R)) := by
    apply eLpNorm_congr_ae
    filter_upwards [huv.restrict (s := v12_spatial_cylinder R)] with z hz
    rw [hz]
  have hlimv (R : ℕ) : Tendsto (fun n => (eLpNorm (fun z => qn n z-v z) 2
      (μ.restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
    simpa only [hnorm] using hlim R
  have hdiv (n : ℕ) (ψ : V12Spacetime → ℂ)
      (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b) :
      (∫ z, v12_actualCoulombA (qn n) 0 z * fderiv ℝ ψ z (v12_spatialDirection 0) ∂μ) +
      (∫ z, v12_actualCoulombA (qn n) 1 z * fderiv ℝ ψ z (v12_spatialDirection 1) ∂μ) = 0 := by
    have h := (hCompat n ψ hψ hc hs).1
    linear_combination -h
  obtain ⟨hv4, hEv, hP⟩ := v12_actual_Coulomb_PDE_closure_original_distribution hHLS a b qn v
    hmn hmv hn4 hn2 hv2 hlimv M hM hEn Z hZ hb v12_timeDirection
    (v12_spatialDirection 0) (v12_spatialDirection 1) hqSmooth hdiv hPDE
  have hC := v12_original_distributional_constraints_closed hHLS a b qn v hmn hmv hn4
    hn2 hv2 hlimv M hM hEn Z hZ hb hCompat
  have hB := v12_global_budget_inherited_from_local_L2 a b qn v hmv hn2 hv2 hlimv 4 Z hb
  have hCoeffs : V12SameFieldLocalCoefficientConvergence a b qn v := by
    intro R
    have hcurv := v12_raw_curvature_L1_limit (μ.restrict (v12_spatial_cylinder R))
      qn v (hn2 R) (hv2 R) (hlimv R)
    have hH := v12_actual_Hodge_local_L2_limit hHLS a b R qn v hmn hmv hn4 hv4 hn2 hv2
      hlimv M hM hEn hEv Z hZ hb
    refine ⟨hcurv.1, hcurv.2, hH.1, hH.2, ?_⟩
    intro j
    exact v12_actual_Coulomb_drift_local_L1_limit hHLS a b R j qn v hmn hmv hn4 hv4
      hn2 hv2 hlimv M hM hEn hEv Z hZ hb
  have hReal := v12_same_field_coefficients_all_real_radii hHLS a b qn v
    hmn hmv hn4 hv4 M hEn hEv hCoeffs
  refine ⟨v, hmv, huv.symm, hv4, hEv, hB, hP, hC, hCoeffs, hReal, ?_⟩
  intro r
  refine ⟨v12_local_memLp_all_real_radii a b v 2 hv2 r, ?_⟩
  exact v12_local_eLpNorm_limit_all_real_radii a b (fun n z => qn n z-v z) 2
      (fun R n => (hn2 R n).sub (hv2 R)) hlimv r

#print axioms v12_same_field_distributional_local_closure
end SMScattering.W20Full
