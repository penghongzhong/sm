import lean.v12.V12_YZZSCanonicalClosureStatements
import lean.v12.V12_YNSRealCylinderIntegral

/-! Every real-radius coefficient conclusion, with actual finite AQ norms
proved from the same-field MZ budget before transferring toReal limits. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

def V12SameFieldRealCoefficientConvergence
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field) : Prop :=
  ∀ r : ℝ,
    (∀ n, Integrable (fun z => v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z))
      ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))) ∧
    Tendsto (fun n => ∫ z, ‖v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z)‖
      ∂((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))) atTop (𝓝 0) ∧
    (∀ n, MemLp (fun z => v12_spacetimeHodge (qn n) z - v12_spacetimeHodge q z)
      2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))) ∧
    Tendsto (fun n => (eLpNorm (fun z => v12_spacetimeHodge (qn n) z-v12_spacetimeHodge q z)
      2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal) atTop (𝓝 0) ∧
    ∀ j, (∀ n, MemLp (fun z => v12_actualCoulombA (qn n) j z • qn n z -
      v12_actualCoulombA q j z • q z) 1
      ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))) ∧
      Tendsto (fun n => (eLpNorm (fun z => v12_actualCoulombA (qn n) j z • qn n z -
      v12_actualCoulombA q j z • q z) 1
      ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal) atTop (𝓝 0)


theorem v12_same_field_coefficients_all_real_radii
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hmn : ∀ n, StronglyMeasurable (qn n)) (hmq : StronglyMeasurable q)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hq4 : MemLp q 4 (v12_slab_measure a b)) (M : ℝ)
    (hEn : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn n (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (hlocal : V12SameFieldLocalCoefficientConvergence a b qn q) :
    V12SameFieldRealCoefficientConvergence a b qn q := by
  let μ := v12_slab_measure a b
  obtain ⟨C, hC, hD⟩ := v12_actualCoulomb_drift_MZZ hHLS
  have hDrift (R n : ℕ) (j : Fin 2) : MemLp
      (fun z => v12_actualCoulombA (qn n) j z • qn n z-v12_actualCoulombA q j z • q z)
      1 (μ.restrict (v12_spatial_cylinder R)) := by
    have hn := (hD a b (qn n) (hmn n) (hn4 n) (ENNReal.ofReal M) (by finiteness) (hEn n) j).1
    have hq := (hD a b q hmq hq4 (ENNReal.ofReal M) (by finiteness) hEq j).1
    have h : MemLp (fun z => v12_driftProduct (v12_actualCoulombA (qn n)) (qn n) j z -
        v12_driftProduct (v12_actualCoulombA q) q j z) 1 (μ.restrict (v12_spatial_cylinder R)) :=
      ((hn.sub hq).restrict (v12_spatial_cylinder R)).mono_exponent (by norm_num)
    simpa only [v12_driftProduct] using h
  intro r
  have hB := v12_local_integral_norm_limit_all_real_radii a b
    (fun n z => v12_curvatureDensity (qn n z)-v12_curvatureDensity (q z))
    (fun R => (hlocal R).1) (fun R => (hlocal R).2.1) r
  refine ⟨hB.1, hB.2, ?_, ?_, ?_⟩
  · intro n
    exact v12_local_memLp_all_real_radii a b
      (fun z => v12_spacetimeHodge (qn n) z-v12_spacetimeHodge q z) 2
      (fun R => (hlocal R).2.2.1 n) r
  · exact v12_local_eLpNorm_limit_all_real_radii a b
      (fun n z => v12_spacetimeHodge (qn n) z-v12_spacetimeHodge q z) 2
      (fun R => (hlocal R).2.2.1) (fun R => (hlocal R).2.2.2.1) r
  · intro j
    refine ⟨?_, ?_⟩
    · intro n
      exact v12_local_memLp_all_real_radii a b
        (fun z => v12_actualCoulombA (qn n) j z • qn n z-v12_actualCoulombA q j z • q z) 1
        (fun R => hDrift R n j) r
    · exact v12_local_eLpNorm_limit_all_real_radii a b
        (fun n z => v12_actualCoulombA (qn n) j z • qn n z-v12_actualCoulombA q j z • q z) 1
        (fun R n => hDrift R n j) (fun R => (hlocal R).2.2.2.2 j) r

#print axioms v12_same_field_coefficients_all_real_radii
end SMScattering.W20Full
