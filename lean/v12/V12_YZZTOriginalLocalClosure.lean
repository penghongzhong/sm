import lean.v12.V12_YZZSCanonicalClosureStatements
import lean.v12.V12_YZZBVOriginalScalarPDE

/-! Original smooth same-Q fields to all local-closure conclusions. The
limit is represented by a strongly measurable function derived from local
L2 membership, rather than imposing global measurability as a new assumption.
All coordinate equations, zero-extension applicability, coefficient limits
and inherited budgets are proved from the original data. -/
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_original_local_closure
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (q : ℕ → ℝ → V12Spatial → V12Field)
    (A0 V : ℕ → V12Spacetime → ℂ)
    (hqcont : ∀ n, ContinuousOn (Function.uncurry (q n)) (Set.Icc a b ×ˢ Set.univ))
    (hqSmooth : ∀ n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (q n)) (Prod.fst ⁻¹' Set.Ioo a b))
    (hASmooth : ∀ n k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (v12_actualCoulombA (Function.uncurry (q n)) k) (Prod.fst ⁻¹' Set.Ioo a b))
    (hA0cont : ∀ n, ContinuousOn (A0 n) (Set.Icc a b ×ˢ Set.univ))
    (hq4 : ∀ n, MemLp (Function.uncurry (q n)) 4 (v12_slab_measure a b))
    (hA0formula : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      ∀ ht : MemLp (q n t) 4 (volume : Measure V12Spatial),
      (fun x => A0 n (t,x)) =ᵐ[volume]
      (v12_temporalCoulombClass
        (fun j k => v12_SL2Class volume j k (q n t) ht)
        (v12_massComplexL2Class volume (q n t) ht) : V12Spatial → ℂ))
    (hVformula : ∀ n z, V n z = -A0 n z +
      ((‖v12_spacetimeHodge (Function.uncurry (q n)) z‖^2 : ℝ) : ℂ) -
      (2 : ℂ) * ((‖Function.uncurry (q n) z‖^2 : ℝ) : ℂ))
    (hdiv : ∀ n t, t ∈ Set.Ioo a b → ∀ y,
      fderiv ℝ (fun x => v12_actualCoulombA (Function.uncurry (q n)) 0 (t,x)) y
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (fun x => v12_actualCoulombA (Function.uncurry (q n)) 1 (t,x)) y
          (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0)
    (hcurl : ∀ n t, t ∈ Set.Ioo a b → ∀ x,
      fderiv ℝ (fun y => v12_actualCoulombA (Function.uncurry (q n)) 1 (t,y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) -
      fderiv ℝ (fun y => v12_actualCoulombA (Function.uncurry (q n)) 0 (t,y)) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) = (v12_curvatureDensity (q n t x) : ℂ))
    (htorsion : ∀ n t, t ∈ Set.Ioo a b → ∀ x,
      fderiv ℝ (fun y => q n t y 1) x (EuclideanSpace.basisFun (Fin 2) ℝ 0) -
      fderiv ℝ (fun y => q n t y 0) x (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      Complex.I * (v12_actualCoulombA (Function.uncurry (q n)) 0 (t,x) * q n t x 1 -
        v12_actualCoulombA (Function.uncurry (q n)) 1 (t,x) * q n t x 0))
    (hCoulomb : ∀ n t, t ∈ Set.Ioo a b → ∀ y,
      let e := EuclideanSpace.basisFun (Fin 2) ℝ
      Complex.I • deriv (fun s => q n s y) t +
        (fderiv ℝ (fun x => fderiv ℝ (q n t) x (e 0)) y (e 0) +
         fderiv ℝ (fun x => fderiv ℝ (q n t) x (e 1)) y (e 1)) =
      (2 * Complex.I) •
        (v12_actualCoulombA (Function.uncurry (q n)) 0 (t,y) • fderiv ℝ (q n t) y (e 0) +
         v12_actualCoulombA (Function.uncurry (q n)) 1 (t,y) • fderiv ℝ (q n t) y (e 1)) +
      v12_zeroOrderProduct (V n) (fun z => v12_WDensity (Function.uncurry (q n) z))
        (Function.uncurry (q n)) (t,y))
    (M : ℝ) (hM : 0 ≤ M) (Z : ℝ≥0∞) (hZ : Z ≠ ∞)
    (hEnergy : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (q n t) 2 volume ≤ ENNReal.ofReal M)
    (hqbound : ∀ n, eLpNorm (Function.uncurry (q n)) 4 (v12_slab_measure a b) ≤ Z)
    (u : V12Spacetime → V12Field)
    (hn2 : ∀ R n, MemLp (Function.uncurry (q n)) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hu2 : ∀ R, MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => q n z.1 z.2-u z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0)) :
    ∃ (v : V12Spacetime → V12Field) (hmv : StronglyMeasurable v),
      v =ᵐ[v12_slab_measure a b] u ∧
      ∃ (hv4 : MemLp v 4 (v12_slab_measure a b))
        (hEv : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
          eLpNorm (fun x => v (t,x)) 2 volume ≤ ENNReal.ofReal M),
        eLpNorm v 4 (v12_slab_measure a b) ≤ Z ∧
        V12CanonicalCoulombDistributionalEquation hHLS a b v hmv hv4 M hEv ∧
        V12CanonicalSpatialDistributionalConstraints a b v ∧
        V12SameFieldLocalCoefficientConvergence a b (fun n => Function.uncurry (q n)) v := by
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
  let ext := fun n => v12_smoothSlabExtension a b (Function.uncurry (q n))
  have hmn n := v12_smoothSlabExtension_stronglyMeasurable a b _ (hqcont n)
  have hn4 n := v12_smoothSlabExtension_memLp a b _ 4 (hq4 n)
  have hEe n := v12_smoothSlabExtension_energy a b _ M (hEnergy n)
  have hext (n : ℕ) : ext n =ᵐ[μ] Function.uncurry (q n) :=
    v12_smoothSlabExtension_ae a b (Function.uncurry (q n))
  have hen2 (R n : ℕ) : MemLp (ext n) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (hn2 R n).ae_eq (Filter.EventuallyEq.symm ((hext n).restrict))
  have hbext (n : ℕ) : eLpNorm (ext n) 4 μ ≤ Z := by
    rw [v12_smoothSlabExtension_eLpNorm]
    exact hqbound n
  have hnormOrig (R n : ℕ) : eLpNorm (fun z => q n z.1 z.2-v z) 2
      (μ.restrict (v12_spatial_cylinder R)) = eLpNorm (fun z => q n z.1 z.2-u z) 2
      (μ.restrict (v12_spatial_cylinder R)) := by
    apply eLpNorm_congr_ae
    filter_upwards [huv.restrict (s := v12_spatial_cylinder R)] with z hz
    rw [hz]
  have hnormExt (R n : ℕ) : eLpNorm (fun z => ext n z-v z) 2
      (μ.restrict (v12_spatial_cylinder R)) = eLpNorm (fun z => q n z.1 z.2-u z) 2
      (μ.restrict (v12_spatial_cylinder R)) := by
    apply eLpNorm_congr_ae
    filter_upwards [(hext n).restrict (s := v12_spatial_cylinder R), huv.restrict (s := v12_spatial_cylinder R)]
      with z he hu
    rw [he, hu]
  have hlimOrig (R : ℕ) : Tendsto (fun n => (eLpNorm (fun z => q n z.1 z.2-v z) 2
      (μ.restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
    simpa only [hnormOrig] using hlim R
  have hlimExt (R : ℕ) : Tendsto (fun n => (eLpNorm (fun z => ext n z-v z) 2
      (μ.restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
    simpa only [hnormExt] using hlim R
  have hs n := v12_original_extended_spatial_constraints a b (q n) (hqSmooth n)
    (hASmooth n) (hdiv n) (hcurl n) (htorsion n)
  let dq := fun n t x => deriv (fun s => q n s x) t
  have hder (n : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo a b) (x : V12Spatial) :
      HasDerivAt (fun s => q n s x) (dq n t x) t :=
    v12_joint_smooth_time_hasDerivAt a b (Function.uncurry (q n)) (hqSmooth n) t ht x
  have hp n := v12_original_extended_scalar_PDE hHLS a b (q n) (dq n) (A0 n) (V n)
    (hqcont n) (hqSmooth n) (hq4 n) M (hEnergy n) (hA0cont n) (hA0formula n)
    (hVformula n) (hder n) (hCoulomb n)
  obtain ⟨hv4, hEv, hP⟩ := v12_actual_Coulomb_PDE_distributional_closure hHLS a b ext v
    hmn hmv hn4 hen2 hv2 hlimExt M hM hEe Z hZ hbext v12_timeDirection
    (v12_spatialDirection 0) (v12_spatialDirection 1)
    (fun n => (hs n).1) (fun n => (hs n).2.1) (fun n => (hs n).2.2.1) hp
  have hC := v12_actual_spatial_constraints_distributional_closure hHLS a b ext v
    hmn hmv hn4 hen2 hv2 hlimExt M hM hEe Z hZ hbext
    (v12_spatialDirection 0) (v12_spatialDirection 1)
    (fun n => (hs n).1) (fun n => (hs n).2.1) (fun n => (hs n).2.2.1)
    (fun n => (hs n).2.2.2.1) (fun n => (hs n).2.2.2.2)
  have hB := v12_global_budget_inherited_from_local_L2 a b ext v hmv hen2 hv2 hlimExt 4 Z hbext
  refine ⟨v, hmv, huv.symm, hv4, hEv, hB, hP, hC, ?_⟩
  intro R
  have hcurv := v12_raw_curvature_L1_limit (μ.restrict (v12_spatial_cylinder R))
    (fun n => Function.uncurry (q n)) v (hn2 R) (hv2 R) (hlimOrig R)
  have hH := v12_actual_Hodge_local_L2_limit hHLS a b R ext v hmn hmv hn4 hv4 hen2 hv2
    hlimExt M hM hEe hEv Z hZ hbext
  have hHae (n : ℕ) : (fun z => v12_spacetimeHodge (ext n) z-v12_spacetimeHodge v z)
      =ᵐ[μ.restrict (v12_spatial_cylinder R)]
      (fun z => v12_spacetimeHodge (Function.uncurry (q n)) z-v12_spacetimeHodge v z) := by
    filter_upwards [(v12_smoothSlabExtension_Hodge_ae a b (Function.uncurry (q n))).restrict
      (v12_spatial_cylinder R)] with z hz
    rw [hz]
  have hHnorm n := eLpNorm_congr_ae (hHae n) (p := (2 : ℝ≥0∞))
  have hHlim : Tendsto (fun n => (eLpNorm (fun z =>
      v12_spacetimeHodge (Function.uncurry (q n)) z-v12_spacetimeHodge v z) 2
      (μ.restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
    simpa only [hHnorm] using hH.2
  refine ⟨hcurv.1, hcurv.2, (fun n => (hH.1 n).ae_eq (hHae n)), hHlim, ?_⟩
  intro j
  have hD := v12_actual_Coulomb_drift_local_L1_limit hHLS a b R j ext v hmn hmv hn4 hv4
    hen2 hv2 hlimExt M hM hEe hEv Z hZ hbext
  have hDnorm (n : ℕ) : eLpNorm (fun z => v12_actualCoulombA (ext n) j z • ext n z -
      v12_actualCoulombA v j z • v z) 1 (μ.restrict (v12_spatial_cylinder R)) =
      eLpNorm (fun z => v12_actualCoulombA (Function.uncurry (q n)) j z • q n z.1 z.2 -
        v12_actualCoulombA v j z • v z) 1 (μ.restrict (v12_spatial_cylinder R)) := by
    apply eLpNorm_congr_ae
    filter_upwards [(hext n).restrict (s := v12_spatial_cylinder R),
      (v12_smoothSlabExtension_Hodge_ae a b (Function.uncurry (q n))).restrict
        (v12_spatial_cylinder R)] with z hqz hAz
    simp only [v12_actualCoulombA, hqz, hAz]
  simpa only [hDnorm] using hD

#print axioms v12_original_local_closure
end SMScattering.W20Full
