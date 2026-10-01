import lean.v12.V12_YZZVCompatibleLocalClosure
import lean.v12.V12_YZZKTOriginalDistributionExtension
import lean.v12.V12_YZZSESpatialConstraintExtension
import lean.v12.V12_YZZSFRealCoefficientExtension

/-! Original closed-slab smooth compatible sequence to all local-closure
conclusions. Global sequence measurability, local sequence L2 membership,
source-class correspondence, derivative/constraint extension and all-real
radii are proved. The only equation premises are the ORIGINAL reconstructed
advective distributional PDE and original spatial compatibility. No joint
A smoothness, A0 continuity, derived compact identity or coefficient limit
is imposed. Certification requires actual Lean execution and exact final
manuscript statement audit; this file is not itself a status assertion. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_closed_slab_original_local_closure
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (qn : ℕ → V12Spacetime → V12Field) (u : V12Spacetime → V12Field)
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
    (hu2 : ∀ R, MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z-u z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0)) :
    ∃ (v : V12Spacetime → V12Field) (hmv : StronglyMeasurable v),
      v =ᵐ[v12_slab_measure a b] u ∧
      ∃ (hv4 : MemLp v 4 (v12_slab_measure a b))
        (hEv : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
          eLpNorm (fun x => v (t,x)) 2 volume ≤ ENNReal.ofReal M),
        eLpNorm v 4 (v12_slab_measure a b) ≤ Z ∧
        V12CanonicalCoulombDistributionalEquation hHLS a b v hmv hv4 M hEv ∧
        V12CanonicalSpatialDistributionalConstraints a b v ∧
        V12SameFieldRealCoefficientConvergence a b qn v ∧
        ∀ r : ℝ, MemLp v 2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)) ∧
          Tendsto (fun n => (eLpNorm (fun z => qn n z-v z) 2
            ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal) atTop (𝓝 0) := by
  let μ := v12_slab_measure a b
  let ext := fun n => v12_smoothSlabExtension a b (qn n)
  have hmn n := v12_smoothSlabExtension_stronglyMeasurable a b (qn n) (hc n)
  have h4 n := v12_smoothSlabExtension_memLp a b (qn n) 4 (hn4 n)
  have hE n := v12_smoothSlabExtension_energy a b (qn n) M (hEn n)
  have hbound (n : ℕ) : eLpNorm (ext n) 4 μ ≤ Z := by
    rw [v12_smoothSlabExtension_eLpNorm]
    exact hb n
  have h2 (R n : ℕ) : MemLp (ext n) 2 (μ.restrict (v12_spatial_cylinder R)) := by
    letI : IsFiniteMeasure (μ.restrict (v12_spatial_cylinder R)) :=
      v12_cylinder_isFiniteMeasure a b R
    exact ((h4 n).restrict (v12_spatial_cylinder R)).mono_exponent (by norm_num)
  have hsComp (n : ℕ) (j : Fin 2) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ext n z j) (Prod.fst ⁻¹' Set.Ioo a b) :=
    v12_component_contDiffOn a b (ext n) j
      (v12_smoothSlabExtension_contDiffOn a b (qn n) (hs n))
  have hCompatExt (n : ℕ) := v12_original_spatial_constraints_extension a b (qn n) (hCompat n)
  have hPDEExt (n : ℕ) (j : Fin 2) := v12_original_distributional_PDE_extension hHLS a b
    (qn n) (hc n) (hn4 n) M (hEn n) j v12_timeDirection
    (v12_spatialDirection 0) (v12_spatialDirection 1) (hPDE n j)
  have hnorm (R n : ℕ) : eLpNorm (fun z => ext n z-u z) 2
      (μ.restrict (v12_spatial_cylinder R)) = eLpNorm (fun z => qn n z-u z) 2
      (μ.restrict (v12_spatial_cylinder R)) := by
    apply eLpNorm_congr_ae
    filter_upwards [(v12_smoothSlabExtension_ae a b (qn n)).restrict (s := v12_spatial_cylinder R)] with z hz
    change ext n z = qn n z at hz
    rw [hz]
  have hlimExt (R : ℕ) : Tendsto (fun n => (eLpNorm (fun z => ext n z-u z) 2
      (μ.restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
    simpa only [hnorm] using hlim R
  obtain ⟨v, hmv, hvu, hv4, hEv, hB, hP, hC, hLC, hRC, hQ⟩ :=
    v12_same_field_distributional_local_closure hHLS a b ext u hmn h4 h2 hu2 hlimExt
      M hM hE Z hZ hbound hsComp hCompatExt hPDEExt
  have hRaw := v12_real_coefficient_convergence_of_extension a b qn v hRC
  refine ⟨v, hmv, hvu, hv4, hEv, hB, hP, hC, hRaw, ?_⟩
  intro r
  have hn (n : ℕ) : eLpNorm (fun z => ext n z-v z) 2
      (μ.restrict (v12_real_spatial_cylinder r)) = eLpNorm (fun z => qn n z-v z) 2
      (μ.restrict (v12_real_spatial_cylinder r)) := by
    apply eLpNorm_congr_ae
    filter_upwards [(v12_smoothSlabExtension_ae a b (qn n)).restrict (s := v12_real_spatial_cylinder r)] with z hz
    change ext n z = qn n z at hz
    rw [hz]
  refine ⟨(hQ r).1, ?_⟩
  simpa only [hn] using (hQ r).2

#print axioms v12_closed_slab_original_local_closure
end SMScattering.W20Full
