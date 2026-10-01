import lean.v12.V12_YZZWClosedSlabLocalClosure

/-! Literal strong convergence in each local L2 quotient, with membership of
both the sequence and limit proved. This prevents an ENNReal.toReal statement
from concealing an infinite norm. Original all-real-radius data is also
specialized explicitly to the countable exhaustion used by W. Pending CI. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

def V12StrongLocalL2Convergence (a b : ℝ)
    (qn : ℕ → V12Spacetime → V12Field) (u : V12Spacetime → V12Field) : Prop :=
  ∀ r : ℝ,
    ∃ (hu : MemLp u 2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)))
      (hn : ∀ n, MemLp (qn n) 2
        ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))),
      Tendsto (fun n => (hn n).toLp (qn n)) atTop (𝓝 (hu.toLp u))

theorem v12_L4_memLp2_on_real_cylinder
    (a b : ℝ) (q : V12Spacetime → V12Field)
    (hq : MemLp q 4 (v12_slab_measure a b)) (r : ℝ) :
    MemLp q 2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)) := by
  apply v12_local_memLp_all_real_radii a b q 2 _ r
  intro R
  letI : IsFiniteMeasure ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)) :=
    v12_cylinder_isFiniteMeasure a b R
  exact (hq.restrict (v12_spatial_cylinder R)).mono_exponent (by norm_num)

theorem v12_strong_local_L2_of_L4_and_norm_limits
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (u : V12Spacetime → V12Field)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (h : ∀ r : ℝ, MemLp u 2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)) ∧
      Tendsto (fun n => (eLpNorm (fun z => qn n z-u z) 2
        ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal) atTop (𝓝 0)) :
    V12StrongLocalL2Convergence a b qn u := by
  intro r
  let hn (n : ℕ) := v12_L4_memLp2_on_real_cylinder a b (qn n) (hn4 n) r
  refine ⟨(h r).1, hn, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (n : ℕ) : dist ((hn n).toLp (qn n)) ((h r).1.toLp u) =
      (eLpNorm (fun z => qn n z-u z) 2
        ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal := by
    rw [Lp.dist_def]
    apply congrArg ENNReal.toReal
    exact eLpNorm_congr_ae ((hn n).coeFn_toLp.sub (h r).1.coeFn_toLp)
  simpa only [he] using (h r).2

#print axioms v12_L4_memLp2_on_real_cylinder
#print axioms v12_strong_local_L2_of_L4_and_norm_limits

theorem v12_original_all_real_local_closure
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
    (hu2 : ∀ r : ℝ, MemLp u 2 ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)))
    (hlim : ∀ r : ℝ, Tendsto (fun n => (eLpNorm (fun z => qn n z-u z) 2
      ((v12_slab_measure a b).restrict (v12_real_spatial_cylinder r))).toReal) atTop (𝓝 0)) :
    ∃ (v : V12Spacetime → V12Field) (hmv : StronglyMeasurable v),
      v =ᵐ[v12_slab_measure a b] u ∧
      ∃ (hv4 : MemLp v 4 (v12_slab_measure a b))
        (hEv : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
          eLpNorm (fun x => v (t,x)) 2 volume ≤ ENNReal.ofReal M),
        eLpNorm v 4 (v12_slab_measure a b) ≤ Z ∧
        V12CanonicalCoulombDistributionalEquation hHLS a b v hmv hv4 M hEv ∧
        V12CanonicalSpatialDistributionalConstraints a b v ∧
        V12SameFieldRealCoefficientConvergence a b qn v ∧
        V12StrongLocalL2Convergence a b qn v := by
  have hu (R : ℕ) : MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)) := by
    simpa only [v12_real_spatial_cylinder, v12_spatial_cylinder] using hu2 ((R : ℝ)+1)
  have hl (R : ℕ) : Tendsto (fun n => (eLpNorm (fun z => qn n z-u z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
    simpa only [v12_real_spatial_cylinder, v12_spatial_cylinder] using hlim ((R : ℝ)+1)
  obtain ⟨v, hmv, hvu, hv4, hEv, hbV, hP, hC, hCoeff, hQ⟩ :=
    v12_closed_slab_original_local_closure hHLS a b qn u hc hs hn4 M hM Z hZ
      hEn hb hCompat hPDE hu hl
  exact ⟨v, hmv, hvu, hv4, hEv, hbV, hP, hC, hCoeff,
    v12_strong_local_L2_of_L4_and_norm_limits a b qn v hn4 hQ⟩

#print axioms v12_original_all_real_local_closure

end SMScattering.W20Full
