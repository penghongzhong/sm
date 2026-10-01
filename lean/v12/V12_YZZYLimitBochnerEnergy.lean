import lean.v12.V12_YZZXStrongLocalL2Closure
import lean.v12.V12_YUEveryTimeBochnerEnergy

/-! The inherited a.e. energy bound of the measurable limit is realized in
literal Bochner L-infinity(time;L2(space)), without continuity of that limit.
The representative and its Bochner measurability are constructed from the
same joint field, not given as an interface. Pending CI. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

def V12MixedEnergyBound (a b : ℝ) (q : V12Spacetime → V12Field) (M : ℝ) : Prop :=
  ∃ Q : ℝ → V12SpatialL2,
    (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      (Q t : V12Spatial → V12Field) =ᵐ[volume] (fun x => q (t,x))) ∧
    MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)) ∧
    eLpNorm Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ ENNReal.ofReal M

theorem v12_mixed_energy_bound_of_slices
    (a b : ℝ) (q : V12Spacetime → V12Field) (hm : StronglyMeasurable q)
    (M : ℝ) (hM : 0 ≤ M)
    (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) :
    V12MixedEnergyBound a b q M := by
  classical
  let μ := (volume : Measure ℝ).restrict (Set.Icc a b)
  let Q : ℝ → V12SpatialL2 := fun t =>
    if h : MemLp (fun x => q (t,x)) 2 (volume : Measure V12Spatial)
    then h.toLp (fun x => q (t,x)) else 0
  have hrep : ∀ᵐ t ∂μ, (Q t : V12Spatial → V12Field) =ᵐ[volume] (fun x => q (t,x)) := by
    filter_upwards [hE] with t ht
    have h2 : MemLp (fun x => q (t,x)) 2 (volume : Measure V12Spatial) :=
      ht.trans_lt (by finiteness)
    simp only [Q, dif_pos h2]
    exact h2.coeFn_toLp
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hQM := v12_aestronglyMeasurable_Lp_sections μ 2 q hm.aestronglyMeasurable Q hrep
  have hnorm : ∀ᵐ t ∂μ, ‖Q t‖ ≤ M := by
    filter_upwards [hE] with t ht
    have h2 : MemLp (fun x => q (t,x)) 2 (volume : Measure V12Spatial) :=
      ht.trans_lt (by finiteness)
    simp only [Q, dif_pos h2, Lp.norm_toLp]
    exact (ENNReal.toReal_mono (by finiteness) ht).trans_eq (ENNReal.toReal_ofReal hM)
  refine ⟨Q, hrep, memLp_top_of_bound hQM M hnorm, ?_⟩
  rw [eLpNorm_exponent_top hQM]
  exact eLpNormEssSup_le_of_ae_bound hnorm

#print axioms v12_mixed_energy_bound_of_slices

theorem v12_original_local_closure_with_mixed_norm
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
        V12MixedEnergyBound a b v M ∧
        eLpNorm v 4 (v12_slab_measure a b) ≤ Z ∧
        V12CanonicalCoulombDistributionalEquation hHLS a b v hmv hv4 M hEv ∧
        V12CanonicalSpatialDistributionalConstraints a b v ∧
        V12SameFieldRealCoefficientConvergence a b qn v ∧
        V12StrongLocalL2Convergence a b qn v := by
  obtain ⟨v, hmv, hvu, hv4, hEv, hbV, hP, hC, hCoeff, hQ⟩ :=
    v12_original_all_real_local_closure hHLS a b qn u hc hs hn4 M hM Z hZ
      hEn hb hCompat hPDE hu2 hlim
  exact ⟨v, hmv, hvu, hv4, hEv, v12_mixed_energy_bound_of_slices a b v hmv M hM hEv,
    hbV, hP, hC, hCoeff, hQ⟩

#print axioms v12_original_local_closure_with_mixed_norm

end SMScattering.W20Full
