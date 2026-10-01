import lean.v12.V12_YZZSCanonicalClosureStatements

/-! Closure of the ORIGINAL spatial distributional compatibility equations.
The three input equations are exactly div A=0, curl A=B and D1 Q2=D2 Q1
from v12:eq:curv-constraints--v12:eq:Q-system. Coefficient test convergence
and inherited budgets are proved from the same Q, not assumed. No smoothness
of A or pointwise representative of these original distributions is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_original_distributional_constraints_closed
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hmn : ∀ n, StronglyMeasurable (qn n)) (hmq : StronglyMeasurable q)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z-q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn n (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z)
    (hCompat : ∀ n, V12CanonicalSpatialDistributionalConstraints a b (qn n)) :
    V12CanonicalSpatialDistributionalConstraints a b q := by
  intro ψ hψ hc hs
  let μ := v12_slab_measure a b
  have hA (j : Fin 2) (v : V12Spacetime) := v12_actual_connection_compact_derivative_limit
    hHLS a b qn q hmn hmq hn4 hn2 hq2 hlim M hM hEn Z hZ hb j ψ hψ hc v
  have hB := v12_actual_curvature_compact_test_limit a b qn q hn2 hq2 hlim ψ hc hψ.continuous
  have hD (k j : Fin 2) := v12_actual_scalar_drift_compact_limit hHLS a b qn q hmn hmq
    hn4 hn2 hq2 hlim M hM hEn Z hZ hb k j ψ hψ.continuous hc
  have hnC (j : Fin 2) (R n : ℕ) : MemLp (fun z => qn n z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 (qn n) (hn2 R n).aestronglyMeasurable j).trans_lt (hn2 R n)
  have hqC (j : Fin 2) (R : ℕ) : MemLp (fun z => q z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 q (hq2 R).aestronglyMeasurable j).trans_lt (hq2 R)
  have hQ (j : Fin 2) (v : V12Spacetime) : Tendsto (fun n => ∫ z,
      qn n z j * fderiv ℝ ψ z v ∂μ) atTop (𝓝 (∫ z, q z j * fderiv ℝ ψ z v ∂μ)) := by
    have h := v12_raw_local_L2_derivative_test_limit a b (fun n z => qn n z j) (fun z => q z j)
      (hnC j) (hqC j) (fun R => v12_raw_component_L2_limit _ qn q (hn2 R) (hq2 R) (hlim R) j)
      ψ hψ hc v
    simpa only [smul_eq_mul, mul_comm] using h
  have hdivI (n : ℕ) := (hCompat n ψ hψ hc hs).1
  have hcurlI (n : ℕ) := (hCompat n ψ hψ hc hs).2.1
  have htorI (n : ℕ) := (hCompat n ψ hψ hc hs).2.2
  have hdivL := ((hA 0 (v12_spatialDirection 0)).neg).sub (hA 1 (v12_spatialDirection 1))
  rw [funext hdivI] at hdivL
  have hdivOut := tendsto_nhds_unique hdivL tendsto_const_nhds
  have hcurlL := ((hA 1 (v12_spatialDirection 0)).neg).add (hA 0 (v12_spatialDirection 1))
  rw [funext hcurlI] at hcurlL
  have hcurlOut := tendsto_nhds_unique hcurlL hB
  have htorL := ((hQ 1 (v12_spatialDirection 0)).neg).add (hQ 0 (v12_spatialDirection 1))
  rw [funext htorI] at htorL
  have htorOut := tendsto_nhds_unique htorL (((hD 0 1).sub (hD 1 0)).const_mul Complex.I)
  exact ⟨hdivOut, hcurlOut, htorOut⟩

#print axioms v12_original_distributional_constraints_closed
end SMScattering.W20Full
