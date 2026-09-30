import lean.v12.V12_YZZIActualDriftTest

/-! Coordinate tests of the actual vector drift. Projection commutes with
the Bochner integral because weighted integrability is derived from the
original MZ^2 source bound. Limit-field budgets are inherited internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_scalar_drift_derivative_limit
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
    (k j : Fin 2) (ψ : V12Spacetime → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (v : V12Spacetime) :
    Tendsto (fun n => ∫ z,
      (v12_actualCoulombA (qn n) k z * qn n z j) * fderiv ℝ ψ z v ∂v12_slab_measure a b)
      atTop (𝓝 (∫ z, (v12_actualCoulombA q k z * q z j) * fderiv ℝ ψ z v
        ∂v12_slab_measure a b)) := by
  let μ := v12_slab_measure a b
  have hq4 : MemLp q 4 μ :=
    (v12_global_budget_inherited_from_local_L2 a b qn q hmq hn2 hq2 hlim 4 Z hb).trans_lt
      (lt_top_iff_ne_top.mpr hZ)
  have hEq := v12_global_energy_inherited a b qn q hmq hn2 hq2 hlim
    (ENNReal.ofReal M) (by finiteness) hEn
  have ht := v12_actual_drift_compact_derivative_limit hHLS a b qn q hmn hmq hn4 hn2 hq2
    hlim M hM hEn Z hZ hb k ψ hψ hc v
  let P := EuclideanSpace.proj (𝕜 := ℂ) j
  have h := P.continuous.tendsto _ |>.comp ht
  obtain ⟨C, hC, hDrift⟩ := v12_actualCoulomb_drift_MZZ hHLS
  obtain ⟨hcd, hdψ⟩ := v12_compact_spacetime_test_derivative ψ hψ hc v
  have he (r : V12Spacetime → V12Field) (hr : StronglyMeasurable r) (hr4 : MemLp r 4 μ)
      (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => r (t,x)) 2 volume ≤ ENNReal.ofReal M) :
      P (∫ z, fderiv ℝ ψ z v • (v12_actualCoulombA r k z • r z) ∂μ) =
        ∫ z, (v12_actualCoulombA r k z * r z j) * fderiv ℝ ψ z v ∂μ := by
    have hi : Integrable (fun z => fderiv ℝ ψ z v • (v12_actualCoulombA r k z • r z)) μ :=
      ((hDrift a b r hr hr4 (ENNReal.ofReal M) (by finiteness) hE k).1.locallyIntegrable
        (by norm_num)).integrable_smul_left_of_hasCompactSupport hdψ.continuous hcd
    rw [← P.integral_comp_comm hi]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    change fderiv ℝ ψ z v * (v12_actualCoulombA r k z * r z j) =
      (v12_actualCoulombA r k z * r z j) * fderiv ℝ ψ z v
    ring
  change Tendsto (fun n => P (∫ z, fderiv ℝ ψ z v •
    (v12_actualCoulombA (qn n) k z • qn n z) ∂μ)) atTop
      (𝓝 (P (∫ z, fderiv ℝ ψ z v • (v12_actualCoulombA q k z • q z) ∂μ))) at h
  have hen (n : ℕ) := he (qn n) (hmn n) (hn4 n) (hEn n)
  have heq := he q hmq hq4 hEq
  simpa only [hen, heq] using h

#print axioms v12_actual_scalar_drift_derivative_limit
end SMScattering.W20Full
