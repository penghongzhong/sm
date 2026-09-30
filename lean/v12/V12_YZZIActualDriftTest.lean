import lean.v12.V12_YPInheritedEnergy
import lean.v12.V12_YZZActualDriftStrong
import lean.v12.V12_YZZCCompactDistributionTests

/-! Concrete differentiated compact tests for the SAME Hodge drift.
Limit-field L4 and energy bounds are inherited from the original sequence;
no coefficient convergence or limit-field budget is an assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_drift_compact_derivative_limit
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
    (j : Fin 2) (ψ : V12Spacetime → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (v : V12Spacetime) :
    Tendsto (fun n => ∫ z, fderiv ℝ ψ z v •
      (v12_actualCoulombA (qn n) j z • qn n z) ∂v12_slab_measure a b) atTop
      (𝓝 (∫ z, fderiv ℝ ψ z v • (v12_actualCoulombA q j z • q z)
        ∂v12_slab_measure a b)) := by
  have hq4 : MemLp q 4 (v12_slab_measure a b) :=
    (v12_global_budget_inherited_from_local_L2 a b qn q hmq hn2 hq2 hlim 4 Z hb).trans_lt
      (lt_top_iff_ne_top.mpr hZ)
  have hEq := v12_global_energy_inherited a b qn q hmq hn2 hq2 hlim
    (ENNReal.ofReal M) (by finiteness) hEn
  obtain ⟨C, hC, hDrift⟩ := v12_actualCoulomb_drift_MZZ hHLS
  have hmem (r : V12Spacetime → V12Field) (hr : StronglyMeasurable r)
      (hr4 : MemLp r 4 (v12_slab_measure a b))
      (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => r (t,x)) 2 volume ≤ ENNReal.ofReal M) (R : ℕ) :
      MemLp (fun z => v12_actualCoulombA r j z • r z) 1
        ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)) :=
    ((hDrift a b r hr hr4 (ENNReal.ofReal M) (by finiteness) hE j).1.restrict
      (v12_spatial_cylinder R)).mono_exponent (by norm_num)
  obtain ⟨hcd, hdψ⟩ := v12_compact_spacetime_test_derivative ψ hψ hc v
  exact v12_raw_local_L1_compact_test_limit a b
    (fun n z => v12_actualCoulombA (qn n) j z • qn n z)
    (fun z => v12_actualCoulombA q j z • q z)
    (fun R n => hmem (qn n) (hmn n) (hn4 n) (hEn n) R)
    (fun R => hmem q hmq hq4 hEq R)
    (fun R => v12_actual_Coulomb_drift_local_L1_limit hHLS a b R j qn q hmn hmq
      hn4 hq4 hn2 hq2 hlim M hM hEn hEq Z hZ hb) _ hcd hdψ.continuous

#print axioms v12_actual_drift_compact_derivative_limit
end SMScattering.W20Full
