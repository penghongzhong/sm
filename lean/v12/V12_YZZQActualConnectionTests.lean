import lean.v12.V12_YPInheritedEnergy
import lean.v12.V12_YZZCCompactDistributionTests
import lean.v12.V12_YZZActualDriftStrong

/-! Differentiated compact tests of the same raw Hodge connection. The
scalar component convergence and all local memberships are proved from
Q convergence, inherited energy and the actual MZ application. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_connection_compact_derivative_limit
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
    Tendsto (fun n => ∫ z, v12_actualCoulombA (qn n) j z * fderiv ℝ ψ z v
      ∂v12_slab_measure a b) atTop
      (𝓝 (∫ z, v12_actualCoulombA q j z * fderiv ℝ ψ z v ∂v12_slab_measure a b)) := by
  let μ := v12_slab_measure a b
  have hq4 : MemLp q 4 μ :=
    (v12_global_budget_inherited_from_local_L2 a b qn q hmq hn2 hq2 hlim 4 Z hb).trans_lt
      (lt_top_iff_ne_top.mpr hZ)
  have hEq := v12_global_energy_inherited a b qn q hmq hn2 hq2 hlim
    (ENNReal.ofReal M) (by finiteness) hEn
  obtain ⟨C, hC, hMZ⟩ := v12_actual_hodge_spacetime_MZ hHLS
  have hA2 (r : V12Spacetime → V12Field) (hr : StronglyMeasurable r) (hr4 : MemLp r 4 μ)
      (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => r (t,x)) 2 volume ≤ ENNReal.ofReal M) (R : ℕ) :
      MemLp (v12_actualCoulombA r j) 2 (μ.restrict (v12_spatial_cylinder R)) := by
    have h4 := (hMZ a b r hr hr4 (ENNReal.ofReal M) (by finiteness) hE).1
    have hj4 : MemLp (v12_actualCoulombA r j) 4 μ :=
      (v12_actualCoulombA_eLpNorm_le μ r hr 4 j).trans_lt h4
    exact (hj4.restrict (v12_spatial_cylinder R)).mono_exponent (by norm_num)
  have ht (R : ℕ) : Tendsto (fun n => (eLpNorm
      (fun z => v12_actualCoulombA (qn n) j z-v12_actualCoulombA q j z) 2
      (μ.restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
    obtain ⟨hD, hL⟩ := v12_actual_Hodge_local_L2_limit hHLS a b R qn q hmn hmq
      hn4 hq4 hn2 hq2 hlim M hM hEn hEq Z hZ hb
    apply squeeze_zero (fun n => ENNReal.toReal_nonneg) _ hL
    intro n
    apply ENNReal.toReal_mono (hD n).eLpNorm_ne_top
    apply eLpNorm_mono_ae
    · exact ((hA2 (qn n) (hmn n) (hn4 n) (hEn n) R).sub (hA2 q hmq hq4 hEq R)).aestronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro z
      simpa only [v12_actualCoulombA, ← Complex.ofReal_sub, Complex.norm_real,
        PiLp.sub_apply] using PiLp.norm_apply_le
          (v12_spacetimeHodge (qn n) z-v12_spacetimeHodge q z) j
  have h := v12_raw_local_L2_derivative_test_limit a b
    (fun n => v12_actualCoulombA (qn n) j) (v12_actualCoulombA q j)
    (fun R n => hA2 (qn n) (hmn n) (hn4 n) (hEn n) R)
    (fun R => hA2 q hmq hq4 hEq R) ht ψ hψ hc v
  simpa only [smul_eq_mul, mul_comm] using h

#print axioms v12_actual_connection_compact_derivative_limit
end SMScattering.W20Full
