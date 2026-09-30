import lean.v12.V12_YPInheritedEnergy
import lean.v12.V12_YZZFActualVQTest

/-! Both actual reconstructed zero-order products tested against compact
functions. Limit L4 and energy assumptions are discharged by inheritance. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_compact_times_local_memLp_two
    (a b : ℝ) (f ψ : V12Spacetime → ℂ)
    (hf : ∀ R, MemLp f 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hc : HasCompactSupport ψ) (hψ : Continuous ψ) :
    MemLp (fun z => ψ z * f z) 2 (v12_slab_measure a b) := by
  let μ := v12_slab_measure a b
  obtain ⟨R, hR⟩ := v12_compact_test_in_cylinder ψ hc
  let s := v12_spatial_cylinder R
  have hI : MemLp (s.indicator f) 2 μ :=
    (memLp_indicator_iff_restrict (v12_spatial_cylinder_measurable R).nullMeasurableSet).2 (hf R)
  have hp : MemLp ψ ∞ μ := hψ.memLp_top_of_hasCompactSupport hc μ
  have hh : MemLp (fun z => ψ z * s.indicator f z) 2 μ := hp.mul hI
  have he : (fun z => ψ z * s.indicator f z) = (fun z => ψ z * f z) := by
    funext z
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz]
    · rw [hR z hz, zero_mul, zero_mul]
  rw [he] at hh
  exact hh

theorem v12_actual_zero_order_compact_limits
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
    (j : Fin 2) (ψ : V12Spacetime → ℂ) (hc : HasCompactSupport ψ) (hψ : Continuous ψ) :
    ∃ (hq4 : MemLp q 4 (v12_slab_measure a b))
      (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M),
      Tendsto (fun n => ∫ z,
        (v12_actualPotentialL2Class hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n) z *
          (ψ z * qn n z j) + v12_WDensity (qn n z) * (ψ z * star (qn n z j)))
        ∂v12_slab_measure a b) atTop
      (𝓝 (∫ z,
        (v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq z * (ψ z * q z j) +
          v12_WDensity (q z) * (ψ z * star (q z j))) ∂v12_slab_measure a b)) := by
  let μ := v12_slab_measure a b
  have hq4 : MemLp q 4 μ :=
    (v12_global_budget_inherited_from_local_L2 a b qn q hmq hn2 hq2 hlim 4 Z hb).trans_lt
      (lt_top_iff_ne_top.mpr hZ)
  have hEq := v12_global_energy_inherited a b qn q hmq hn2 hq2 hlim
    (ENNReal.ofReal M) (by finiteness) hEn
  refine ⟨hq4, hEq, ?_⟩
  have hv := v12_actual_VQ_compact_test_limit hHLS a b qn q hmn hmq hn4 hq4 hn2 hq2
    hlim M hM hEn hEq Z hZ hb j ψ hc hψ
  have hw := v12_actual_WQ_compact_test_limit a b qn q hn4 hq4 hn2 hq2 hlim Z hZ hb j ψ hc hψ
  have hcomponent (r : V12Spacetime → V12Field)
      (hr : ∀ R, MemLp r 2 (μ.restrict (v12_spatial_cylinder R))) :
      ∀ R, MemLp (fun z => r z j) 2 (μ.restrict (v12_spatial_cylinder R)) := fun R =>
    (v12_raw_component_eLpNorm_le _ 2 r (hr R).aestronglyMeasurable j).trans_lt (hr R)
  have hint (r : V12Spacetime → V12Field) (hr4 : MemLp r 4 μ)
      (hr2 : ∀ R, MemLp r 2 (μ.restrict (v12_spatial_cylinder R))) (V : Lp ℂ 2 μ) :
      Integrable (fun z => V z * (ψ z * r z j)) μ ∧
      Integrable (fun z => v12_WDensity (r z) * (ψ z * star (r z j))) μ := by
    have hf := v12_compact_times_local_memLp_two a b _ ψ (hcomponent r hr2) hc hψ
    have hs := v12_compact_times_local_memLp_two a b _ ψ
      (fun R => (hcomponent r hr2 R).star) hc hψ
    exact ⟨memLp_one_iff_integrable.mp ((Lp.memLp V).mul hf),
      memLp_one_iff_integrable.mp ((v12_actual_W_mass_L2_budgets μ r hr4).1.mul hs)⟩
  have he := hv.add hw
  have hnInt (n : ℕ) := hint (qn n) (hn4 n) (fun R => hn2 R n)
    (v12_actualPotentialL2Class hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n))
  have hqInt := hint q hq4 hq2 (v12_actualPotentialL2Class hHLS a b q hmq hq4 M hEq)
  have heN (n : ℕ) := integral_add (hnInt n).1 (hnInt n).2
  have heQ := integral_add hqInt.1 hqInt.2
  simpa only [heN, heQ] using he

#print axioms v12_compact_times_local_memLp_two
#print axioms v12_actual_zero_order_compact_limits
end SMScattering.W20Full
