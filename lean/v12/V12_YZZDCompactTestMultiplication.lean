import lean.v12.V12_YWeakStrongProducts
import lean.v12.V12_YZZCCompactDistributionTests

/-! A compact test turns a raw local strong L2 sequence into an actual
strong global L2 test sequence. Used for weak-strong zero-order PDE terms. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_local_L2_compact_multiplier
    (a b : ℝ) (fn : ℕ → V12Spacetime → ℂ) (f : V12Spacetime → ℂ)
    (hn : ∀ R n, MemLp (fn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hf : ∀ R, MemLp f 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => fn n z-f z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (ψ : V12Spacetime → ℂ) (hc : HasCompactSupport ψ) (hψ : Continuous ψ) :
    ∃ (Fn : ℕ → Lp ℂ 2 (v12_slab_measure a b)) (F : Lp ℂ 2 (v12_slab_measure a b)),
      (∀ n, (Fn n : V12Spacetime → ℂ) =ᵐ[v12_slab_measure a b] fun z => ψ z * fn n z) ∧
      ((F : V12Spacetime → ℂ) =ᵐ[v12_slab_measure a b] fun z => ψ z * f z) ∧
      Tendsto Fn atTop (𝓝 F) := by
  let μ := v12_slab_measure a b
  obtain ⟨R, hR⟩ := v12_compact_test_in_cylinder ψ hc
  let s := v12_spatial_cylinder R
  have hs : MeasurableSet s := v12_spatial_cylinder_measurable R
  have hnI : ∀ n, MemLp (s.indicator (fn n)) 2 μ := fun n =>
    (memLp_indicator_iff_restrict hs.nullMeasurableSet).2 (hn R n)
  have hfI : MemLp (s.indicator f) 2 μ :=
    (memLp_indicator_iff_restrict hs.nullMeasurableSet).2 (hf R)
  have hIlim : Tendsto (fun n => (eLpNorm
      (fun z => s.indicator (fn n) z-s.indicator f z) 2 μ).toReal) atTop (𝓝 0) := by
    have he (n : ℕ) : (fun z => s.indicator (fn n) z-s.indicator f z) =
        s.indicator (fun z => fn n z-f z) := by
      funext z
      by_cases hz : z ∈ s <;> simp [Set.indicator_apply, hz]
    simp only [he, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
    exact hlim R
  have hI := v12_raw_L2_toLp_tendsto μ (fun n => s.indicator (fn n)) (s.indicator f) hnI hfI hIlim
  have hp : MemLp ψ ∞ μ := hψ.memLp_top_of_hasCompactSupport hc μ
  let P := hp.toLp ψ
  let B := (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 P
  let Fn := fun n => B ((hnI n).toLp (s.indicator (fn n)))
  let F := B (hfI.toLp (s.indicator f))
  have hr (r : V12Spacetime → ℂ) (hr : MemLp (s.indicator r) 2 μ) :
      (B (hr.toLp (s.indicator r)) : V12Spacetime → ℂ) =ᵐ[μ] fun z => ψ z * r z := by
    have hh := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) P (hr.toLp (s.indicator r))
    filter_upwards [hh, hp.coeFn_toLp, hr.coeFn_toLp] with z hz hpz hrz
    change B (hr.toLp (s.indicator r)) z = P z * (hr.toLp (s.indicator r)) z at hz
    rw [hz, hpz, hrz]
    by_cases hzs : z ∈ s
    · rw [Set.indicator_of_mem hzs]
    · rw [hR z hzs, zero_mul, zero_mul]
  exact ⟨Fn, F, fun n => hr (fn n) (hnI n), hr f hfI, (B.continuous.tendsto _).comp hI⟩

theorem v12_weak_L2_local_strong_L2_compact_integral_limit
    (a b : ℝ) (Vn : ℕ → Lp ℂ 2 (v12_slab_measure a b)) (V : Lp ℂ 2 (v12_slab_measure a b))
    (C : ℝ) (hC : ∀ n, ‖Vn n‖ ≤ C)
    (hweak : ∀ φ : Lp ℂ 2 (v12_slab_measure a b),
      Tendsto (fun n => ∫ z, Vn n z * φ z ∂v12_slab_measure a b) atTop
        (𝓝 (∫ z, V z * φ z ∂v12_slab_measure a b)))
    (fn : ℕ → V12Spacetime → ℂ) (f : V12Spacetime → ℂ)
    (hn : ∀ R n, MemLp (fn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hf : ∀ R, MemLp f 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => fn n z-f z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (ψ : V12Spacetime → ℂ) (hc : HasCompactSupport ψ) (hψ : Continuous ψ) :
    Tendsto (fun n => ∫ z, Vn n z * (ψ z * fn n z) ∂v12_slab_measure a b) atTop
      (𝓝 (∫ z, V z * (ψ z * f z) ∂v12_slab_measure a b)) := by
  obtain ⟨Fn, F, hnrep, hfrep, hF⟩ := v12_local_L2_compact_multiplier a b fn f hn hf hlim ψ hc hψ
  have h := v12_weak_L2_strong_L2_integral_limit (v12_slab_measure a b) Vn V Fn F C hC hweak hF
  have he (v t : Lp ℂ 2 (v12_slab_measure a b)) (r : V12Spacetime → ℂ)
      (hr : (t : V12Spacetime → ℂ) =ᵐ[v12_slab_measure a b] fun z => ψ z*r z) :
      (∫ z, v z * t z ∂v12_slab_measure a b) = ∫ z, v z*(ψ z*r z) ∂v12_slab_measure a b := by
    apply integral_congr_ae
    filter_upwards [hr] with z hz
    rw [hz]
  simpa only [he _ _ _ (hnrep _), he _ _ _ hfrep] using h

#print axioms v12_local_L2_compact_multiplier
#print axioms v12_weak_L2_local_strong_L2_compact_integral_limit
end SMScattering.W20Full
