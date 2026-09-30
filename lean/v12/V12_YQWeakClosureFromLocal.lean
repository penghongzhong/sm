import lean.v12.V12_YPCompactTestDensity
import lean.v12.V12_YPDenseTestExtension
import lean.v12.V12_YMeasurableLocalLimitGluing

/-! Global weak L2 closure from actual local L1 convergence. Compact tests
are constructed and their density proved; no weak-limit premise is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_compact_test_in_cylinder
    (g : V12Spacetime → ℂ) (hg : HasCompactSupport g) :
    ∃ R : ℕ, ∀ z, z ∉ v12_spatial_cylinder R → g z = 0 := by
  obtain ⟨C, hC⟩ := hg.exists_bound_of_continuousOn continuous_snd.continuousOn
  obtain ⟨R, hR⟩ := exists_nat_gt C
  refine ⟨R, ?_⟩
  intro z hz
  by_contra hgz
  have hs : z ∈ tsupport g := subset_closure (Function.mem_support.mpr hgz)
  have hc := hC z hs
  have hmem : z ∈ v12_spatial_cylinder R := by
    change ‖z.2‖ < (R : ℝ) + 1
    linarith
  exact hz hmem

theorem v12_local_L1_compact_test_limit
    (a b : ℝ) (fn : ℕ → V12Spacetime → ℂ) (f : V12Spacetime → ℂ)
    (Fn : ∀ R : ℕ, ℕ → Lp ℂ 1 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (F : ∀ R : ℕ, Lp ℂ 1 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hn : ∀ R n, (Fn R n : V12Spacetime → ℂ) =ᵐ[(v12_slab_measure a b).restrict
      (v12_spatial_cylinder R)] fn n)
    (hf : ∀ R, (F R : V12Spacetime → ℂ) =ᵐ[(v12_slab_measure a b).restrict
      (v12_spatial_cylinder R)] f)
    (hlim : ∀ R, Tendsto (Fn R) atTop (𝓝 (F R)))
    (g : V12Spacetime → ℂ) (hgc : HasCompactSupport g) (hgt : Continuous g) :
    Tendsto (fun n => ∫ z, fn n z * g z ∂v12_slab_measure a b) atTop
      (𝓝 (∫ z, f z * g z ∂v12_slab_measure a b)) := by
  obtain ⟨R, hR⟩ := v12_compact_test_in_cylinder g hgc
  let μ := (v12_slab_measure a b).restrict (v12_spatial_cylinder R)
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgt
  have hg : MemLp g ∞ μ := memLp_top_of_bound hgt.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
  let G := hg.toLp g
  let B := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ ∞ 1 G
  have h := (B.continuous.tendsto (F R)).comp (hlim R)
  have he (q : Lp ℂ 1 μ) (r : V12Spacetime → ℂ) (hr : (q : V12Spacetime → ℂ) =ᵐ[μ] r) :
      B q = ∫ z, r z * g z ∂v12_slab_measure a b := by
    change (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ ∞ 1 G q = _
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    calc
      (∫ z, (ContinuousLinearMap.mul ℂ ℂ) (G z) (q z) ∂μ) =
          ∫ z, r z * g z ∂μ := by
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp, hr] with z hz hq
        simp only [ContinuousLinearMap.mul_apply', G, hz, hq, mul_comm]
      _ = ∫ z, r z * g z ∂v12_slab_measure a b := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        rw [hR z hz, mul_zero]
  simpa only [Function.comp_def, he _ _ (hn R _), he _ _ (hf R)] using h

/-- Uniform L2 bounds and local L1 convergence imply actual integral weak
convergence against every global L2 test, including noncompact tests. -/
theorem v12_global_weak_L2_of_local_L1
    (a b : ℝ) (Vn : ℕ → Lp ℂ 2 (v12_slab_measure a b))
    (V : Lp ℂ 2 (v12_slab_measure a b))
    (C : ℝ) (hC : ∀ n, ‖Vn n‖ ≤ C)
    (Fn : ∀ R : ℕ, ℕ → Lp ℂ 1 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (F : ∀ R : ℕ, Lp ℂ 1 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hn : ∀ R n, (Fn R n : V12Spacetime → ℂ) =ᵐ[(v12_slab_measure a b).restrict
      (v12_spatial_cylinder R)] (Vn n : V12Spacetime → ℂ))
    (hf : ∀ R, (F R : V12Spacetime → ℂ) =ᵐ[(v12_slab_measure a b).restrict
      (v12_spatial_cylinder R)] (V : V12Spacetime → ℂ))
    (hlim : ∀ R, Tendsto (Fn R) atTop (𝓝 (F R))) :
    ∀ φ : Lp ℂ 2 (v12_slab_measure a b),
      Tendsto (fun n => ∫ z, Vn n z * φ z ∂v12_slab_measure a b) atTop
        (𝓝 (∫ z, V z * φ z ∂v12_slab_measure a b)) := by
  let B := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (v12_slab_measure a b) 2 2
  have hb : ∀ n, ‖B (Vn n)‖ ≤ ‖B‖ * C := by
    intro n
    exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg B))
  have hc : ∀ φ ∈ v12_compactContinuousTests (v12_slab_measure a b),
      Tendsto (fun n => B (Vn n) φ) atTop (𝓝 (B V φ)) := by
    rintro φ ⟨g, hgc, hgt, hg, rfl⟩
    have h := v12_local_L1_compact_test_limit a b (fun n => Vn n) V Fn F hn hf hlim g hgc hgt
    have he (q : Lp ℂ 2 (v12_slab_measure a b)) :
        B q (hg.toLp g) = ∫ z, q z * g z ∂v12_slab_measure a b := by
      rw [ContinuousLinearMap.lpPairing_eq_integral]
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with z hz
      simp only [ContinuousLinearMap.mul_apply', hz]
    simpa only [he] using h
  have h := v12_dense_test_extension (fun n => B (Vn n)) (B V) (‖B‖ * C) hb
    _ (v12_slab_compactContinuousTests_dense a b) hc
  intro φ
  simpa only [B, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply'] using h φ

#print axioms v12_compact_test_in_cylinder
#print axioms v12_local_L1_compact_test_limit
#print axioms v12_global_weak_L2_of_local_L1
end SMScattering.W20Full
