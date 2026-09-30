import lean.v12.V12_YRTensorWeakClosure
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Concrete compact continuous tests for raw local Lp limits. Smooth test
functions and their derivatives will be instantiated through these lemmas. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem v12_raw_local_L1_compact_test_limit
    (a b : ℝ) (fn : ℕ → V12Spacetime → E) (f : V12Spacetime → E)
    (hn : ∀ R n, MemLp (fn n) 1 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hf : ∀ R, MemLp f 1 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => fn n z-f z) 1
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (g : V12Spacetime → ℂ) (hgc : HasCompactSupport g) (hgt : Continuous g) :
    Tendsto (fun n => ∫ z, g z • fn n z ∂v12_slab_measure a b) atTop
      (𝓝 (∫ z, g z • f z ∂v12_slab_measure a b)) := by
  obtain ⟨R, hR⟩ := v12_compact_test_in_cylinder g hgc
  let μ := (v12_slab_measure a b).restrict (v12_spatial_cylinder R)
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgt
  have hg : MemLp g ∞ μ := MemLp.of_bound hgt.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
  let G := hg.toLp g
  let Fn := fun n => (hn R n).toLp (fn n)
  let F := (hf R).toLp f
  have hF : Tendsto Fn atTop (𝓝 F) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have he (n : ℕ) : dist (Fn n) F = (eLpNorm (fun z => fn n z-f z) 1 μ).toReal := by
      rw [Lp.dist_def]
      congr 1
      exact eLpNorm_congr_ae ((hn R n).coeFn_toLp.sub (hf R).coeFn_toLp)
    simpa only [he] using hlim R
  let B := (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).lpPairing μ ∞ 1
  have h := ((B G).continuous.tendsto F).comp hF
  have he (r : V12Spacetime → E) (hr : MemLp r 1 μ) :
      B G (hr.toLp r) = ∫ z, g z • r z ∂v12_slab_measure a b := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    calc
      _ = ∫ z, g z • r z ∂μ := by
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp, hr.coeFn_toLp] with z hgz hrz
        simp only [ContinuousLinearMap.lsmul_apply, G, hgz, hrz]
      _ = _ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        rw [hR z hz, zero_smul]
  change Tendsto (fun n => B G ((hn R n).toLp (fn n))) atTop
    (𝓝 (B G ((hf R).toLp f))) at h
  simpa only [he] using h

#print axioms v12_raw_local_L1_compact_test_limit

theorem v12_raw_local_L2_compact_test_limit
    (a b : ℝ) (fn : ℕ → V12Spacetime → E) (f : V12Spacetime → E)
    (hn : ∀ R n, MemLp (fn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hf : ∀ R, MemLp f 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => fn n z-f z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (g : V12Spacetime → ℂ) (hgc : HasCompactSupport g) (hgt : Continuous g) :
    Tendsto (fun n => ∫ z, g z • fn n z ∂v12_slab_measure a b) atTop
      (𝓝 (∫ z, g z • f z ∂v12_slab_measure a b)) := by
  obtain ⟨R, hR⟩ := v12_compact_test_in_cylinder g hgc
  let μ := (v12_slab_measure a b).restrict (v12_spatial_cylinder R)
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hgt
  have hg : MemLp g 2 μ := MemLp.of_bound hgt.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)
  let G := hg.toLp g
  let Fn := fun n => (hn R n).toLp (fn n)
  let F := (hf R).toLp f
  have hF : Tendsto Fn atTop (𝓝 F) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have he (n : ℕ) : dist (Fn n) F = (eLpNorm (fun z => fn n z-f z) 2 μ).toReal := by
      rw [Lp.dist_def]
      congr 1
      exact eLpNorm_congr_ae ((hn R n).coeFn_toLp.sub (hf R).coeFn_toLp)
    simpa only [he] using hlim R
  let B := (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] E →L[ℂ] E).lpPairing μ 2 2
  have h := ((B G).continuous.tendsto F).comp hF
  have he (r : V12Spacetime → E) (hr : MemLp r 2 μ) :
      B G (hr.toLp r) = ∫ z, g z • r z ∂v12_slab_measure a b := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    calc
      _ = ∫ z, g z • r z ∂μ := by
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp, hr.coeFn_toLp] with z hgz hrz
        simp only [ContinuousLinearMap.lsmul_apply, G, hgz, hrz]
      _ = _ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        rw [hR z hz, zero_smul]
  change Tendsto (fun n => B G ((hn R n).toLp (fn n))) atTop
    (𝓝 (B G ((hf R).toLp f))) at h
  simpa only [he] using h

#print axioms v12_raw_local_L2_compact_test_limit

theorem v12_compact_spacetime_test_derivative
    (ψ : V12Spacetime → ℂ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (v : V12Spacetime) :
    HasCompactSupport (fun z => fderiv ℝ ψ z v) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ ψ z v) :=
  ⟨hc.fderiv_apply ℝ v, (hψ.fderiv_right (by simp)).clm_apply contDiff_const⟩

theorem v12_compact_spacetime_test_derivative_memLp_top
    (μ : Measure V12Spacetime) (ψ : V12Spacetime → ℂ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (v : V12Spacetime) : MemLp (fun z => fderiv ℝ ψ z v) ∞ μ := by
  obtain ⟨hs, hd⟩ := v12_compact_spacetime_test_derivative ψ hψ hc v
  exact hd.continuous.memLp_top_of_hasCompactSupport hs μ

theorem v12_raw_local_L2_derivative_test_limit
    (a b : ℝ) (fn : ℕ → V12Spacetime → E) (f : V12Spacetime → E)
    (hn : ∀ R n, MemLp (fn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hf : ∀ R, MemLp f 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => fn n z-f z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (ψ : V12Spacetime → ℂ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (v : V12Spacetime) :
    Tendsto (fun n => ∫ z, fderiv ℝ ψ z v • fn n z ∂v12_slab_measure a b) atTop
      (𝓝 (∫ z, fderiv ℝ ψ z v • f z ∂v12_slab_measure a b)) := by
  obtain ⟨hs, hd⟩ := v12_compact_spacetime_test_derivative ψ hψ hc v
  exact v12_raw_local_L2_compact_test_limit a b fn f hn hf hlim _ hs hd.continuous

theorem v12_raw_local_L2_second_derivative_test_limit
    (a b : ℝ) (fn : ℕ → V12Spacetime → E) (f : V12Spacetime → E)
    (hn : ∀ R n, MemLp (fn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hf : ∀ R, MemLp f 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => fn n z-f z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (ψ : V12Spacetime → ℂ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (v w : V12Spacetime) :
    Tendsto (fun n => ∫ z, fderiv ℝ (fun y => fderiv ℝ ψ y v) z w • fn n z ∂v12_slab_measure a b)
      atTop (𝓝 (∫ z, fderiv ℝ (fun y => fderiv ℝ ψ y v) z w • f z ∂v12_slab_measure a b)) := by
  obtain ⟨hs, hd⟩ := v12_compact_spacetime_test_derivative ψ hψ hc v
  exact v12_raw_local_L2_derivative_test_limit a b fn f hn hf hlim _ hd hs w

#print axioms v12_compact_spacetime_test_derivative_memLp_top
#print axioms v12_raw_local_L2_derivative_test_limit
#print axioms v12_raw_local_L2_second_derivative_test_limit

end SMScattering.W20Full
