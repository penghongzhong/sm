import lean.v12.V12_FrequencyTightnessLimit

/-!
Global representative identity for arbitrary spatial L2 input. The previously
verified equality on every ball is exhausted over countably many balls.
This is the actual Fourier cutoff, not a replacement operator with only a
similar norm bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SMScattering.W20Full

open MeasureTheory
open scoped ENNReal

theorem v12_cutoffN_ae_continuousRep
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (N : ℕ) (f : V12SpatialL2) :
    (v12_cutoffN p hpc hps N f : V12Spatial → V12Field) =ᵐ[volume]
      v12_L2ConvolutionRep (v12_cutoffKernelL2 p hpc hps N) f := by
  let P := v12_cutoffN p hpc hps N f
  let F := v12_L2ConvolutionBCFCLM (v12_cutoffKernelL2 p hpc hps N) f
  have hball : ∀ R, (P : V12Spatial → V12Field)
      =ᵐ[(volume : Measure V12Spatial).restrict (v12_spatial_ball R)] F := by
    intro R
    have hc : v12_ballRestrictCLM R P = v12_ballBCFToLpCLM R F :=
      v12_cutoffNBall_eq_convolutionBall p hpc hps N R f
    have hleft : (v12_ballRestrictCLM R P : V12Spatial → V12Field)
        =ᵐ[(volume : Measure V12Spatial).restrict (v12_spatial_ball R)] P :=
      LpToLpRestrictCLM_coeFn ℂ (v12_spatial_ball R) P
    have hright : (v12_ballBCFToLpCLM R F : V12Spatial → V12Field)
        =ᵐ[(volume : Measure V12Spatial).restrict (v12_spatial_ball R)] F :=
      BoundedContinuousFunction.coeFn_toLp 2
        ((volume : Measure V12Spatial).restrict (v12_spatial_ball R)) ℂ F
    rw [hc] at hleft
    exact hleft.symm.trans hright
  have hcover : (⋃ R : ℕ, v12_spatial_ball R) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨R, hR⟩ := exists_nat_gt ‖x‖
    refine ⟨R, ?_⟩
    simpa only [v12_spatial_ball, Metric.mem_ball, dist_zero_right] using
      hR.trans (lt_add_one (R : ℝ))
  have h := (ae_eq_restrict_iUnion_iff (fun R => v12_spatial_ball R)
    (P : V12Spatial → V12Field) (F : V12Spatial → V12Field)).mpr hball
  rw [hcover, Measure.restrict_univ] at h
  exact h

/-- The continuous cutoff representative has the actual Fourier L2 class. -/
theorem v12_cutoff_rep_memLp_and_class
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (N : ℕ) (f : V12SpatialL2) :
    ∃ h : MemLp (v12_L2ConvolutionRep (v12_cutoffKernelL2 p hpc hps N) f)
        2 (volume : Measure V12Spatial),
      h.toLp (v12_L2ConvolutionRep (v12_cutoffKernelL2 p hpc hps N) f) =
        v12_cutoffN p hpc hps N f := by
  have heq := v12_cutoffN_ae_continuousRep p hpc hps N f
  have hLp := MemLp.ae_eq heq (Lp.memLp (v12_cutoffN p hpc hps N f))
  refine ⟨hLp, ?_⟩
  apply Lp.ext_iff.mpr
  exact hLp.coeFn_toLp.trans heq.symm

#print axioms v12_cutoffN_ae_continuousRep
#print axioms v12_cutoff_rep_memLp_and_class

end SMScattering.W20Full
