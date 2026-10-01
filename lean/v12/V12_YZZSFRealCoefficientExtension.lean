import lean.v12.V12_YZZSDRealCoefficientConvergence
import lean.v12.V12_YWSmoothSlabExtension

/-! Transport all real-radius coefficient conclusions from the concrete
zero extensions back to the same original fields, including finite AQ norms. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_real_coefficient_convergence_of_extension
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (h : V12SameFieldRealCoefficientConvergence a b
      (fun n => v12_smoothSlabExtension a b (qn n)) q) :
    V12SameFieldRealCoefficientConvergence a b qn q := by
  intro r
  let ν := (v12_slab_measure a b).restrict (v12_real_spatial_cylinder r)
  let ext := fun n => v12_smoothSlabExtension a b (qn n)
  have he (n : ℕ) : ext n =ᵐ[ν] qn n :=
    (v12_smoothSlabExtension_ae a b (qn n)).restrict
  have hH (n : ℕ) : v12_spacetimeHodge (ext n) =ᵐ[ν] v12_spacetimeHodge (qn n) :=
    (v12_smoothSlabExtension_Hodge_ae a b (qn n)).restrict
  have hBae (n : ℕ) :
      (fun z => v12_curvatureDensity (ext n z)-v12_curvatureDensity (q z)) =ᵐ[ν]
      (fun z => v12_curvatureDensity (qn n z)-v12_curvatureDensity (q z)) := by
    filter_upwards [he n] with z hz
    rw [hz]
  have hBint (n : ℕ) : (∫ z, ‖v12_curvatureDensity (ext n z)-v12_curvatureDensity (q z)‖ ∂ν) =
      ∫ z, ‖v12_curvatureDensity (qn n z)-v12_curvatureDensity (q z)‖ ∂ν :=
    integral_congr_ae ((hBae n).fun_comp norm)
  have hAae (n : ℕ) : (fun z => v12_spacetimeHodge (ext n) z-v12_spacetimeHodge q z) =ᵐ[ν]
      (fun z => v12_spacetimeHodge (qn n) z-v12_spacetimeHodge q z) := by
    filter_upwards [hH n] with z hz
    rw [hz]
  have hAnorm (n : ℕ) := eLpNorm_congr_ae (hAae n) (p := (2 : ℝ≥0∞))
  have hDae (n : ℕ) (j : Fin 2) :
      (fun z => v12_actualCoulombA (ext n) j z • ext n z-v12_actualCoulombA q j z • q z) =ᵐ[ν]
      (fun z => v12_actualCoulombA (qn n) j z • qn n z-v12_actualCoulombA q j z • q z) := by
    filter_upwards [he n, hH n] with z hqz haz
    simp only [v12_actualCoulombA, hqz, haz]
  have hDnorm (n : ℕ) (j : Fin 2) := eLpNorm_congr_ae (hDae n j) (p := (1 : ℝ≥0∞))
  dsimp only [ext, ν] at hBint hAnorm hDnorm
  refine ⟨fun n => ((h r).1 n).congr (hBae n), ?_,
    (fun n => ((h r).2.2.1 n).ae_eq (hAae n)), ?_, ?_⟩
  · simpa only [hBint] using (h r).2.1
  · simpa only [hAnorm] using (h r).2.2.2.1
  · intro j
    refine ⟨fun n => (((h r).2.2.2.2 j).1 n).ae_eq (hDae n j), ?_⟩
    simpa only [hDnorm] using ((h r).2.2.2.2 j).2

#print axioms v12_real_coefficient_convergence_of_extension
end SMScattering.W20Full
