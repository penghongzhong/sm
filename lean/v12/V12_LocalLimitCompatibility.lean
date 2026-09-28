import Mathlib
import «V12_FrequencyTightnessLimit»

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_spatial_cylinder_mono {R S : ℕ} (hRS : R ≤ S) :
    v12_spatial_cylinder R ⊆ v12_spatial_cylinder S := by
  intro z hz
  simp only [v12_spatial_cylinder, Set.mem_setOf_eq] at hz ⊢
  have hnat : (R : ℝ) ≤ (S : ℝ) := by exact_mod_cast hRS
  linarith

theorem v12_spatial_cylinder_measurable (R : ℕ) :
    MeasurableSet (v12_spatial_cylinder R) := by
  have hopen : IsOpen (v12_spatial_cylinder R) := by
    rw [v12_spatial_cylinder]
    exact isOpen_lt continuous_norm (continuous_const.add continuous_const)
  exact hopen.measurableSet

theorem v12_nested_measure_eq
    (a b : ℝ) {R S : ℕ} (hRS : R ≤ S) :
    ((v12_slab_measure a b).restrict (v12_spatial_cylinder S)).restrict
        (v12_spatial_cylinder R)
      =
    (v12_slab_measure a b).restrict (v12_spatial_cylinder R) := by
  exact Measure.restrict_restrict_of_subset (v12_spatial_cylinder_mono hRS)

noncomputable def v12_localize_nested
    (a b : ℝ) {R S : ℕ} (hRS : R ≤ S) :
    V12CylinderL2 a b S →L[ℂ] V12CylinderL2 a b R := by
  let T :=
    LpToLpRestrictCLM V12Spacetime V12Field ℂ
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder S)) 2
      (v12_spatial_cylinder R)
  rw [v12_nested_measure_eq a b hRS] at T
  exact T

theorem v12_localize_nested_coeFn
    (a b : ℝ) {R S : ℕ} (hRS : R ≤ S)
    (f : V12CylinderL2 a b S) :
    (v12_localize_nested a b hRS f : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] f := by
  unfold v12_localize_nested
  simp only
  exact LpToLpRestrictCLM_coeFn ℂ (v12_spatial_cylinder R) f

theorem v12_nested_direct_ae
    (a b : ℝ) {R S : ℕ} (hRS : R ≤ S)
    (f : V12SlabL2 a b) :
    (v12_localize_nested a b hRS (v12_localize a b S f) :
        V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)]
    (v12_localize a b R f) := by
  have h1 := v12_localize_nested_coeFn a b hRS (v12_localize a b S f)
  have h2 := v12_localize_coeFn a b S f
  have h3 := v12_localize_coeFn a b R f
  filter_upwards [h1, h3,
    (ae_mono
      (show
        (v12_slab_measure a b).restrict (v12_spatial_cylinder R)
          ≤
        (v12_slab_measure a b).restrict (v12_spatial_cylinder S) by
          exact Measure.restrict_mono' (v12_spatial_cylinder_mono hRS))
      h2)] with z hz1 hz3 hz2
  rw [hz1, hz2, hz3]

theorem v12_nested_direct
    (a b : ℝ) {R S : ℕ} (hRS : R ≤ S)
    (f : V12SlabL2 a b) :
    v12_localize_nested a b hRS (v12_localize a b S f)
      =
    v12_localize a b R f := by
  apply Lp.ext
  exact v12_nested_direct_ae a b hRS f

theorem v12_common_subsequence_local_compatibility
    (a b : ℝ) (Q : ℕ → V12SlabL2 a b)
    (σ : ℕ → ℕ)
    (q : ∀ R, V12CylinderL2 a b R)
    (hconv : ∀ R,
      Tendsto (fun n => v12_localize a b R (Q (σ n)))
        atTop (𝓝 (q R))) :
    ∀ {R S : ℕ} (hRS : R ≤ S),
      v12_localize_nested a b hRS (q S) = q R := by
  intro R S hRS
  have hmap :
      Tendsto
        (fun n =>
          v12_localize_nested a b hRS
            (v12_localize a b S (Q (σ n))))
        atTop
        (𝓝 (v12_localize_nested a b hRS (q S))) :=
    (v12_localize_nested a b hRS).continuous.tendsto (q S) |>.comp (hconv S)
  have hsame :
      (fun n =>
          v12_localize_nested a b hRS
            (v12_localize a b S (Q (σ n))))
        =
      (fun n => v12_localize a b R (Q (σ n))) := by
    funext n
    exact v12_nested_direct a b hRS (Q (σ n))
  rw [hsame] at hmap
  exact tendsto_nhds_unique hmap (hconv R)

#print axioms v12_spatial_cylinder_mono
#print axioms v12_spatial_cylinder_measurable
#print axioms v12_nested_measure_eq
#print axioms v12_localize_nested_coeFn
#print axioms v12_nested_direct
#print axioms v12_common_subsequence_local_compatibility

end SMScattering.W20Full
