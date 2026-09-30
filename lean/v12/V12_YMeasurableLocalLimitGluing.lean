import lean.v12.V12_YLocalLimitCompatibility

/-!
A single measurable raw field is constructed from the local L2 limits of
one global sequence. The least containing cylinder selects a representative;
countably many a.e. compatibility equalities prove that this selection agrees
with every local class. No measurable-gluing or compatibility input is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_spatial_cylinder_measurable (R : ℕ) :
    MeasurableSet (v12_spatial_cylinder R) := by
  change MeasurableSet {z : V12Spacetime | ‖z.2‖ < (R : ℝ) + 1}
  exact measurableSet_lt measurable_snd.norm measurable_const

theorem v12_spatial_cylinder_exhausts (z : V12Spacetime) :
    ∃ R : ℕ, z ∈ v12_spatial_cylinder R := by
  obtain ⟨R, hR⟩ := exists_nat_gt ‖z.2‖
  exact ⟨R, hR.trans (lt_add_one _)⟩

theorem v12_spatial_cylinder_iUnion :
    (⋃ R : ℕ, v12_spatial_cylinder R) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact v12_spatial_cylinder_exhausts z

noncomputable def v12_glue_local_representatives (a b : ℝ)
    (q : ∀ R, V12CylinderL2 a b R) (z : V12Spacetime) : V12Field :=
  by
  classical
  exact q (Nat.find (v12_spatial_cylinder_exhausts z)) z

theorem v12_glue_local_representatives_ae (a b : ℝ)
    (q : ∀ R, V12CylinderL2 a b R)
    (hcompat : ∀ R S, R ≤ S →
      (q R : V12Spacetime → V12Field)
        =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] q S)
    (R : ℕ) :
    v12_glue_local_representatives a b q
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] q R := by
  classical
  have hpair : ∀ n : ℕ, ∀ᵐ z ∂v12_slab_measure a b,
      n ≤ R → z ∈ v12_spatial_cylinder n → q n z = q R z := by
    intro n
    by_cases hn : n ≤ R
    · have h := (ae_restrict_iff' (v12_spatial_cylinder_measurable n)).mp
        (hcompat n R hn)
      filter_upwards [h] with z hz
      exact fun _ => hz
    · exact Filter.Eventually.of_forall (fun z h => (hn h).elim)
  have hall : ∀ᵐ z ∂v12_slab_measure a b, ∀ n : ℕ,
      n ≤ R → z ∈ v12_spatial_cylinder n → q n z = q R z :=
    ae_all_iff.mpr hpair
  filter_upwards [ae_restrict_of_ae hall,
    ae_restrict_mem (v12_spatial_cylinder_measurable R)] with z hz hzR
  exact hz (Nat.find (v12_spatial_cylinder_exhausts z))
    (Nat.find_min' (v12_spatial_cylinder_exhausts z) hzR)
    (Nat.find_spec (v12_spatial_cylinder_exhausts z))

/-- Same-sequence local L2 limits give one globally measurable local limit. -/
theorem v12_measurable_local_limit_from_common_sequence
    (a b : ℝ) (u : ℕ → V12SlabL2 a b)
    (q : ∀ R, V12CylinderL2 a b R)
    (hlim : ∀ R, Tendsto (fun n => v12_localize a b R (u n)) atTop (𝓝 (q R))) :
    ∃ g : V12Spacetime → V12Field,
      AEStronglyMeasurable g (v12_slab_measure a b) ∧
      ∀ R, ∃ hg : MemLp g 2
          ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)),
        Tendsto (fun n => v12_localize a b R (u n)) atTop (𝓝 (hg.toLp g)) := by
  let g := v12_glue_local_representatives a b q
  have hcompat : ∀ R S, R ≤ S →
      (q R : V12Spacetime → V12Field)
        =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] q S := by
    intro R S hRS
    exact v12_local_limits_ae_compatible a b hRS u (q R) (q S) (hlim R) (hlim S)
  have heq : ∀ R, g =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] q R :=
    v12_glue_local_representatives_ae a b q hcompat
  have hLp : ∀ R, MemLp g 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)) :=
    fun R => MemLp.ae_eq (heq R).symm (Lp.memLp (q R))
  have hmeas := AEStronglyMeasurable.iUnion (fun R => (hLp R).aestronglyMeasurable)
  rw [v12_spatial_cylinder_iUnion, Measure.restrict_univ] at hmeas
  refine ⟨g, hmeas, ?_⟩
  intro R
  refine ⟨hLp R, ?_⟩
  have hclass : (hLp R).toLp g = q R := by
    apply Lp.ext_iff.mpr
    exact (hLp R).coeFn_toLp.trans (heq R)
  rw [hclass]
  exact hlim R

/-- Choose one strongly measurable representative without changing any local limit. -/
theorem v12_stronglyMeasurable_local_limit_from_common_sequence
    (a b : ℝ) (u : ℕ → V12SlabL2 a b)
    (q : ∀ R, V12CylinderL2 a b R)
    (hlim : ∀ R, Tendsto (fun n => v12_localize a b R (u n)) atTop (𝓝 (q R))) :
    ∃ g : V12Spacetime → V12Field,
      StronglyMeasurable g ∧
      ∀ R, ∃ hg : MemLp g 2
          ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)),
        Tendsto (fun n => v12_localize a b R (u n)) atTop (𝓝 (hg.toLp g)) := by
  obtain ⟨g, hg, hlocal⟩ :=
    v12_measurable_local_limit_from_common_sequence a b u q hlim
  refine ⟨hg.mk g, hg.stronglyMeasurable_mk, ?_⟩
  intro R
  obtain ⟨hLp, hconv⟩ := hlocal R
  have heq : g =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] hg.mk g :=
    ae_restrict_of_ae hg.ae_eq_mk
  have hLp' := MemLp.ae_eq heq hLp
  refine ⟨hLp', ?_⟩
  have hclass : hLp'.toLp (hg.mk g) = hLp.toLp g := by
    apply Lp.ext_iff.mpr
    exact hLp'.coeFn_toLp.trans (heq.symm.trans hLp.coeFn_toLp.symm)
  rw [hclass]
  exact hconv

#print axioms v12_stronglyMeasurable_local_limit_from_common_sequence

#print axioms v12_spatial_cylinder_measurable
#print axioms v12_spatial_cylinder_exhausts
#print axioms v12_glue_local_representatives_ae
#print axioms v12_measurable_local_limit_from_common_sequence

end SMScattering.W20Full
