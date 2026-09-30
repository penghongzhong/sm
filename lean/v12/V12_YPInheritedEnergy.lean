import lean.v12.V12_YOInheritedBounds

/-! Preserve the original a.e.-time spatial L2 energy bound through local
spacetime strong L2 convergence, using actual Fubini slices and Fatou. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_local_energy_inherited
    (a b : ℝ) (R : ℕ) (f : ℕ → V12Spacetime → V12Field) (u : V12Spacetime → V12Field)
    (hu : StronglyMeasurable u)
    (hf2 : ∀ n, MemLp (f n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hu2 : MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : Tendsto (fun n => (eLpNorm (fun z => f n z - u z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (M : ℝ≥0∞) (hM : M ≠ ∞)
    (hE : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => f n (t,x)) 2 (volume : Measure V12Spatial) ≤ M) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => u (t,x)) 2
        ((volume : Measure V12Spatial).restrict (Metric.ball 0 ((R : ℝ) + 1))) ≤ M := by
  let μ := (v12_slab_measure a b).restrict (v12_spatial_cylinder R)
  have he (n : ℕ) : ENNReal.ofReal ((eLpNorm (fun z => f n z - u z) 2 μ).toReal) =
      eLpNorm (fun z => f n z - u z) 2 μ :=
    ENNReal.ofReal_toReal ((hf2 n).sub hu2).eLpNorm_ne_top
  have hENN : Tendsto (fun n => eLpNorm (fun z => f n z - u z) 2 μ) atTop (𝓝 0) := by
    simpa only [Function.comp_def, he, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm
    (μ := μ) (f := f) (g := u) (by norm_num : (2 : ℝ≥0∞) ≠ 0) hENN
  obtain ⟨σ, hσ, hae⟩ := hmeasure.exists_seq_tendsto_ae
  change ∀ᵐ z ∂((v12_slab_measure a b).restrict (v12_spatial_cylinder R)),
    Tendsto (fun n => f (σ n) z) atTop (𝓝 (u z)) at hae
  rw [v12_cylinder_measure_eq_prod] at hae
  have hslices := Measure.ae_ae_of_ae_prod hae
  have hEall := ae_all_iff.mpr hE
  filter_upwards [hslices, hEall] with t ht hEt
  have hum : AEStronglyMeasurable (fun x : V12Spatial => u (t,x))
      ((volume : Measure V12Spatial).restrict (Metric.ball 0 ((R : ℝ) + 1))) :=
    (hu.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hfm : ∀ n, MemLp (fun x => f (σ n) (t,x)) 2 (volume : Measure V12Spatial) := by
    intro n
    change eLpNorm (fun x => f (σ n) (t,x)) 2 volume < ∞
    exact (hEt (σ n)).trans_lt hM.lt_top
  apply Lp.eLpNorm_le_of_ae_tendsto
    (Filter.Eventually.of_forall (fun n =>
      (eLpNorm_mono_measure (fun x => f (σ n) (t,x)) Measure.restrict_le_self).trans (hEt (σ n))))
    (fun n => (hfm n).aestronglyMeasurable.restrict) hum ht

theorem v12_global_energy_inherited
    (a b : ℝ) (f : ℕ → V12Spacetime → V12Field) (u : V12Spacetime → V12Field)
    (hu : StronglyMeasurable u)
    (hf2 : ∀ R n, MemLp (f n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hu2 : ∀ R, MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => f n z - u z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (M : ℝ≥0∞) (hM : M ≠ ∞)
    (hE : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => f n (t,x)) 2 (volume : Measure V12Spatial) ≤ M) :
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => u (t,x)) 2 (volume : Measure V12Spatial) ≤ M := by
  have hall := ae_all_iff.mpr (fun R =>
    v12_local_energy_inherited a b R f u hu (hf2 R) (hu2 R) (hlim R) M hM hE)
  filter_upwards [hall] with t ht
  apply v12_Lp_bound_of_measurable_exhaustion volume (fun x => u (t,x))
    (hu.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (fun R : ℕ => Metric.ball (0 : V12Spatial) ((R : ℝ) + 1))
    (fun R => measurableSet_ball) _ _ 2 M ht
  · intro R S hRS
    exact Metric.ball_subset_ball (add_le_add (Nat.cast_le.mpr hRS) le_rfl)
  · intro x
    obtain ⟨R, hR⟩ := exists_nat_gt ‖x‖
    refine ⟨R, ?_⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hR.trans (lt_add_one _)

#print axioms v12_local_energy_inherited
#print axioms v12_global_energy_inherited
end SMScattering.W20Full
