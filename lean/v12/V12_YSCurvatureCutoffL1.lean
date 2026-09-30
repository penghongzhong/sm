import lean.v12.V12_YRTensorWeakClosure
import lean.v12.V12_YSActualHodgeFarBounds

/-! The density convergence and uniform slice budget used by actual Young
convolution are derived from the same original fields. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_raw_curvature_L1_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (qn : ℕ → Ω → V12Field) (q : Ω → V12Field)
    (hn : ∀ n, MemLp (qn n) 2 μ) (hq : MemLp q 2 μ)
    (hlim : Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2 μ).toReal) atTop (𝓝 0)) :
    (∀ n, Integrable (fun z => v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z)) μ) ∧
    Tendsto (fun n => ∫ z, ‖v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z)‖ ∂μ)
      atTop (𝓝 0) := by
  let Qn := fun n => (hn n).toLp (qn n)
  let Q := hq.toLp q
  have hQ := v12_raw_L2_toLp_tendsto μ qn q hn hq hlim
  have hB := (v12_quadratic_coefficients_strong_L1 μ Qn Q hQ).1
  have hr (r : Ω → V12Field) (h : MemLp r 2 μ) :
      (v12_B_L1Class μ (h.toLp r) : Ω → ℝ) =ᵐ[μ] fun z => v12_curvatureDensity (r z) := by
    filter_upwards [v12_B_L1Class_ae μ (h.toLp r), h.coeFn_toLp] with z hz hqz
    rw [hz, hqz]
    rfl
  have hd (n : ℕ) :
      ((v12_B_L1Class μ (Qn n) - v12_B_L1Class μ Q : Lp ℝ 1 μ) : Ω → ℝ) =ᵐ[μ]
        fun z => v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z) :=
    (Lp.coeFn_sub _ _).trans ((hr (qn n) (hn n)).sub (hr q hq))
  refine ⟨?_, ?_⟩
  · intro n
    exact (memLp_one_iff_integrable.mp (Lp.memLp
      (v12_B_L1Class μ (Qn n) - v12_B_L1Class μ Q))).congr (hd n)
  · have ht := (hB.sub_const (v12_B_L1Class μ Q)).norm
    have he (n : ℕ) : ‖v12_B_L1Class μ (Qn n) - v12_B_L1Class μ Q‖ =
        ∫ z, ‖v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z)‖ ∂μ := by
      rw [L1.norm_eq_integral_norm]
      exact integral_congr_ae ((hd n).fun_comp norm)
    simpa only [sub_self, norm_zero, he] using ht

noncomputable def v12_curvatureCutoffDifference (L : ℝ)
    (qn q : V12Spacetime → V12Field) : V12Spacetime → ℝ :=
  {z : V12Spacetime | ‖z.2‖ < L}.indicator
    (fun z => v12_curvatureDensity (qn z) - v12_curvatureDensity (q z))

theorem v12_curvatureCutoffDifference_stronglyMeasurable
    (L : ℝ) (qn q : V12Spacetime → V12Field)
    (hn : StronglyMeasurable qn) (hq : StronglyMeasurable q) :
    StronglyMeasurable (v12_curvatureCutoffDifference L qn q) := by
  apply ((v12_curvatureDensity_continuous.comp_stronglyMeasurable hn).sub
    (v12_curvatureDensity_continuous.comp_stronglyMeasurable hq)).indicator
  exact measurableSet_lt measurable_snd.norm measurable_const

theorem v12_curvatureCutoffDifference_L1_limit
    (a b : ℝ) (R : ℕ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hn : ∀ n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq : MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : Tendsto (fun n => (eLpNorm (fun z => qn n z - q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0)) :
    (∀ n, Integrable (v12_curvatureCutoffDifference ((R : ℝ)+1) (qn n) q) (v12_slab_measure a b)) ∧
    Tendsto (fun n => ∫ z, ‖v12_curvatureCutoffDifference ((R : ℝ)+1) (qn n) q z‖
      ∂v12_slab_measure a b) atTop (𝓝 0) := by
  obtain ⟨hi, ht⟩ := v12_raw_curvature_L1_limit _ qn q hn hq hlim
  refine ⟨?_, ?_⟩
  · intro n
    exact (integrable_indicator_iff (v12_spatial_cylinder_measurable R)).2 (hi n)
  · have he (n : ℕ) :
        (∫ z, ‖v12_curvatureCutoffDifference ((R : ℝ)+1) (qn n) q z‖ ∂v12_slab_measure a b) =
          ∫ z, ‖v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z)‖
            ∂(v12_slab_measure a b).restrict (v12_spatial_cylinder R) := by
      simp only [v12_curvatureCutoffDifference, norm_indicator_eq_indicator_norm]
      exact integral_indicator (v12_spatial_cylinder_measurable R)
    simpa only [he] using ht

theorem v12_curvature_difference_cutoff_energy
    (L : ℝ) (qn q : V12Spatial → V12Field)
    (hn : MemLp qn 2 (volume : Measure V12Spatial)) (hq : MemLp q 2 (volume : Measure V12Spatial))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : eLpNorm qn 2 volume ≤ ENNReal.ofReal M) (hEq : eLpNorm q 2 volume ≤ ENNReal.ofReal M) :
    (∫ y, ‖(Metric.ball (0 : V12Spatial) L).indicator
      (fun y => v12_curvatureDensity (qn y) - v12_curvatureDensity (q y)) y‖) ≤ 4*M^2 := by
  obtain ⟨hin, hbn⟩ := v12_actual_curvature_integral_bound qn hn M hM hEn
  obtain ⟨hiq, hbq⟩ := v12_actual_curvature_integral_bound q hq M hM hEq
  have hid := (hin.sub hiq).indicator (measurableSet_ball (x := (0 : V12Spatial)) (ε := L))
  calc
    _ ≤ ∫ y, ‖v12_curvatureDensity (qn y)‖ + ‖v12_curvatureDensity (q y)‖ := by
      apply integral_mono hid.norm (hin.norm.add hiq.norm)
      intro y
      exact (norm_indicator_le_norm_self _ _ _).trans (norm_sub_le _ _)
    _ = (∫ y, ‖v12_curvatureDensity (qn y)‖) + (∫ y, ‖v12_curvatureDensity (q y)‖) :=
      integral_add hin.norm hiq.norm
    _ ≤ 4*M^2 := by linarith

#print axioms v12_raw_curvature_L1_limit
#print axioms v12_curvatureCutoffDifference_L1_limit
#print axioms v12_curvature_difference_cutoff_energy
end SMScattering.W20Full
