import lean.v12.V12_YMeasurableLocalLimitGluing
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Preserve genuine Lp budgets under raw local L2 convergence. Fatou is
applied on each cylinder, then exhaustion recovers the global budget. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_Lp_bound_of_raw_L2_limit
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : ℕ → Ω → E) (g : Ω → E)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => (eLpNorm (fun x => f n x - g x) 2 μ).toReal) atTop (𝓝 0))
    (p C : ℝ≥0∞) (hb : ∀ n, eLpNorm (f n) p μ ≤ C) :
    eLpNorm g p μ ≤ C := by
  have hfin (n : ℕ) : eLpNorm (fun x => f n x - g x) 2 μ ≠ ∞ :=
    ((hf n).sub hg).eLpNorm_ne_top
  have he (n : ℕ) : ENNReal.ofReal ((eLpNorm (fun x => f n x - g x) 2 μ).toReal) =
      eLpNorm (fun x => f n x - g x) 2 μ := ENNReal.ofReal_toReal (hfin n)
  have hENN : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ) atTop (𝓝 0) := by
    simpa only [Function.comp_def, he, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm (μ := μ) (f := f) (g := g) (by norm_num : (2 : ℝ≥0∞) ≠ 0) hENN
  obtain ⟨σ, hσ, hae⟩ := hmeasure.exists_seq_tendsto_ae
  exact Lp.eLpNorm_le_of_ae_tendsto
    (Filter.Eventually.of_forall (fun n => hb (σ n)))
    (fun n => (hf (σ n)).aestronglyMeasurable) hg.aestronglyMeasurable hae

theorem v12_Lp_bound_of_measurable_exhaustion
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (u : Ω → E) (hu : AEStronglyMeasurable u μ)
    (s : ℕ → Set Ω) (hs : ∀ R, MeasurableSet (s R))
    (hmono : Monotone s) (hex : ∀ z, ∃ R, z ∈ s R)
    (p C : ℝ≥0∞) (hb : ∀ R, eLpNorm u p (μ.restrict (s R)) ≤ C) :
    eLpNorm u p μ ≤ C := by
  let f : ℕ → Ω → E := fun R => (s R).indicator u
  have hm : ∀ R, AEStronglyMeasurable (f R) μ := fun R => hu.indicator (hs R)
  have hbn : ∀ R, eLpNorm (f R) p μ ≤ C := by
    intro R
    change eLpNorm ((s R).indicator u) p μ ≤ C
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hs R).nullMeasurableSet]
    exact hb R
  apply Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbn) hm hu
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨R0, hR0⟩ := hex z
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop R0] with R hR
  have hz : z ∈ s R := hmono hR hR0
  simp [f, hz]

theorem v12_global_Lp_bound_of_cylinders
    (μ : Measure V12Spacetime) (u : V12Spacetime → V12Field)
    (hu : AEStronglyMeasurable u μ) (p C : ℝ≥0∞)
    (hb : ∀ R, eLpNorm u p (μ.restrict (v12_spatial_cylinder R)) ≤ C) :
    eLpNorm u p μ ≤ C := by
  apply v12_Lp_bound_of_measurable_exhaustion μ u hu v12_spatial_cylinder
    v12_spatial_cylinder_measurable _ v12_spatial_cylinder_exhausts p C hb
  intro R S hRS z hz
  change ‖z.2‖ < (S : ℝ) + 1
  change ‖z.2‖ < (R : ℝ) + 1 at hz
  exact hz.trans_le (add_le_add (Nat.cast_le.mpr hRS) le_rfl)

theorem v12_global_budget_inherited_from_local_L2
    (a b : ℝ) (f : ℕ → V12Spacetime → V12Field) (u : V12Spacetime → V12Field)
    (hu : StronglyMeasurable u)
    (hf2 : ∀ R n, MemLp (f n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hu2 : ∀ R, MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => f n z - u z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (p C : ℝ≥0∞) (hb : ∀ n, eLpNorm (f n) p (v12_slab_measure a b) ≤ C) :
    eLpNorm u p (v12_slab_measure a b) ≤ C := by
  apply v12_global_Lp_bound_of_cylinders (v12_slab_measure a b) u hu.aestronglyMeasurable p C
  intro R
  apply v12_Lp_bound_of_raw_L2_limit _ f u (hf2 R) (hu2 R) (hlim R) p C
  intro n
  exact (eLpNorm_mono_measure (f n) Measure.restrict_le_self).trans (hb n)

#print axioms v12_Lp_bound_of_raw_L2_limit
#print axioms v12_Lp_bound_of_measurable_exhaustion
#print axioms v12_global_Lp_bound_of_cylinders
#print axioms v12_global_budget_inherited_from_local_L2
end SMScattering.W20Full
