import lean.v12.V12_FrequencyTightnessLimit
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Sequences

/-!
W20 Theorem 7.2, v6:eq:good-time and v6:eq:every-time-energy.
The raw field is kept fixed. Pointwise time continuity and the actual
a.e.-in-time norm bound give the norm bound at EVERY time, including both
endpoints. No continuity with values in L2 is assumed.

A nondegenerate interval is necessary: on a singleton interval the a.e.
hypothesis is vacuous. Construction of time-Bochner measurability and the
PDE time integral identity are separate obligations, not claimed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal

/-- Full-measure good times are dense up to both endpoints. -/
theorem v12_good_times_closure (a b : ℝ) (hab : a < b) (P : ℝ → Prop)
    (hP : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b), P t) :
    closure {t : ℝ | t ∈ Set.Icc a b ∧ P t} = Set.Icc a b := by
  have hD : Dense {t : ℝ | t ∈ Set.Icc a b → P t} :=
    Measure.dense_of_ae (ae_imp_of_ae_restrict hP)
  have hinner : Set.Ioo a b ⊆ closure {t : ℝ | t ∈ Set.Icc a b ∧ P t} := by
    intro t ht
    apply mem_closure_iff.mpr
    intro U hU htU
    obtain ⟨s, hsD, hsU, hsI⟩ :=
      hD.exists_mem_open (hU.inter isOpen_Ioo) ⟨t, htU, ht⟩
    have hs : s ∈ Set.Icc a b := ⟨hsI.1.le, hsI.2.le⟩
    exact ⟨s, hsU, hs, hsD hs⟩
  apply Set.Subset.antisymm
  · exact closure_minimal (fun t ht => ht.1) isClosed_Icc
  · have hcl := closure_minimal hinner isClosed_closure
    simpa only [closure_Ioo hab.ne] using hcl

/-- Fatou along good times transfers an actual spatial Lp bound to every
closed-interval time. Spatial measurability is required only on that interval. -/
theorem v12_time_slice_eLpNorm_le_of_ae
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (a b : ℝ) (hab : a < b)
    (Q : ℝ → Ω → E) (p : ℝ≥0∞) (C : ℝ≥0∞)
    (hmeas : ∀ t ∈ Set.Icc a b, AEStronglyMeasurable (Q t) μ)
    (htime : ∀ x : Ω, ContinuousOn (fun t => Q t x) (Set.Icc a b))
    (hbound : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (Q t) p μ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc a b) : eLpNorm (Q t) p μ ≤ C := by
  have hclosure : t ∈ closure
      {s : ℝ | s ∈ Set.Icc a b ∧ eLpNorm (Q s) p μ ≤ C} := by
    rw [v12_good_times_closure a b hab (fun s => eLpNorm (Q s) p μ ≤ C) hbound]
    exact ht
  obtain ⟨τ, hτmem, hτlim⟩ := mem_closure_iff_seq_limit.mp hclosure
  have hτwithin : Tendsto τ atTop (𝓝[Set.Icc a b] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hτlim, Filter.Eventually.of_forall (fun n => (hτmem n).1)⟩
  apply Lp.eLpNorm_le_of_ae_tendsto
    (Filter.Eventually.of_forall (fun n => (hτmem n).2))
    (fun n => hmeas (τ n) (hτmem n).1) (hmeas t ht)
  exact Filter.Eventually.of_forall
    (fun x => ((htime x) t ht).tendsto.comp hτwithin)

/-- Exact W20 C2-valued spatial specialization, still for the same raw Q. -/
theorem v12_raw_field_every_time_L2_bound
    (a b : ℝ) (hab : a < b) (Q : ℝ → V12Spatial → V12Field)
    (M : ℝ)
    (hmeas : ∀ t ∈ Set.Icc a b,
      AEStronglyMeasurable (Q t) (volume : Measure V12Spatial))
    (htime : ∀ x : V12Spatial, ContinuousOn (fun t => Q t x) (Set.Icc a b))
    (hbound : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (Q t) 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    eLpNorm (Q t) 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M :=
  v12_time_slice_eLpNorm_le_of_ae (volume : Measure V12Spatial) a b hab
    Q 2 (ENNReal.ofReal M) hmeas htime hbound ht

/-- Actual spatial L2 classes with an every-time norm bound and exact a.e.
raw-field identity. No temporal measurability is inferred from this choice. -/
theorem v12_exists_every_time_L2_realization
    (a b : ℝ) (hab : a < b) (Q : ℝ → V12Spatial → V12Field)
    (M : ℝ) (hM : 0 ≤ M)
    (hmeas : ∀ t ∈ Set.Icc a b,
      AEStronglyMeasurable (Q t) (volume : Measure V12Spatial))
    (htime : ∀ x : V12Spatial, ContinuousOn (fun t => Q t x) (Set.Icc a b))
    (hbound : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (Q t) 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M) :
    ∃ q : ℝ → V12SpatialL2, ∀ t ∈ Set.Icc a b,
      ((q t : V12Spatial → V12Field) =ᵐ[volume] Q t) ∧ ‖q t‖ ≤ M := by
  classical
  have hall : ∀ t ∈ Set.Icc a b,
      eLpNorm (Q t) 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M :=
    fun t ht => v12_raw_field_every_time_L2_bound a b hab Q M hmeas htime hbound ht
  have hLp : ∀ t ∈ Set.Icc a b, MemLp (Q t) 2 (volume : Measure V12Spatial) :=
    fun t ht => (hall t ht).trans_lt ENNReal.ofReal_lt_top
  let q : ℝ → V12SpatialL2 := fun t =>
    if ht : t ∈ Set.Icc a b then (hLp t ht).toLp (Q t) else 0
  refine ⟨q, ?_⟩
  intro t ht
  have hq : q t = (hLp t ht).toLp (Q t) := by simp only [q, dif_pos ht]
  have hrep : (q t : V12Spatial → V12Field) =ᵐ[volume] Q t := by
    rw [hq]
    exact (hLp t ht).coeFn_toLp
  refine ⟨hrep, ?_⟩
  rw [Lp.norm_def, eLpNorm_congr_ae hrep]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hall t ht)).trans_eq
    (ENNReal.toReal_ofReal hM)

#print axioms v12_good_times_closure
#print axioms v12_time_slice_eLpNorm_le_of_ae
#print axioms v12_raw_field_every_time_L2_bound
#print axioms v12_exists_every_time_L2_realization

end SMScattering.W20Full
