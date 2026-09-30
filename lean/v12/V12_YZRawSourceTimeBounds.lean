import lean.v12.V12_YUEveryTimeBochnerEnergy
import lean.v12.V12_YTBochnerSectionNorm

/-!
Actual time-valued Q,F,G are constructed from jointly smooth raw Q, its a.e.
energy bound and the raw spacetime nonlinear-source bounds. No time-valued
Lp representatives, Bochner measurability or Fubini norm identification are
inputs. Hodge reconstruction of A,V,W and their M/Z estimates remain upstream.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace SMScattering.W20Full
open MeasureTheory
open scoped ENNReal

theorem v12_actual_raw_time_realizations
    (a b : ℝ) (hab : a < b)
    (q : ℝ → V12Spatial → V12Field)
    (hqcont : ContinuousOn (Function.uncurry q) (Set.Icc a b ×ˢ Set.univ))
    (A : Fin 2 → V12Spacetime → ℂ) (V W : V12Spacetime → ℂ)
    (hA : ∀ j, MemLp (A j) 4 (v12_slab_measure a b))
    (hV : MemLp V 2 (v12_slab_measure a b))
    (hW : MemLp W 2 (v12_slab_measure a b))
    (hq4 : MemLp (Function.uncurry q) 4 (v12_slab_measure a b))
    (M : ℝ) (hM : 0 ≤ M)
    (hEnergy : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (q t) 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M) :
    ∃ (Q : ℝ → V12SpatialL2) (F : Fin 2 → ℝ → V12SpatialL2)
        (G : ℝ → V12SpatialLFourThirds),
      (∀ t ∈ Set.Icc a b, (Q t : V12Spatial → V12Field) =ᵐ[volume] q t) ∧
      (∀ t ∈ Set.Icc a b, ‖Q t‖ ≤ M) ∧
      MemLp Q ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)) ∧
      (∀ j, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        (F j t : V12Spatial → V12Field) =ᵐ[volume]
          fun y => v12_driftProduct A (Function.uncurry q) j (t,y)) ∧
      (∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        (G t : V12Spatial → V12Field) =ᵐ[volume]
          fun y => v12_zeroOrderProduct V W (Function.uncurry q) (t,y)) ∧
      (∀ j, MemLp (F j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b))) ∧
      MemLp G ((4 : ℝ≥0∞) / 3) ((volume : Measure ℝ).restrict (Set.Icc a b)) ∧
      (∀ j, eLpNorm (F j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤
        eLpNorm (A j) 4 (v12_slab_measure a b) *
          eLpNorm (Function.uncurry q) 4 (v12_slab_measure a b)) ∧
      eLpNorm G ((4 : ℝ≥0∞) / 3) ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤
        (eLpNorm V 2 (v12_slab_measure a b) + eLpNorm W 2 (v12_slab_measure a b)) *
          eLpNorm (Function.uncurry q) 4 (v12_slab_measure a b) := by
  have hspace : ∀ t ∈ Set.Icc a b, Continuous (q t) := by
    intro t ht
    apply continuousOn_univ.mp
    exact hqcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => ⟨ht, Set.mem_univ y⟩)
  have htime : ∀ y, ContinuousOn (fun t => q t y) (Set.Icc a b) := by
    intro y
    exact hqcont.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, Set.mem_univ y⟩)
  obtain ⟨Q, hQr, hQLp, _⟩ := v12_exists_every_time_Bochner_L2_realization
    a b hab q M hM (fun t ht => (hspace t ht).aestronglyMeasurable)
    htime hq4.aestronglyMeasurable hEnergy
  obtain ⟨F, G, hFr, hGr, hFLp, hGLp, hFnorm, hGnorm⟩ :=
    v12_exists_actual_source_Bochner_realizations
      ((volume : Measure ℝ).restrict (Set.Icc a b)) A V W (Function.uncurry q)
      hA hV hW hq4
  exact ⟨Q, F, G, (fun t ht => (hQr t ht).1), (fun t ht => (hQr t ht).2),
    hQLp, hFr, hGr, hFLp, hGLp, hFnorm, hGnorm⟩

#print axioms v12_actual_raw_time_realizations
end SMScattering.W20Full
