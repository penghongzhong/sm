import lean.v12.V12_WeakTimeIntegration
import lean.v12.V12_SpatialEquicontinuity

/-!
W20 Theorem 7.2: actual fixed-cutoff cylinder compactness.
The cylinder representative is constructed here, not assumed continuous.
Spatial regularity comes from L2 kernel translation continuity. Time
regularity comes from the established integral identity and the source
budget. No equicontinuity, ambient spacetime continuity, or compactness
hypothesis is accepted by the terminal theorem.

Boundary: the same-field source realization, uniform energy representatives,
coefficient budget, integral identity, and local L2 representative equality
remain explicit application inputs. This module does not certify the full PDE.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_cylinder_time_mem (a b : ℝ) (R : ℕ) (hab : a ≤ b)
    (z : V12CompactCylinder a b R) : z.1.1 ∈ Set.Icc a b := by
  have hz : z.1.1 ∈ Set.Icc (min a b) (max a b) := z.2.1
  simpa only [min_eq_left hab, max_eq_right hab] using hz

noncomputable def v12_cutoffCylinderValue (a b : ℝ) (R : ℕ)
    (k : V12ScalarL2) (Q : ℕ → ℝ → V12SpatialL2)
    (n : ℕ) (z : V12CompactCylinder a b R) : V12Field :=
  v12_L2ConvolutionRep k (Q n z.1.1) z.1.2

/-- A local modulus on the actual compact cylinder. The time family need
not be defined continuously outside the closed manuscript interval. -/
theorem v12_cutoffCylinder_equicontinuous
    (a b : ℝ) (R : ℕ) (hab : a ≤ b)
    (k : V12ScalarL2) (Q : ℕ → ℝ → V12SpatialL2)
    (M C : ℝ)
    (hEnergy : ∀ n t, t ∈ Set.Icc a b → ‖Q n t‖ ≤ M)
    (hTime : ∀ n s, s ∈ Set.Icc a b → ∀ t, t ∈ Set.Icc a b →
      ∀ x : V12Spatial,
        dist (v12_L2ConvolutionRep k (Q n s) x)
          (v12_L2ConvolutionRep k (Q n t) x) ≤
          C * |t - s| ^ ((1 : ℝ) / 4)) :
    Equicontinuous (v12_cutoffCylinderValue a b R k Q) := by
  intro z₀
  let b₀ : V12CompactCylinder a b R → ℝ := fun z =>
    ‖v12_L2ConvolutionPairing‖ *
      dist (v12_reflectedTranslate k z₀.1.2)
        (v12_reflectedTranslate k z.1.2) * M +
      C * |z.1.1 - z₀.1.1| ^ ((1 : ℝ) / 4)
  have ht : Continuous (fun z : V12CompactCylinder a b R => z.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hx : Continuous (fun z : V12CompactCylinder a b R => z.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hb : Continuous b₀ := by
    exact ((continuous_const.mul
      (continuous_const.dist ((v12_continuous_reflectedTranslate k).comp hx))).mul
        continuous_const).add
      (continuous_const.mul ((ht.sub continuous_const).abs.rpow_const
        (fun _ => Or.inr (by norm_num))))
  have hlim : Tendsto b₀ (𝓝 z₀) (𝓝 0) := by
    simpa [b₀, Real.zero_rpow (by norm_num : (1 : ℝ) / 4 ≠ 0)] using hb.tendsto z₀
  apply Metric.equicontinuousAt_of_continuity_modulus b₀ hlim
    (v12_cutoffCylinderValue a b R k Q)
  apply Filter.Eventually.of_forall
  intro z n
  have hs := v12_cylinder_time_mem a b R hab z₀
  have ht' := v12_cylinder_time_mem a b R hab z
  have hcoef : 0 ≤ ‖v12_L2ConvolutionPairing‖ *
      dist (v12_reflectedTranslate k z₀.1.2)
        (v12_reflectedTranslate k z.1.2) :=
    mul_nonneg (norm_nonneg v12_L2ConvolutionPairing) dist_nonneg
  have hspace := (v12_L2ConvolutionRep_dist_le k (Q n z₀.1.1) z₀.1.2 z.1.2).trans
    (mul_le_mul_of_nonneg_left (hEnergy n z₀.1.1 hs) hcoef)
  exact (dist_triangle
    (v12_L2ConvolutionRep k (Q n z₀.1.1) z₀.1.2)
    (v12_L2ConvolutionRep k (Q n z₀.1.1) z.1.2)
    (v12_L2ConvolutionRep k (Q n z.1.1) z.1.2)).trans
    (add_le_add hspace (hTime n z₀.1.1 hs z.1.1 ht' z.1.2))

/-- No ambient continuous representative and no local compactness hypothesis.
The only representative input identifies the actual local L2 classes. -/
theorem v12_local_compact_from_cutoff_time_modulus
    (a b : ℝ) (R : ℕ) (hab : a ≤ b)
    (k : V12ScalarL2) (Q : ℕ → ℝ → V12SpatialL2)
    (M C : ℝ)
    (hEnergy : ∀ n t, t ∈ Set.Icc a b → ‖Q n t‖ ≤ M)
    (hTime : ∀ n s, s ∈ Set.Icc a b → ∀ t, t ∈ Set.Icc a b →
      ∀ x : V12Spatial,
        dist (v12_L2ConvolutionRep k (Q n s) x)
          (v12_L2ConvolutionRep k (Q n t) x) ≤
          C * |t - s| ^ ((1 : ℝ) / 4))
    (v : ℕ → V12CylinderL2 a b R)
    (hRep : ∀ n, (v n : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)]
        fun z => v12_L2ConvolutionRep k (Q n z.1) z.2) :
    IsCompact (closure (Set.range v)) := by
  have hEq := v12_cutoffCylinder_equicontinuous a b R hab k Q M C hEnergy hTime
  let F : ℕ → BoundedContinuousFunction (V12CompactCylinder a b R) V12Field :=
    fun n => BoundedContinuousFunction.mkOfCompact
      ⟨v12_cutoffCylinderValue a b R k Q n, hEq.continuous n⟩
  have hEqF : Equicontinuous
      ((↑) : Set.range F → V12CompactCylinder a b R → V12Field) := by
    intro z₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, Hδ⟩ := Metric.equicontinuousAt_iff.mp (hEq z₀) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro z hz f
    obtain ⟨n, hn⟩ := f.property
    change dist (f.val z₀) (f.val z) < ε
    rw [← hn]
    exact Hδ z hz n
  have hBound : ∀ n z, ‖F n z‖ ≤
      ‖v12_L2ConvolutionPairing‖ * ‖k‖ * M := by
    intro n z
    exact (v12_L2ConvolutionRep_norm_le k (Q n z.1.1) z.1.2).trans
      (mul_le_mul_of_nonneg_left
        (hEnergy n z.1.1 (v12_cylinder_time_mem a b R hab z))
        (mul_nonneg (norm_nonneg v12_L2ConvolutionPairing) (norm_nonneg k)))
  have hRepF : ∀ n, (v n : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)]
        fun z => F n (v12_toCompactCylinder a b R z) := by
    intro n
    filter_upwards [hRep n, v12_toCompactCylinder_coe_ae a b R] with z hv hz
    change (v n : V12Spacetime → V12Field) z =
      v12_L2ConvolutionRep k (Q n (v12_toCompactCylinder a b R z).1.1)
        (v12_toCompactCylinder a b R z).1.2
    rw [hz]
    exact hv
  exact v12_ascoli_localLp_compact
    ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))
    (v12_toCompactCylinder a b R) F v
    (‖v12_L2ConvolutionPairing‖ * ‖k‖ * M) hEqF hBound hRepF

/-- Actual source-integral specialization. The spatial/time regularity and
local compactness conclusions are derived, not supplied as input hypotheses. -/
theorem v12_cutoff_local_compact_from_source_integrals
    (a b : ℝ) (R : ℕ) (hab : a ≤ b)
    (p : V12Spatial → ℝ) (hp_cpt : HasCompactSupport p)
    (hp_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p) (N : ℕ)
    (Q : ℕ → ℝ → V12SpatialL2)
    (F : ℕ → Fin 2 → ℝ → V12SpatialL2)
    (G : ℕ → ℝ → V12SpatialLFourThirds)
    (M : ℝ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hEnergy : ∀ n t, t ∈ Set.Icc a b → ‖Q n t‖ ≤ M)
    (hQ : ∀ n, MemLp (Q n) ∞ ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hF : ∀ n j, MemLp (F n j) 2 ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hG : ∀ n, MemLp (G n) ((4 : ℝ≥0∞) / 3)
      ((volume : Measure ℝ).restrict (Set.Icc a b)))
    (hBudget : ∀ n, v12_cutoffSourceBudget p hp_cpt hp_smooth N
      ((volume : Measure ℝ).restrict (Set.Icc a b)) (Q n) (F n) (G n) ≤ C)
    (hIntegral : ∀ n s, s ∈ Set.Icc a b → ∀ t, t ∈ Set.Icc a b → s ≤ t →
      v12_cutoffTimeField p hp_cpt hp_smooth N (Q n) t -
        v12_cutoffTimeField p hp_cpt hp_smooth N (Q n) s =
        ∫ τ in s..t, v12_cutoffTimeSource p hp_cpt hp_smooth N (Q n) (F n) (G n) τ)
    (v : ℕ → V12CylinderL2 a b R)
    (hRep : ∀ n, (v n : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)]
        fun z => v12_cutoffTimeField p hp_cpt hp_smooth N (Q n) z.1 z.2) :
    IsCompact (closure (Set.range v)) := by
  apply v12_local_compact_from_cutoff_time_modulus a b R hab
    (v12_cutoffKernelL2 p hp_cpt hp_smooth N) Q M C.toReal hEnergy
    (v := v) (hRep := hRep)
  intro n s hs t ht x
  have hsource := v12_cutoffTimeSource_memLp p hp_cpt hp_smooth N
    ((volume : Measure ℝ).restrict (Set.Icc a b)) (Q n) (F n) (G n)
    (hQ n) (hF n) (hG n)
  have hbound := (v12_cutoffTimeSource_eLpNorm_le p hp_cpt hp_smooth N
    ((volume : Measure ℝ).restrict (Set.Icc a b)) (Q n) (F n) (G n)
    (hQ n).aestronglyMeasurable (fun j => (hF n j).aestronglyMeasurable)
    (hG n).aestronglyMeasurable).trans (hBudget n)
  have htime := v12_norm_increment_quarter_of_integral_identities a b
    (v12_cutoffTimeField p hp_cpt hp_smooth N (Q n))
    (v12_cutoffTimeSource p hp_cpt hp_smooth N (Q n) (F n) (G n))
    hsource C hC hbound (hIntegral n) hs ht
  calc
    _ ≤ dist (v12_cutoffTimeField p hp_cpt hp_smooth N (Q n) s)
          (v12_cutoffTimeField p hp_cpt hp_smooth N (Q n) t) :=
      BoundedContinuousFunction.dist_coe_le_dist x
    _ = ‖v12_cutoffTimeField p hp_cpt hp_smooth N (Q n) t -
          v12_cutoffTimeField p hp_cpt hp_smooth N (Q n) s‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    _ ≤ C.toReal * |t - s| ^ ((1 : ℝ) / 4) := htime

#print axioms v12_cylinder_time_mem
#print axioms v12_cutoffCylinder_equicontinuous
#print axioms v12_local_compact_from_cutoff_time_modulus
#print axioms v12_cutoff_local_compact_from_source_integrals

end SMScattering.W20Full
