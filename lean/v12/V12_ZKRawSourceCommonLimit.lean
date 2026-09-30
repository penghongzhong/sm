import lean.v12.V12_ZJRawPDECommonLimit
import lean.v12.V12_YZRawSourceTimeBounds
import lean.v12.V12_YZRawTailIdentification

/-!
Raw-field compactness with actual nonlinear sources. Every time-Lp object,
representative, source bound, cutoff identity, compact set and measurable
local limit is constructed. The frequency-tail hypothesis is stated on the
raw field and its actual convolution, independent of choices of Lp classes.
Remaining upstream assumptions: actual coefficient spacetime bounds and raw
smooth divergence PDE. Hodge/MZ and nonlinear closure are not interfaces here.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_common_limit_from_actual_raw_sources
    (a b : ℝ) (hab : a < b)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (q dq : ℕ → ℝ → V12Spatial → V12Field)
    (A : ℕ → Fin 2 → V12Spacetime → ℂ) (V W : ℕ → V12Spacetime → ℂ)
    (hqcont : ∀ n, ContinuousOn (Function.uncurry (q n)) (Set.Icc a b ×ˢ Set.univ))
    (hdqcont : ∀ n, ContinuousOn (Function.uncurry (dq n)) (Set.Icc a b ×ˢ Set.univ))
    (hder : ∀ n t, t ∈ Set.Ioo a b → ∀ y, HasDerivAt (fun s => q n s y) (dq n t y) t)
    (hq : ∀ n t, t ∈ Set.Ioo a b → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q n t))
    (hAsmooth : ∀ n t, t ∈ Set.Ioo a b → ∀ j,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => A n j (t,y)))
    (hVcont : ∀ n t, t ∈ Set.Ioo a b → Continuous (fun y => V n (t,y)))
    (hWcont : ∀ n t, t ∈ Set.Ioo a b → Continuous (fun y => W n (t,y)))
    (hPDE : ∀ n t, t ∈ Set.Ioo a b → ∀ y,
      dq n t y = v12_rawDivergenceRHS (q n t)
        (fun j y => v12_driftProduct (A n) (Function.uncurry (q n)) j (t,y))
        (fun y => v12_zeroOrderProduct (V n) (W n) (Function.uncurry (q n)) (t,y)) y)
    (hA : ∀ n j, MemLp (A n j) 4 (v12_slab_measure a b))
    (hV : ∀ n, MemLp (V n) 2 (v12_slab_measure a b))
    (hW : ∀ n, MemLp (W n) 2 (v12_slab_measure a b))
    (hq4 : ∀ n, MemLp (Function.uncurry (q n)) 4 (v12_slab_measure a b))
    (M : ℝ) (hM : 0 ≤ M)
    (CA CV CW Z : ℝ≥0∞) (hCA : CA ≠ ∞) (hCV : CV ≠ ∞)
    (hCW : CW ≠ ∞) (hZ : Z ≠ ∞)
    (hEnergy : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (q n t) 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M)
    (hAbound : ∀ n j, eLpNorm (A n j) 4 (v12_slab_measure a b) ≤ CA)
    (hVbound : ∀ n, eLpNorm (V n) 2 (v12_slab_measure a b) ≤ CV)
    (hWbound : ∀ n, eLpNorm (W n) 2 (v12_slab_measure a b) ≤ CW)
    (hqbound : ∀ n, eLpNorm (Function.uncurry (q n)) 4 (v12_slab_measure a b) ≤ Z)
    (hTight : Tendsto (fun N => sSup (Set.range (fun n =>
      v12_rawFrequencyTail a b p hpc hps N (q n)))) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (u : V12Spacetime → V12Field), StrictMono σ ∧
      StronglyMeasurable u ∧ ∀ R,
        MemLp u 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)) ∧
        (∀ n, MemLp (Function.uncurry (q (σ n))) 2
          ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))) ∧
        Tendsto (fun n => (eLpNorm (fun z : V12Spacetime => q (σ n) z.1 z.2 - u z)
          2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) := by
  classical
  choose Q F G hQr hE hQ hFr hGr hF hG hFn hGn using fun n =>
    v12_actual_raw_time_realizations a b hab (q n) (hqcont n) (A n) (V n) (W n)
      (hA n) (hV n) (hW n) (hq4 n) M hM (hEnergy n)
  let f : ℕ → Fin 2 → ℝ → V12Spatial → V12Field := fun n j t y =>
    v12_driftProduct (A n) (Function.uncurry (q n)) j (t,y)
  let g : ℕ → ℝ → V12Spatial → V12Field := fun n t y =>
    v12_zeroOrderProduct (V n) (W n) (Function.uncurry (q n)) (t,y)
  have hf : ∀ n t, t ∈ Set.Ioo a b → ∀ j,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f n j t) := by
    intro n t ht j
    exact (hAsmooth n t ht j).smul (hq n t ht)
  have hg : ∀ n t, t ∈ Set.Ioo a b → Continuous (g n t) := by
    intro n t ht
    exact ((hVcont n t ht).smul (hq n t ht).continuous).add
      ((hWcont n t ht).smul (v12_conjugateField_continuous.comp (hq n t ht).continuous))
  have hFnorm : ∀ n j, eLpNorm (F n j) 2
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ CA * Z := by
    intro n j
    exact (hFn n j).trans (mul_le_mul' (hAbound n j) (hqbound n))
  have hGnorm : ∀ n, eLpNorm (G n) ((4 : ℝ≥0∞) / 3)
      ((volume : Measure ℝ).restrict (Set.Icc a b)) ≤ (CV + CW) * Z := by
    intro n
    exact (hGn n).trans (mul_le_mul' (add_le_add (hVbound n) (hWbound n)) (hqbound n))
  have hT : Tendsto (fun N => sSup (Set.range (fun n =>
      ‖v12_rawSlabClass a b (q n) (hqcont n) (Q n) (hQ n) (hQr n) -
        v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n)‖))) atTop (𝓝 0) := by
    have heq : ∀ N n,
        ‖v12_rawSlabClass a b (q n) (hqcont n) (Q n) (hQ n) (hQr n) -
          v12_spacetimeCutoffClass a b p hpc hps N (Q n) (hQ n)‖ =
        v12_rawFrequencyTail a b p hpc hps N (q n) := fun N n =>
      (v12_rawFrequencyTail_eq_class_norm a b p hpc hps N (q n) (hqcont n)
        (Q n) (hQ n) (hQr n)).symm
    simp_rw [heq]
    exact hTight
  obtain ⟨σ, u, hσ, hu, hlocal⟩ := v12_common_measurable_limit_from_raw_pde
    a b hab.le p hpc hps q dq g f Q F G hqcont hdqcont hder hPDE hq hf hg
    hQr hFr hGr hQ hF hG M (CA * Z) ((CV + CW) * Z)
    (by finiteness) (by finiteness) hE hFnorm hGnorm hT
  refine ⟨σ, u, hσ, hu, ?_⟩
  intro R
  obtain ⟨huR, hconv⟩ := hlocal R
  let c : ℕ → V12CylinderL2 a b R := fun n => v12_localize a b R
    (v12_rawSlabClass a b (q (σ n)) (hqcont (σ n)) (Q (σ n)) (hQ (σ n)) (hQr (σ n)))
  have hcr : ∀ n, (c n : V12Spacetime → V12Field)
      =ᵐ[(v12_slab_measure a b).restrict (v12_spatial_cylinder R)] Function.uncurry (q (σ n)) := by
    intro n
    exact (v12_localize_coeFn a b R _).trans (ae_restrict_of_ae
      (v12_rawSlabClass_ae a b (q (σ n)) (hqcont (σ n)) (Q (σ n)) (hQ (σ n)) (hQr (σ n))))
  refine ⟨huR, (fun n => MemLp.ae_eq (hcr n) (Lp.memLp (c n))), ?_⟩
  have heq : ∀ n, dist (c n) (huR.toLp u) =
      (eLpNorm (fun z : V12Spacetime => q (σ n) z.1 z.2 - u z) 2
        ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal := by
    intro n
    rw [Lp.dist_def]
    apply congrArg ENNReal.toReal
    exact eLpNorm_congr_ae ((hcr n).sub huR.coeFn_toLp)
  have hd := tendsto_iff_dist_tendsto_zero.mp hconv
  change Tendsto (fun n => dist (c n) (huR.toLp u)) atTop (𝓝 0) at hd
  simpa only [heq] using hd

#print axioms v12_common_limit_from_actual_raw_sources
end SMScattering.W20Full
