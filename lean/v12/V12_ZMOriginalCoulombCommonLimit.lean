import lean.v12.V12_ZLCoulombCommonLimit
import lean.v12.V12_YZZBUOriginalSourceBudgets

/-! Original smooth Coulomb fields enter the common-subsequence theorem
with every A/V/W Lp budget proved from their same-Q definitions. The
remaining geometric construction and smooth-gauge correspondence belong
to the full-paper application and are not asserted by this theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_original_coulomb_common_limit
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (hab : a ≤ b)
    (p : V12Spatial → ℝ) (hpc : HasCompactSupport p)
    (hps : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) p)
    (q dq : ℕ → ℝ → V12Spatial → V12Field)
    (A0 V : ℕ → V12Spacetime → ℂ)
    (hqcont : ∀ n, ContinuousOn (Function.uncurry (q n)) (Set.Icc a b ×ˢ Set.univ))
    (hdqcont : ∀ n, ContinuousOn (Function.uncurry (dq n)) (Set.Icc a b ×ˢ Set.univ))
    (hder : ∀ n t, t ∈ Set.Ioo a b → ∀ y, HasDerivAt (fun s => q n s y) (dq n t y) t)
    (hq : ∀ n t, t ∈ Set.Ioo a b → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q n t))
    (hAsmooth : ∀ n t, t ∈ Set.Ioo a b → ∀ j,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y => v12_actualCoulombA (Function.uncurry (q n)) j (t,y)))
    (hVcont : ∀ n t, t ∈ Set.Ioo a b → Continuous (fun y => V n (t,y)))
    (hA0cont : ∀ n, ContinuousOn (A0 n) (Set.Icc a b ×ˢ Set.univ))
    (hq4 : ∀ n, MemLp (Function.uncurry (q n)) 4 (v12_slab_measure a b))
    (hA0formula : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      ∀ ht : MemLp (q n t) 4 (volume : Measure V12Spatial),
      (fun x => A0 n (t,x)) =ᵐ[volume]
      (v12_temporalCoulombClass
        (fun j k => v12_SL2Class volume j k (q n t) ht)
        (v12_massComplexL2Class volume (q n t) ht) : V12Spatial → ℂ))
    (hVformula : ∀ n z, V n z = -A0 n z +
      ((‖v12_spacetimeHodge (Function.uncurry (q n)) z‖^2 : ℝ) : ℂ) -
      (2 : ℂ) * ((‖Function.uncurry (q n) z‖^2 : ℝ) : ℂ))
    (hdiv : ∀ n t, t ∈ Set.Ioo a b → ∀ y,
      fderiv ℝ (fun x => v12_actualCoulombA (Function.uncurry (q n)) 0 (t,x)) y
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (fun x => v12_actualCoulombA (Function.uncurry (q n)) 1 (t,x)) y
          (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0)
    (hCoulomb : ∀ n t, t ∈ Set.Ioo a b → ∀ y,
      let e := EuclideanSpace.basisFun (Fin 2) ℝ
      Complex.I • dq n t y +
        (fderiv ℝ (fun x => fderiv ℝ (q n t) x (e 0)) y (e 0) +
         fderiv ℝ (fun x => fderiv ℝ (q n t) x (e 1)) y (e 1)) =
      (2 * Complex.I) •
        (v12_actualCoulombA (Function.uncurry (q n)) 0 (t,y) • fderiv ℝ (q n t) y (e 0) +
         v12_actualCoulombA (Function.uncurry (q n)) 1 (t,y) • fderiv ℝ (q n t) y (e 1)) +
      v12_zeroOrderProduct (V n) (fun z => v12_WDensity (Function.uncurry (q n) z))
        (Function.uncurry (q n)) (t,y))
    (M : ℝ) (hM : 0 ≤ M) (Z : ℝ≥0∞) (hZ : Z ≠ ∞)
    (hEnergy : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (q n t) 2 (volume : Measure V12Spatial) ≤ ENNReal.ofReal M)
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
  obtain ⟨CA, hCA, CV, hCV, hB⟩ := v12_original_source_coefficient_budgets hHLS
  have hs n := hB a b (Function.uncurry (q n)) (hqcont n) (hq4 n) M hM
    (hEnergy n) Z hZ (hqbound n) (A0 n) (V n) (hA0cont n) (hA0formula n) (hVformula n)
  have hWcont : ∀ n t, t ∈ Set.Ioo a b →
      Continuous (fun y => v12_WDensity (Function.uncurry (q n) (t,y))) := by
    intro n t ht
    exact v12_WDensity_continuous.comp (hq n t ht).continuous
  exact v12_common_limit_from_coulomb_equation a b hab p hpc hps q dq
    (fun n => v12_actualCoulombA (Function.uncurry (q n))) V
    (fun n z => v12_WDensity (Function.uncurry (q n) z))
    hqcont hdqcont hder hq hAsmooth hVcont hWcont hdiv hCoulomb
    (fun n j => ((hs n).1 j).1) (fun n => (hs n).2.1.1)
    (fun n => (hs n).2.2.1) hq4 M hM (CA*ENNReal.ofReal M*Z)
    (ENNReal.ofReal ((24+CV*M^2)*Z.toReal^2)) (2*Z^2) Z
    (by finiteness) (by finiteness) (by finiteness) hZ hEnergy
    (fun n j => ((hs n).1 j).2) (fun n => (hs n).2.1.2)
    (fun n => (hs n).2.2.2) hqbound hTight

#print axioms v12_original_coulomb_common_limit
end SMScattering.W20Full
