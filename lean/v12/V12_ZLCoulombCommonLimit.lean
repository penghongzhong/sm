import lean.v12.V12_ZKRawSourceCommonLimit
import lean.v12.V12_ZHCoulombPDEToDivergence
import lean.v12.V12_YZeroLengthSlab

/-!
The original i*dt+Laplacian Coulomb equation enters the actual-source
compactness theorem, with its drift divergence derived by the product rule.
The degenerate interval is proved separately. This is not yet full Theorem7.2:
Hodge/MZ coefficient applications and the complete7.1 closure remain open.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_coulomb_time_algebra (d l v g : V12Field)
    (h : Complex.I • d + l = (2 * Complex.I) • v + g) :
    d = Complex.I • l + (2 : ℂ) • v + (-Complex.I) • g := by
  have hi : (-Complex.I) * Complex.I = 1 := by simp
  have hi2 : (-Complex.I) * (2 * Complex.I) = 2 := by
    calc
      (-Complex.I) * (2 * Complex.I) = 2 * ((-Complex.I) * Complex.I) := by ring
      _ = 2 := by rw [hi, mul_one]
  have hh := congrArg (fun z : V12Field => (-Complex.I) • z) h
  simp only [smul_add, smul_smul, hi, hi2, one_smul] at hh
  calc
    d = (d + (-Complex.I) • l) + Complex.I • l := by simp [neg_smul, add_assoc]
    _ = ((2 : ℂ) • v + (-Complex.I) • g) + Complex.I • l := by rw [hh]
    _ = _ := by abel

theorem v12_common_limit_from_coulomb_equation
    (a b : ℝ) (hab : a ≤ b)
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
    (hdiv : ∀ n t, t ∈ Set.Ioo a b → ∀ y,
      fderiv ℝ (fun x => A n 0 (t,x)) y (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      fderiv ℝ (fun x => A n 1 (t,x)) y (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0)
    (hCoulomb : ∀ n t, t ∈ Set.Ioo a b → ∀ y,
      let e := EuclideanSpace.basisFun (Fin 2) ℝ
      Complex.I • dq n t y +
        (fderiv ℝ (fun x => fderiv ℝ (q n t) x (e 0)) y (e 0) +
         fderiv ℝ (fun x => fderiv ℝ (q n t) x (e 1)) y (e 1)) =
      (2 * Complex.I) • (A n 0 (t,y) • fderiv ℝ (q n t) y (e 0) +
        A n 1 (t,y) • fderiv ℝ (q n t) y (e 1)) +
      v12_zeroOrderProduct (V n) (W n) (Function.uncurry (q n)) (t,y))
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
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst b
    exact v12_zero_length_common_limit a q
  · have hPDE : ∀ n t, t ∈ Set.Ioo a b → ∀ y,
        dq n t y = v12_rawDivergenceRHS (q n t)
          (fun j y => v12_driftProduct (A n) (Function.uncurry (q n)) j (t,y))
          (fun y => v12_zeroOrderProduct (V n) (W n) (Function.uncurry (q n)) (t,y)) y := by
      intro n t ht y
      let e := EuclideanSpace.basisFun (Fin 2) ℝ
      have halg := v12_coulomb_time_algebra _ _ _ _ (hCoulomb n t ht y)
      have hdivergence := v12_rawDivergenceRHS_coulomb
        (fun j x => A n j (t,x)) (q n t)
        (fun x => v12_zeroOrderProduct (V n) (W n) (Function.uncurry (q n)) (t,x)) y
        (fun j => (hAsmooth n t ht j).differentiable (by simp) y)
        ((hq n t ht).differentiable (by simp) y) (hdiv n t ht y)
      exact halg.trans hdivergence.symm
    exact v12_common_limit_from_actual_raw_sources a b hlt p hpc hps q dq A V W
      hqcont hdqcont hder hq hAsmooth hVcont hWcont hPDE hA hV hW hq4
      M hM CA CV CW Z hCA hCV hCW hZ hEnergy hAbound hVbound hWbound hqbound hTight

#print axioms v12_coulomb_time_algebra
#print axioms v12_common_limit_from_coulomb_equation
end SMScattering.W20Full
