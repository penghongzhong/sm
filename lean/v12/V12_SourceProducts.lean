import lean.v12.V12_FrequencyTightnessLimit

/-!
Actual products entering the cutoff evolution. The fields F_j and G are
constructed as A_j Q and V Q + W conjugate(Q), not supplied independently.
This file proves the Holder-product part of the source budget. It does not
certify the Hodge reconstruction estimates for A,V,W or the time/spacetime
Fubini realization. Scalars may be complex; real Coulomb coefficients are
included through their usual complex embedding.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open Filter MeasureTheory
open scoped ENNReal

/-- Coordinatewise complex conjugation on the actual two-component field. -/
noncomputable def v12_conjugateField (v : V12Field) : V12Field :=
  WithLp.toLp 2 (fun j : Fin 2 => star (v j))

@[simp]
theorem v12_conjugateField_apply (v : V12Field) (j : Fin 2) :
    v12_conjugateField v j = star (v j) := rfl

theorem v12_conjugateField_continuous : Continuous v12_conjugateField := by
  change Continuous (fun v : V12Field =>
    (EuclideanSpace.equiv (Fin 2) ℂ).symm (fun j : Fin 2 => star (v j)))
  exact (EuclideanSpace.equiv (Fin 2) ℂ).symm.continuous.comp
    (continuous_pi (fun j => continuous_star.comp
      (EuclideanSpace.proj (𝕜 := ℂ) j).continuous))

@[simp]
theorem v12_conjugateField_norm (v : V12Field) :
    ‖v12_conjugateField v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, v12_conjugateField_apply, norm_star]

/-- Exact preservation of the spacetime seminorm by field conjugation. -/
theorem v12_eLpNorm_conjugateField
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Q : Ω → V12Field) (q : ℝ≥0∞)
    (hQ : AEStronglyMeasurable Q μ) :
    eLpNorm (fun z => v12_conjugateField (Q z)) q μ = eLpNorm Q q μ := by
  exact eLpNorm_congr_norm_ae
    (v12_conjugateField_continuous.comp_aestronglyMeasurable hQ) hQ
    (Filter.Eventually.of_forall (fun z => v12_conjugateField_norm (Q z)))

theorem v12_holderTriple_four_four_two :
    ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  have h : Real.HolderTriple (4 : ℝ) 4 2 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using h.ennrealOfReal

theorem v12_holderTriple_two_four_fourThirds :
    ENNReal.HolderTriple (2 : ℝ≥0∞) 4 ((4 : ℝ≥0∞) / 3) := by
  have h : Real.HolderTriple (2 : ℝ) 4 ((4 : ℝ) / 3) :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have h4 : ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) := by norm_num
  have h43 : ENNReal.ofReal ((4 : ℝ) / 3) = (4 : ℝ≥0∞) / 3 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    norm_num
  simpa only [h2, h4, h43] using h.ennrealOfReal

section Products

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def v12_driftProduct
    (A : Fin 2 → Ω → ℂ) (Q : Ω → V12Field) (j : Fin 2) (z : Ω) : V12Field :=
  A j z • Q z

noncomputable def v12_zeroOrderProduct
    (V W : Ω → ℂ) (Q : Ω → V12Field) (z : Ω) : V12Field :=
  V z • Q z + W z • v12_conjugateField (Q z)

/-- Actual A_j Q product: L4 spacetime times L4 spacetime into L2. -/
theorem v12_driftProduct_eLpNorm_le
    (μ : Measure Ω) (A : Fin 2 → Ω → ℂ) (Q : Ω → V12Field) (j : Fin 2)
    (hA : AEStronglyMeasurable (A j) μ) (hQ : AEStronglyMeasurable Q μ) :
    eLpNorm (v12_driftProduct A Q j) 2 μ ≤
      eLpNorm (A j) 4 μ * eLpNorm Q 4 μ := by
  letI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := v12_holderTriple_four_four_two
  exact eLpNorm_smul_le_mul_eLpNorm hA hQ

/-- Actual zero-order product, including the same field's conjugate. -/
theorem v12_zeroOrderProduct_eLpNorm_le
    (μ : Measure Ω) (V W : Ω → ℂ) (Q : Ω → V12Field)
    (hV : AEStronglyMeasurable V μ) (hW : AEStronglyMeasurable W μ)
    (hQ : AEStronglyMeasurable Q μ) :
    eLpNorm (v12_zeroOrderProduct V W Q) ((4 : ℝ≥0∞) / 3) μ ≤
      (eLpNorm V 2 μ + eLpNorm W 2 μ) * eLpNorm Q 4 μ := by
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) 4 ((4 : ℝ≥0∞) / 3) :=
    v12_holderTriple_two_four_fourThirds
  have hconj := v12_conjugateField_continuous.comp_aestronglyMeasurable hQ
  have hVQ : eLpNorm (fun z => V z • Q z) ((4 : ℝ≥0∞) / 3) μ ≤
      eLpNorm V 2 μ * eLpNorm Q 4 μ :=
    eLpNorm_smul_le_mul_eLpNorm hV hQ
  have hWQ : eLpNorm (fun z => W z • v12_conjugateField (Q z))
        ((4 : ℝ≥0∞) / 3) μ ≤
      eLpNorm W 2 μ * eLpNorm (fun z => v12_conjugateField (Q z)) 4 μ :=
    eLpNorm_smul_le_mul_eLpNorm hW hconj
  have hadd : eLpNorm
      ((fun z => V z • Q z) + (fun z => W z • v12_conjugateField (Q z)))
      ((4 : ℝ≥0∞) / 3) μ ≤
      eLpNorm (fun z => V z • Q z) ((4 : ℝ≥0∞) / 3) μ +
      eLpNorm (fun z => W z • v12_conjugateField (Q z)) ((4 : ℝ≥0∞) / 3) μ :=
    eLpNorm_add_le v12_one_le_fourThirds_ENNReal
  calc
    _ ≤ eLpNorm V 2 μ * eLpNorm Q 4 μ +
        eLpNorm W 2 μ * eLpNorm (fun z => v12_conjugateField (Q z)) 4 μ :=
      hadd.trans (add_le_add hVQ hWQ)
    _ = _ := by rw [v12_eLpNorm_conjugateField μ Q 4 hQ, add_mul]

theorem v12_driftProduct_memLp
    (μ : Measure Ω) (A : Fin 2 → Ω → ℂ) (Q : Ω → V12Field) (j : Fin 2)
    (hA : MemLp (A j) 4 μ) (hQ : MemLp Q 4 μ) :
    MemLp (v12_driftProduct A Q j) 2 μ := by
  have ha := hA.eLpNorm_ne_top
  have hq := hQ.eLpNorm_ne_top
  exact (v12_driftProduct_eLpNorm_le μ A Q j
    hA.aestronglyMeasurable hQ.aestronglyMeasurable).trans_lt (by finiteness)

theorem v12_zeroOrderProduct_memLp
    (μ : Measure Ω) (V W : Ω → ℂ) (Q : Ω → V12Field)
    (hV : MemLp V 2 μ) (hW : MemLp W 2 μ) (hQ : MemLp Q 4 μ) :
    MemLp (v12_zeroOrderProduct V W Q) ((4 : ℝ≥0∞) / 3) μ := by
  have hv := hV.eLpNorm_ne_top
  have hw := hW.eLpNorm_ne_top
  have hq := hQ.eLpNorm_ne_top
  exact (v12_zeroOrderProduct_eLpNorm_le μ V W Q
    hV.aestronglyMeasurable hW.aestronglyMeasurable hQ.aestronglyMeasurable).trans_lt
      (by finiteness)

end Products

#print axioms v12_conjugateField_continuous
#print axioms v12_conjugateField_norm
#print axioms v12_eLpNorm_conjugateField
#print axioms v12_holderTriple_four_four_two
#print axioms v12_holderTriple_two_four_fourThirds
#print axioms v12_driftProduct_eLpNorm_le
#print axioms v12_zeroOrderProduct_eLpNorm_le
#print axioms v12_driftProduct_memLp
#print axioms v12_zeroOrderProduct_memLp

end SMScattering.W20Full
