import lean.v12.V12_YZZEComponentTestLimits
import lean.v12.V12_YZZLScalarDriftTest
import lean.v12.V12_YZZOCompactFirstOrderConstraints
import lean.v12.V12_YZZPCurvatureTestLimits
import lean.v12.V12_YZZQActualConnectionTests

/-! Original torsion/divergence/curl equations are integrated by parts and
passed to the same-Q limit. All A/B/AQ test limits come from actual Hodge
and quadratic application proofs, not internal conclusion hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_spatial_constraints_distributional_closure
    (hHLS : V12ExternalHLS2D) (a b : ℝ)
    (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field)
    (hmn : ∀ n, StronglyMeasurable (qn n)) (hmq : StronglyMeasurable q)
    (hn4 : ∀ n, MemLp (qn n) 4 (v12_slab_measure a b))
    (hn2 : ∀ R n, MemLp (qn n) 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hq2 : ∀ R, MemLp q 2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R)))
    (hlim : ∀ R, Tendsto (fun n => (eLpNorm (fun z => qn n z-q z) 2
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0))
    (M : ℝ) (hM : 0 ≤ M)
    (hEn : ∀ n, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => qn n (t,x)) 2 volume ≤ ENNReal.ofReal M)
    (Z : ℝ≥0∞) (hZ : Z ≠ ∞) (hb : ∀ n, eLpNorm (qn n) 4 (v12_slab_measure a b) ≤ Z)
    (e₀ e₁ : V12Spacetime)
    (hqSmooth : ∀ n j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => qn n z j) (Prod.fst ⁻¹' Set.Ioo a b))
    (hASmooth : ∀ n k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (v12_actualCoulombA (qn n) k) (Prod.fst ⁻¹' Set.Ioo a b))
    (hdiv : ∀ n z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (v12_actualCoulombA (qn n) 0) z e₀ +
      fderiv ℝ (v12_actualCoulombA (qn n) 1) z e₁ = 0)
    (hcurl : ∀ n z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (v12_actualCoulombA (qn n) 1) z e₀ -
      fderiv ℝ (v12_actualCoulombA (qn n) 0) z e₁ = (v12_curvatureDensity (qn n z) : ℂ))
    (htorsion : ∀ n z, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
      fderiv ℝ (fun x => qn n x 1) z e₀ - fderiv ℝ (fun x => qn n x 0) z e₁ =
      Complex.I * (v12_actualCoulombA (qn n) 0 z * qn n z 1 -
        v12_actualCoulombA (qn n) 1 z * qn n z 0)) :
    ∀ (ψ : V12Spacetime → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (-(∫ z, v12_actualCoulombA q 0 z * fderiv ℝ ψ z e₀ ∂v12_slab_measure a b) -
        (∫ z, v12_actualCoulombA q 1 z * fderiv ℝ ψ z e₁ ∂v12_slab_measure a b) = 0) ∧
      (-(∫ z, v12_actualCoulombA q 1 z * fderiv ℝ ψ z e₀ ∂v12_slab_measure a b) +
        (∫ z, v12_actualCoulombA q 0 z * fderiv ℝ ψ z e₁ ∂v12_slab_measure a b) =
        ∫ z, (v12_curvatureDensity (q z) : ℂ) * ψ z ∂v12_slab_measure a b) ∧
      (-(∫ z, q z 1 * fderiv ℝ ψ z e₀ ∂v12_slab_measure a b) +
        (∫ z, q z 0 * fderiv ℝ ψ z e₁ ∂v12_slab_measure a b) =
        Complex.I * ((∫ z, (v12_actualCoulombA q 0 z * q z 1) * ψ z ∂v12_slab_measure a b) -
          (∫ z, (v12_actualCoulombA q 1 z * q z 0) * ψ z ∂v12_slab_measure a b))) := by
  intro ψ hψ hc hs
  let μ := v12_slab_measure a b
  have hA (j : Fin 2) (v : V12Spacetime) := v12_actual_connection_compact_derivative_limit
    hHLS a b qn q hmn hmq hn4 hn2 hq2 hlim M hM hEn Z hZ hb j ψ hψ hc v
  have hB := v12_actual_curvature_compact_test_limit a b qn q hn2 hq2 hlim ψ hc hψ.continuous
  have hD (k j : Fin 2) := v12_actual_scalar_drift_compact_limit hHLS a b qn q hmn hmq
    hn4 hn2 hq2 hlim M hM hEn Z hZ hb k j ψ hψ.continuous hc
  have hnC (j : Fin 2) (R n : ℕ) : MemLp (fun z => qn n z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 (qn n) (hn2 R n).aestronglyMeasurable j).trans_lt (hn2 R n)
  have hqC (j : Fin 2) (R : ℕ) : MemLp (fun z => q z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 q (hq2 R).aestronglyMeasurable j).trans_lt (hq2 R)
  have hQ (j : Fin 2) (v : V12Spacetime) : Tendsto (fun n => ∫ z,
      qn n z j * fderiv ℝ ψ z v ∂μ) atTop (𝓝 (∫ z, q z j * fderiv ℝ ψ z v ∂μ)) := by
    have h := v12_raw_local_L2_derivative_test_limit a b (fun n z => qn n z j) (fun z => q z j)
      (hnC j) (hqC j) (fun R => v12_raw_component_L2_limit _ qn q (hn2 R) (hq2 R) (hlim R) j)
      ψ hψ hc v
    simpa only [smul_eq_mul, mul_comm] using h
  have hdivI (n : ℕ) :
      -(∫ z, v12_actualCoulombA (qn n) 0 z * fderiv ℝ ψ z e₀ ∂μ) -
        (∫ z, v12_actualCoulombA (qn n) 1 z * fderiv ℝ ψ z e₁ ∂μ) = 0 := by
    have hraw : ∀ᵐ z ∂μ, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
        fderiv ℝ (v12_actualCoulombA (qn n) 0) z e₀ +
        (1 : ℂ) * fderiv ℝ (v12_actualCoulombA (qn n) 1) z e₁ = (fun _ => (0 : ℂ)) z :=
      Filter.Eventually.of_forall (fun z hz => by simpa only [one_mul] using hdiv n z hz)
    have h := (v12_original_first_order_compact_constraint a b
      (v12_actualCoulombA (qn n) 0) (v12_actualCoulombA (qn n) 1) (fun _ => 0) ψ 1 e₀ e₁
      (hASmooth n 0) (hASmooth n 1) hψ hc hs hraw).2
    simpa only [one_mul, zero_mul, integral_zero] using h
  have hcurlI (n : ℕ) :
      -(∫ z, v12_actualCoulombA (qn n) 1 z * fderiv ℝ ψ z e₀ ∂μ) +
        (∫ z, v12_actualCoulombA (qn n) 0 z * fderiv ℝ ψ z e₁ ∂μ) =
        ∫ z, (v12_curvatureDensity (qn n z) : ℂ) * ψ z ∂μ := by
    have hraw : ∀ᵐ z ∂μ, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
        fderiv ℝ (v12_actualCoulombA (qn n) 1) z e₀ +
        (-1 : ℂ) * fderiv ℝ (v12_actualCoulombA (qn n) 0) z e₁ = (v12_curvatureDensity (qn n z) : ℂ) :=
      Filter.Eventually.of_forall (fun z hz => by
        simpa only [neg_one_mul, sub_eq_add_neg] using hcurl n z hz)
    have h := (v12_original_first_order_compact_constraint a b
      (v12_actualCoulombA (qn n) 1) (v12_actualCoulombA (qn n) 0)
      (fun z => (v12_curvatureDensity (qn n z) : ℂ)) ψ (-1) e₀ e₁
      (hASmooth n 1) (hASmooth n 0) hψ hc hs hraw).2
    simpa only [neg_one_mul, sub_neg_eq_add] using h
  obtain ⟨C, hC, hMZ⟩ := v12_actualCoulomb_drift_MZZ hHLS
  have hDriftInt (n : ℕ) (k j : Fin 2) :
      Integrable (fun z => (v12_actualCoulombA (qn n) k z * qn n z j) * ψ z) μ := by
    have hVec := (hMZ a b (qn n) (hmn n) (hn4 n) (ENNReal.ofReal M) (by finiteness) (hEn n) k).1
    have hScalar : MemLp (fun z => v12_actualCoulombA (qn n) k z * qn n z j) 2 μ := by
      have h : MemLp (fun z => v12_driftProduct (v12_actualCoulombA (qn n)) (qn n) k z j) 2 μ :=
        (v12_raw_component_eLpNorm_le μ 2
        (v12_driftProduct (v12_actualCoulombA (qn n)) (qn n) k) hVec.aestronglyMeasurable j).trans_lt hVec
      simpa only [v12_driftProduct, PiLp.smul_apply, smul_eq_mul] using h
    have h := (hScalar.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hψ.continuous hc
    simpa only [smul_eq_mul] using h
  have htorI (n : ℕ) :
      -(∫ z, qn n z 1 * fderiv ℝ ψ z e₀ ∂μ) + (∫ z, qn n z 0 * fderiv ℝ ψ z e₁ ∂μ) =
        Complex.I * ((∫ z, (v12_actualCoulombA (qn n) 0 z * qn n z 1) * ψ z ∂μ) -
          (∫ z, (v12_actualCoulombA (qn n) 1 z * qn n z 0) * ψ z ∂μ)) := by
    let r := fun z => Complex.I * (v12_actualCoulombA (qn n) 0 z * qn n z 1 -
      v12_actualCoulombA (qn n) 1 z * qn n z 0)
    have hraw : ∀ᵐ z ∂μ, z ∈ Prod.fst ⁻¹' Set.Ioo a b →
        fderiv ℝ (fun x => qn n x 1) z e₀ + (-1 : ℂ) * fderiv ℝ (fun x => qn n x 0) z e₁ = r z :=
      Filter.Eventually.of_forall (fun z hz => by
        simpa only [r, neg_one_mul, sub_eq_add_neg] using htorsion n z hz)
    have h := (v12_original_first_order_compact_constraint a b
      (fun z => qn n z 1) (fun z => qn n z 0) r ψ (-1) e₀ e₁
      (hqSmooth n 1) (hqSmooth n 0) hψ hc hs hraw).2
    simp only [neg_one_mul, sub_neg_eq_add] at h
    have he : (∫ z, r z * ψ z ∂μ) =
        Complex.I * ((∫ z, (v12_actualCoulombA (qn n) 0 z * qn n z 1) * ψ z ∂μ) -
          (∫ z, (v12_actualCoulombA (qn n) 1 z * qn n z 0) * ψ z ∂μ)) := by
      simp only [r, mul_assoc, sub_mul]
      have hsplit := integral_sub (hDriftInt n 0 1) (hDriftInt n 1 0)
      simp only [mul_assoc] at hsplit
      rw [integral_const_mul, hsplit]
    exact h.trans he
  have hdivL := ((hA 0 e₀).neg).sub (hA 1 e₁)
  rw [funext hdivI] at hdivL
  have hdivOut := tendsto_nhds_unique hdivL tendsto_const_nhds
  have hcurlL := ((hA 1 e₀).neg).add (hA 0 e₁)
  rw [funext hcurlI] at hcurlL
  have hcurlOut := tendsto_nhds_unique hcurlL hB
  have htorL := ((hQ 1 e₀).neg).add (hQ 0 e₁)
  rw [funext htorI] at htorL
  have htorOut := tendsto_nhds_unique htorL (((hD 0 1).sub (hD 1 0)).const_mul Complex.I)
  exact ⟨hdivOut, hcurlOut, htorOut⟩

#print axioms v12_actual_spatial_constraints_distributional_closure
end SMScattering.W20Full
