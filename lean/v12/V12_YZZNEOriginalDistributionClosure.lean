import lean.v12.V12_YZZGROriginalDistributionTests
import lean.v12.V12_YZZKActualCompactPDE
import lean.v12.V12_YZZLScalarDriftTest

/-! Same-field original PDE closure. The original advective distributional PDE (not its derived divergence
identity),
distributional Coulomb divergence and local smoothness of Q are the inputs.
No joint connection smoothness or local-integrability input is imposed; the
latter is derived from the actual same-Q Hodge MZ budget. No derived integral identity, coefficient weak limit, source convergence
or limit budget is assumed. The separate torsion/curl obligations still belong to full7.1. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

theorem v12_actual_Coulomb_PDE_closure_original_distribution
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
    (vt e₀ e₁ : V12Spacetime)
    (hqSmooth : ∀ n j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => qn n z j) (Prod.fst ⁻¹' Set.Ioo a b))
    (hdiv : ∀ n (φ : V12Spacetime → ℂ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (∫ z, v12_actualCoulombA (qn n) 0 z * fderiv ℝ φ z e₀ ∂v12_slab_measure a b) +
      (∫ z, v12_actualCoulombA (qn n) 1 z * fderiv ℝ φ z e₁ ∂v12_slab_measure a b) = 0)
    (hPDE : ∀ n j, V12OriginalScalarDistributionalPDE a b (fun z => qn n z j)
      (v12_actualCoulombA (qn n))
      (v12_actualScalarZeroOrder hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n) j)
      vt e₀ e₁) :
    ∃ (hq4 : MemLp q 4 (v12_slab_measure a b))
      (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M),
      ∀ j (ψ : V12Spacetime → ℂ),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
        -Complex.I * (∫ z, q z j * fderiv ℝ ψ z vt ∂v12_slab_measure a b) +
          ((∫ z, q z j * fderiv ℝ (fun x => fderiv ℝ ψ x e₀) z e₀ ∂v12_slab_measure a b) +
           (∫ z, q z j * fderiv ℝ (fun x => fderiv ℝ ψ x e₁) z e₁ ∂v12_slab_measure a b)) =
        -(2 * Complex.I) *
          ((∫ z, (v12_actualCoulombA q 0 z * q z j) * fderiv ℝ ψ z e₀ ∂v12_slab_measure a b) +
           (∫ z, (v12_actualCoulombA q 1 z * q z j) * fderiv ℝ ψ z e₁ ∂v12_slab_measure a b)) +
          ∫ z, v12_actualScalarZeroOrder hHLS a b q hmq hq4 M hEq j z * ψ z
            ∂v12_slab_measure a b := by
  let μ := v12_slab_measure a b
  have hq4 : MemLp q 4 μ :=
    (v12_global_budget_inherited_from_local_L2 a b qn q hmq hn2 hq2 hlim 4 Z hb).trans_lt
      (lt_top_iff_ne_top.mpr hZ)
  have hEq := v12_global_energy_inherited a b qn q hmq hn2 hq2 hlim
    (ENNReal.ofReal M) (by finiteness) hEn
  refine ⟨hq4, hEq, ?_⟩
  intro j ψ hψ hc hs
  have hnC (R n : ℕ) : MemLp (fun z => qn n z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 (qn n) (hn2 R n).aestronglyMeasurable j).trans_lt (hn2 R n)
  have hqC (R : ℕ) : MemLp (fun z => q z j) 2 (μ.restrict (v12_spatial_cylinder R)) :=
    (v12_raw_component_eLpNorm_le _ 2 q (hq2 R).aestronglyMeasurable j).trans_lt (hq2 R)
  have hC (R : ℕ) := v12_raw_component_L2_limit _ qn q (hn2 R) (hq2 R) (hlim R) j
  have hdt := v12_raw_local_L2_derivative_test_limit a b (fun n z => qn n z j)
    (fun z => q z j) hnC hqC hC ψ hψ hc vt
  have hdd (v : V12Spacetime) := v12_raw_local_L2_second_derivative_test_limit a b
    (fun n z => qn n z j) (fun z => q z j) hnC hqC hC ψ hψ hc v v
  have hdt' : Tendsto (fun n => ∫ z, qn n z j * fderiv ℝ ψ z vt ∂μ) atTop
      (𝓝 (∫ z, q z j * fderiv ℝ ψ z vt ∂μ)) := by
    simpa only [smul_eq_mul, mul_comm] using hdt
  have hdd' (v : V12Spacetime) : Tendsto (fun n => ∫ z,
      qn n z j * fderiv ℝ (fun x => fderiv ℝ ψ x v) z v ∂μ) atTop
      (𝓝 (∫ z, q z j * fderiv ℝ (fun x => fderiv ℝ ψ x v) z v ∂μ)) := by
    simpa only [smul_eq_mul, mul_comm] using hdd v
  have hF (k : Fin 2) (v : V12Spacetime) := v12_actual_scalar_drift_derivative_limit
    hHLS a b qn q hmn hmq hn4 hn2 hq2 hlim M hM hEn Z hZ hb k j ψ hψ hc v
  obtain ⟨h4', hE', hG⟩ := v12_actual_zero_order_compact_limits hHLS a b qn q hmn hmq
    hn4 hn2 hq2 hlim M hM hEn Z hZ hb j ψ hc hψ.continuous
  have heG (r : V12Spacetime → V12Field) (hr : StronglyMeasurable r) (hr4 : MemLp r 4 μ)
      (hE : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
        eLpNorm (fun x => r (t,x)) 2 volume ≤ ENNReal.ofReal M) :
      (∫ z, v12_actualScalarZeroOrder hHLS a b r hr hr4 M hE j z * ψ z ∂μ) =
        ∫ z, (v12_actualPotentialL2Class hHLS a b r hr hr4 M hE z * (ψ z * r z j) +
          v12_WDensity (r z) * (ψ z * star (r z j))) ∂μ := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    unfold v12_actualScalarZeroOrder
    ring
  have heGn (n : ℕ) := heG (qn n) (hmn n) (hn4 n) (hEn n)
  have heGq := heG q hmq hq4 hEq
  have hG' : Tendsto (fun n => ∫ z,
      v12_actualScalarZeroOrder hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n) j z * ψ z ∂μ)
      atTop (𝓝 (∫ z, v12_actualScalarZeroOrder hHLS a b q hmq hq4 M hEq j z * ψ z ∂μ)) := by
    simpa only [heGn, heGq] using hG
  have hleft := (hdt'.const_mul (-Complex.I)).add ((hdd' e₀).add (hdd' e₁))
  have hright := (((hF 0 e₀).add (hF 1 e₁)).const_mul (-(2*Complex.I))).add hG'
  obtain ⟨CA, hCA, hAB⟩ := v12_actual_hodge_spacetime_MZ hHLS
  have hALoc (n : ℕ) (k : Fin 2) : LocallyIntegrable (v12_actualCoulombA (qn n) k) μ := by
    have hA4 : MemLp (v12_actualCoulombA (qn n) k) 4 μ :=
      (v12_actualCoulombA_eLpNorm_le μ (qn n) (hmn n) 4 k).trans_lt
        (hAB a b (qn n) (hmn n) (hn4 n) (ENNReal.ofReal M) (by finiteness) (hEn n)).1
    exact hA4.locallyIntegrable (by norm_num)
  have hident (n : ℕ) := v12_compact_PDE_from_original_distribution a b
    (fun z => qn n z j) (v12_actualCoulombA (qn n))
    (v12_actualScalarZeroOrder hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n) j)
    ψ vt e₀ e₁ (hqSmooth n j) (hALoc n)
    (v12_actualScalarZeroOrder_memLp hHLS a b (qn n) (hmn n) (hn4 n) M (hEn n) j)
    hψ hc hs (hdiv n) (hPDE n j)
  have hsame := funext hident
  rw [hsame] at hleft
  exact tendsto_nhds_unique hleft hright

#print axioms v12_actual_Coulomb_PDE_closure_original_distribution
end SMScattering.W20Full
