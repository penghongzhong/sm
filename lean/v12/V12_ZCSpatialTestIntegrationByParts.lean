import lean.v12.V12_XCompactTestTimeDerivative
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
Spatial integration by parts for compact tests against smooth raw fields.
The raw field is not assumed Schwartz or spatially integrable. All products
used by Mathlib's integration-by-parts theorem are proved integrable using
the compact support of the test and its derivatives.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SMScattering.W20Full

open MeasureTheory
open scoped ContDiff

theorem v12_compact_test_spatial_ibp
    (ψ : V12Spatial → ℂ) (Q : V12Spatial → V12Field)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (v : V12Spatial) :
    (∫ y : V12Spatial, ψ y • fderiv ℝ Q y v) =
      -(∫ y : V12Spatial, fderiv ℝ ψ y v • Q y) := by
  have hDψ : Continuous (fun y => fderiv ℝ ψ y v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDQ : Continuous (fun y => fderiv ℝ Q y v) :=
    (hQ.continuous_fderiv (by simp)).clm_apply continuous_const
  apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
  · exact (hDψ.smul hQ.continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).smul_right
  · exact (hψ.continuous.smul hDQ).integrable_of_hasCompactSupport hc.smul_right
  · exact (hψ.continuous.smul hQ.continuous).integrable_of_hasCompactSupport
      hc.smul_right
  · intro y _
    exact hψ.differentiable (by simp) y
  · intro y _
    exact hQ.differentiable (by simp) y

theorem v12_compact_test_spatial_ibp_twice
    (ψ : V12Spatial → ℂ) (Q : V12Spatial → V12Field)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (v : V12Spatial) :
    (∫ y : V12Spatial, ψ y • fderiv ℝ (fun z => fderiv ℝ Q z v) y v) =
      ∫ y : V12Spatial, fderiv ℝ (fun z => fderiv ℝ ψ z v) y v • Q y := by
  have hDψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => fderiv ℝ Q y v) :=
    (hQ.fderiv_right (by simp)).clm_apply contDiff_const
  rw [v12_compact_test_spatial_ibp ψ _ hψ hc hDQ v,
    v12_compact_test_spatial_ibp _ Q hDψ (hc.fderiv_apply ℝ v) hQ v,
    neg_neg]

/-- The first-order identity for the same cutoff/reflected-kernel test. -/
theorem v12_actual_compact_test_spatial_ibp
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x v : V12Spatial)
    (Q : V12Spatial → V12Field)
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q) :
    (∫ y : V12Spatial, v12_compactSpatialTest χ k R x y • fderiv ℝ Q y v) =
      -(∫ y : V12Spatial, fderiv ℝ (v12_compactSpatialTest χ k R x) y v • Q y) :=
  v12_compact_test_spatial_ibp _ Q
    (v12_compactSpatialTest_smooth χ hs k R x)
    (v12_compactSpatialTest_compactSupport χ hc k R x) hQ v

/-- The second-order identity for that same test, with both signs proved. -/
theorem v12_actual_compact_test_spatial_ibp_twice
    (χ : V12Spatial → ℝ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (k : SchwartzMap V12Spatial ℂ) (R : ℕ) (x v : V12Spatial)
    (Q : V12Spatial → V12Field)
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q) :
    (∫ y : V12Spatial, v12_compactSpatialTest χ k R x y •
      fderiv ℝ (fun z => fderiv ℝ Q z v) y v) =
      ∫ y : V12Spatial,
        fderiv ℝ (fun z => fderiv ℝ (v12_compactSpatialTest χ k R x) z v) y v • Q y :=
  v12_compact_test_spatial_ibp_twice _ Q
    (v12_compactSpatialTest_smooth χ hs k R x)
    (v12_compactSpatialTest_compactSupport χ hc k R x) hQ v

/-- Testing the smooth divergence-form PDE gives the actual spatial source.
The only equation input is the pointwise PDE for the raw fields. -/
theorem v12_compact_test_raw_pde_source
    (ψ : V12Spatial → ℂ) (hc : HasCompactSupport ψ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (Q DQ G : V12Spatial → V12Field) (F : Fin 2 → V12Spatial → V12Field)
    (hQ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hF : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F j))
    (hG : Continuous G)
    (hPDE : ∀ y, DQ y =
      Complex.I • (fderiv ℝ (fun z => fderiv ℝ Q z
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)) y (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        fderiv ℝ (fun z => fderiv ℝ Q z
        (EuclideanSpace.basisFun (Fin 2) ℝ 1)) y (EuclideanSpace.basisFun (Fin 2) ℝ 1)) +
      (2 : ℂ) • fderiv ℝ (F 0) y (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
      (2 : ℂ) • fderiv ℝ (F 1) y (EuclideanSpace.basisFun (Fin 2) ℝ 1) +
      (-Complex.I) • G y) :
    let e := EuclideanSpace.basisFun (Fin 2) ℝ
    (∫ y : V12Spatial, ψ y • DQ y) =
      Complex.I • ((∫ y : V12Spatial,
        fderiv ℝ (fun z => fderiv ℝ ψ z (e 0)) y (e 0) • Q y) +
        (∫ y : V12Spatial,
        fderiv ℝ (fun z => fderiv ℝ ψ z (e 1)) y (e 1) • Q y)) +
      (-2 : ℂ) • (∫ y : V12Spatial, fderiv ℝ ψ y (e 0) • F 0 y) +
      (-2 : ℂ) • (∫ y : V12Spatial, fderiv ℝ ψ y (e 1) • F 1 y) +
      (-Complex.I) • (∫ y : V12Spatial, ψ y • G y) := by
  dsimp only
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let D2 : Fin 2 → V12Spatial → V12Field := fun j y =>
    fderiv ℝ (fun z => fderiv ℝ Q z (e j)) y (e j)
  have hD2 : ∀ j, Continuous (D2 j) := by
    intro j
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => fderiv ℝ Q z (e j)) :=
      (hQ.fderiv_right (by simp)).clm_apply contDiff_const
    exact (hD.continuous_fderiv (by simp)).clm_apply continuous_const
  have hiD : ∀ j, Integrable (fun y => ψ y • D2 j y) := fun j =>
    (hψ.continuous.smul (hD2 j)).integrable_of_hasCompactSupport hc.smul_right
  have hiF : ∀ j, Integrable (fun y => ψ y • fderiv ℝ (F j) y (e j)) := by
    intro j
    exact (hψ.continuous.smul
      (((hF j).continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
        hc.smul_right
  have hiG : Integrable (fun y => ψ y • G y) :=
    (hψ.continuous.smul hG).integrable_of_hasCompactSupport hc.smul_right
  have hexpand : (fun y => ψ y • DQ y) = fun y =>
      Complex.I • (ψ y • D2 0 y + ψ y • D2 1 y) +
      (2 : ℂ) • (ψ y • fderiv ℝ (F 0) y (e 0)) +
      (2 : ℂ) • (ψ y • fderiv ℝ (F 1) y (e 1)) +
      (-Complex.I) • (ψ y • G y) := by
    funext y
    rw [hPDE]
    simp only [smul_add, smul_comm (ψ y), D2, e]
  let A : V12Spatial → V12Field := fun y => Complex.I • (ψ y • D2 0 y + ψ y • D2 1 y)
  let B : V12Spatial → V12Field := fun y => (2 : ℂ) • (ψ y • fderiv ℝ (F 0) y (e 0))
  let C : V12Spatial → V12Field := fun y => (2 : ℂ) • (ψ y • fderiv ℝ (F 1) y (e 1))
  let D : V12Spatial → V12Field := fun y => (-Complex.I) • (ψ y • G y)
  have hA : Integrable A := ((hiD 0).add (hiD 1)).smul Complex.I
  have hB : Integrable B := (hiF 0).smul (2 : ℂ)
  have hC : Integrable C := (hiF 1).smul (2 : ℂ)
  have hD : Integrable D := hiG.smul (-Complex.I)
  rw [hexpand]
  change (∫ y : V12Spatial, A y + B y + C y + D y) = _
  rw [integral_add (f := fun y => A y + B y + C y) (g := D) ((hA.add hB).add hC) hD,
    integral_add (f := fun y => A y + B y) (g := C) (hA.add hB) hC,
    integral_add (f := A) (g := B) hA hB]
  dsimp only [A, B, C, D]
  simp only [integral_smul, integral_add (hiD 0) (hiD 1)]
  dsimp only [D2]
  rw [v12_compact_test_spatial_ibp_twice ψ Q hψ hc hQ (e 0),
    v12_compact_test_spatial_ibp_twice ψ Q hψ hc hQ (e 1),
    v12_compact_test_spatial_ibp ψ (F 0) hψ hc (hF 0) (e 0),
    v12_compact_test_spatial_ibp ψ (F 1) hψ hc (hF 1) (e 1)]
  simp only [smul_neg, neg_smul]

#print axioms v12_compact_test_raw_pde_source
#print axioms v12_compact_test_spatial_ibp
#print axioms v12_compact_test_spatial_ibp_twice
#print axioms v12_actual_compact_test_spatial_ibp
#print axioms v12_actual_compact_test_spatial_ibp_twice

end SMScattering.W20Full
