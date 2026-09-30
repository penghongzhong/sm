import lean.v12.V12_YZZNActualPDEClosure
import lean.v12.V12_YZZRSpatialConstraintClosure
import lean.v12.V12_YZZBWOriginalSpatialConstraints

/-! Exact canonical distributional conclusions for the local-closure theorem.
These definitions spell out the test identities; they are not theorem
interfaces and contain no unproved declaration. -/
set_option autoImplicit false
namespace SMScattering.W20Full
open Filter MeasureTheory
open scoped Topology ENNReal

def V12CanonicalCoulombDistributionalEquation
    (hHLS : V12ExternalHLS2D) (a b : ℝ) (q : V12Spacetime → V12Field)
    (hmq : StronglyMeasurable q) (hq4 : MemLp q 4 (v12_slab_measure a b))
    (M : ℝ) (hEq : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Icc a b),
      eLpNorm (fun x => q (t,x)) 2 volume ≤ ENNReal.ofReal M) : Prop :=
∀ j (ψ : V12Spacetime → ℂ),
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
        -Complex.I * (∫ z, q z j * fderiv ℝ ψ z v12_timeDirection ∂v12_slab_measure a b) +
          ((∫ z, q z j * fderiv ℝ (fun x => fderiv ℝ ψ x (v12_spatialDirection 0)) z (v12_spatialDirection 0) ∂v12_slab_measure a b) +
           (∫ z, q z j * fderiv ℝ (fun x => fderiv ℝ ψ x (v12_spatialDirection 1)) z (v12_spatialDirection 1) ∂v12_slab_measure a b)) =
        -(2 * Complex.I) *
          ((∫ z, (v12_actualCoulombA q 0 z * q z j) * fderiv ℝ ψ z (v12_spatialDirection 0) ∂v12_slab_measure a b) +
           (∫ z, (v12_actualCoulombA q 1 z * q z j) * fderiv ℝ ψ z (v12_spatialDirection 1) ∂v12_slab_measure a b)) +
          ∫ z, v12_actualScalarZeroOrder hHLS a b q hmq hq4 M hEq j z * ψ z
            ∂v12_slab_measure a b

def V12CanonicalSpatialDistributionalConstraints
    (a b : ℝ) (q : V12Spacetime → V12Field) : Prop :=
∀ (ψ : V12Spacetime → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Prod.fst ⁻¹' Set.Ioo a b →
      (-(∫ z, v12_actualCoulombA q 0 z * fderiv ℝ ψ z (v12_spatialDirection 0) ∂v12_slab_measure a b) -
        (∫ z, v12_actualCoulombA q 1 z * fderiv ℝ ψ z (v12_spatialDirection 1) ∂v12_slab_measure a b) = 0) ∧
      (-(∫ z, v12_actualCoulombA q 1 z * fderiv ℝ ψ z (v12_spatialDirection 0) ∂v12_slab_measure a b) +
        (∫ z, v12_actualCoulombA q 0 z * fderiv ℝ ψ z (v12_spatialDirection 1) ∂v12_slab_measure a b) =
        ∫ z, (v12_curvatureDensity (q z) : ℂ) * ψ z ∂v12_slab_measure a b) ∧
      (-(∫ z, q z 1 * fderiv ℝ ψ z (v12_spatialDirection 0) ∂v12_slab_measure a b) +
        (∫ z, q z 0 * fderiv ℝ ψ z (v12_spatialDirection 1) ∂v12_slab_measure a b) =
        Complex.I * ((∫ z, (v12_actualCoulombA q 0 z * q z 1) * ψ z ∂v12_slab_measure a b) -
          (∫ z, (v12_actualCoulombA q 1 z * q z 0) * ψ z ∂v12_slab_measure a b)))

def V12SameFieldLocalCoefficientConvergence
    (a b : ℝ) (qn : ℕ → V12Spacetime → V12Field) (q : V12Spacetime → V12Field) : Prop :=
  ∀ R,
    (∀ n, Integrable (fun z => v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z))
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))) ∧
    Tendsto (fun n => ∫ z, ‖v12_curvatureDensity (qn n z) - v12_curvatureDensity (q z)‖
      ∂((v12_slab_measure a b).restrict (v12_spatial_cylinder R))) atTop (𝓝 0) ∧
    (∀ n, MemLp (fun z => v12_spacetimeHodge (qn n) z - v12_spacetimeHodge q z)
      2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))) ∧
    Tendsto (fun n => (eLpNorm (fun z => v12_spacetimeHodge (qn n) z-v12_spacetimeHodge q z)
      2 ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0) ∧
    ∀ j, Tendsto (fun n => (eLpNorm (fun z => v12_actualCoulombA (qn n) j z • qn n z -
      v12_actualCoulombA q j z • q z) 1
      ((v12_slab_measure a b).restrict (v12_spatial_cylinder R))).toReal) atTop (𝓝 0)

end SMScattering.W20Full
