import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.Holder

namespace SMScattering.W20Full

open MeasureTheory FourierTransform
open scoped ENNReal

abbrev V12Spatial := EuclideanSpace ℝ (Fin 2)
abbrev V12Field := EuclideanSpace ℂ (Fin 2)
abbrev V12SpatialL2 : Type := Lp (α := V12Spatial) V12Field 2
abbrev V12SymbolLInf : Type := Lp (α := V12Spatial) ℂ ∞

/--
Multiplication by a fixed L-infinity scalar symbol is a continuous linear map
on vector-valued spatial L2.
-/
noncomputable def v12_L2Multiplier (m : V12SymbolLInf) :
    V12SpatialL2 →L[ℂ] V12SpatialL2 :=
  LinearMap.mkContinuous
    { toFun := fun f => m • f
      map_add' := fun f g => Lp.add_smul m f g
      map_smul' := by
        intro c f
        calc
          m • (c • f) = (c • m) • f := by
            symm
            exact Lp.smul_comm c m f
          _ = c • (m • f) := Lp.smul_assoc c m f }
    ‖m‖
    (fun f => Lp.norm_smul_le m f)

@[simp]
theorem v12_L2Multiplier_apply (m : V12SymbolLInf) (f : V12SpatialL2) :
    v12_L2Multiplier m f = m • f := rfl

/-- The actual L2 Fourier multiplier F^{-1} M_m F. -/
noncomputable def v12_spatialFourierMultiplier (m : V12SymbolLInf) :
    V12SpatialL2 →L[ℂ] V12SpatialL2 :=
  fourierInvCLM ℂ V12SpatialL2 ∘L
    v12_L2Multiplier m ∘L
      fourierCLM ℂ V12SpatialL2

@[simp]
theorem v12_spatialFourierMultiplier_apply
    (m : V12SymbolLInf) (f : V12SpatialL2) :
    v12_spatialFourierMultiplier m f = 𝓕⁻ (m • 𝓕 f) := rfl

theorem v12_norm_fourierInv_eq (g : V12SpatialL2) :
    ‖𝓕⁻ g‖ = ‖g‖ := by
  exact (Lp.fourierTransformₗᵢ V12Spatial V12Field).symm.norm_map g

theorem v12_spatialFourierMultiplier_bound
    (m : V12SymbolLInf) (f : V12SpatialL2) :
    ‖v12_spatialFourierMultiplier m f‖ ≤ ‖m‖ * ‖f‖ := by
  rw [v12_spatialFourierMultiplier_apply, v12_norm_fourierInv_eq]
  calc
    ‖m • 𝓕 f‖ ≤ ‖m‖ * ‖𝓕 f‖ := Lp.norm_smul_le m (𝓕 f)
    _ = ‖m‖ * ‖f‖ := by rw [Lp.norm_fourier_eq]

theorem v12_spatialFourierMultiplier_norm_le
    (m : V12SymbolLInf) :
    ‖v12_spatialFourierMultiplier m‖ ≤ ‖m‖ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg m)
    (v12_spatialFourierMultiplier_bound m)

/--
A bounded continuous scalar symbol gives an actual L-infinity equivalence
class on spatial frequency space without any finite-measure hypothesis.
-/
noncomputable def v12_symbolToLInf
    (m : V12Spatial →ᵇ ℂ) : V12SymbolLInf :=
  (BoundedContinuousFunction.memLp_top m).toLp m

theorem v12_symbolToLInf_ae
    (m : V12Spatial →ᵇ ℂ) :
    (v12_symbolToLInf m : V12Spatial → ℂ) =ᵐ[volume] m := by
  exact MemLp.coeFn_toLp (BoundedContinuousFunction.memLp_top m)

#print axioms v12_L2Multiplier
#print axioms v12_spatialFourierMultiplier
#print axioms v12_spatialFourierMultiplier_bound
#print axioms v12_spatialFourierMultiplier_norm_le
#print axioms v12_symbolToLInf_ae

end SMScattering.W20Full
