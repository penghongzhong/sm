import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib

namespace SMScattering.W20Full

open Filter
open scoped Topology

/--
A common continuity modulus gives the exact equicontinuity hypothesis needed
by Arzela--Ascoli.  This is Mathlib's metric equicontinuity theorem specialized
to a sequence.
-/
theorem v12_equicontinuous_of_common_modulus
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (ω : ℝ → ℝ)
    (hω : Tendsto ω (𝓝 0) (𝓝 0))
    (hmod : ∀ x y n, dist (F n x) (F n y) ≤ ω (dist x y)) :
    Equicontinuous F := by
  exact Metric.equicontinuous_of_continuity_modulus ω hω F hmod

/--
A linear modulus is the special case used for the fixed-frequency spatial
Lipschitz estimate.
-/
theorem v12_equicontinuous_of_uniform_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℕ → X → Y) (C : ℝ)
    (hmod : ∀ x y n, dist (F n x) (F n y) ≤ C * dist x y) :
    Equicontinuous F := by
  apply v12_equicontinuous_of_common_modulus F (fun r => C * r)
  · simpa using (tendsto_const_nhds.mul tendsto_id)
  · exact hmod

/--
Two manuscript estimates may be combined before invoking Ascoli:
one term controls spatial motion and one controls time motion.  The theorem is
stated with an already assembled scalar modulus because the product-domain
metric realization is handled by the concrete representative map.
-/
theorem v12_equicontinuous_of_space_time_modulus
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (F : ℕ → X → Y)
    (ωspace ωtime : ℝ → ℝ)
    (hspace : Tendsto ωspace (𝓝 0) (𝓝 0))
    (htime : Tendsto ωtime (𝓝 0) (𝓝 0))
    (hmod : ∀ x y n,
      dist (F n x) (F n y)
        ≤ ωspace (dist x y) + ωtime (dist x y)) :
    Equicontinuous F := by
  apply v12_equicontinuous_of_common_modulus F
    (fun r => ωspace r + ωtime r)
  · simpa using hspace.add htime
  · exact hmod

#print axioms v12_equicontinuous_of_common_modulus
#print axioms v12_equicontinuous_of_uniform_lipschitz
#print axioms v12_equicontinuous_of_space_time_modulus

end SMScattering.W20Full
