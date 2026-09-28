import Mathlib.Tactic

/-!
W20 full-master dependency assemblies for the v13-v14 cut-set corollaries.

The analytic estimates themselves live in the N001-N033 migration batch and
its source-audited kernels. These declarations certify only the exact logical
composition used by the corollaries; no PDE estimate is postulated here.

No sorry/admit/custom axiom.
-/

namespace SMScattering.W20Full

theorem v14_stability_unconditional_dependency
    (WMB ShortStability LongStability : Prop)
    (hWMB : WMB)
    (hShort : WMB → ShortStability)
    (hLong : WMB → LongStability) :
    ShortStability ∧ LongStability :=
  ⟨hShort hWMB, hLong hWMB⟩

theorem v13_front_dependency_pack
    (Single RelativeCausal WeakFirstGen : Prop)
    (hSingle : Single)
    (hRelative : RelativeCausal)
    (hWeak : WeakFirstGen) :
    Single ∧ RelativeCausal ∧ WeakFirstGen :=
  ⟨hSingle, hRelative, hWeak⟩

theorem v14_cutset_dependency_pack
    (Single ShortStability LongStability WMBClosed : Prop)
    (hSingle : Single)
    (hShort : ShortStability)
    (hLong : LongStability)
    (hWMB : WMBClosed) :
    Single ∧ ShortStability ∧ LongStability ∧ WMBClosed :=
  ⟨hSingle, hShort, hLong, hWMB⟩

#print axioms v14_stability_unconditional_dependency
#print axioms v13_front_dependency_pack
#print axioms v14_cutset_dependency_pack

end SMScattering.W20Full
