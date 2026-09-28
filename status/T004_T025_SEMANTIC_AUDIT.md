# T004–T025 semantic coverage audit

Verification authority: synchronized 133-page W20 manuscript.

This audit distinguishes a compiling scalar/algebraic spine from full paper-node coverage.  A theorem is not promoted merely because its final scalar absorption compiles.

## Classification

| Node | Paper node | Current Lean role | Coverage classification |
|---|---|---|---|
| T004 | v13:lem:lowA | derives low-potential smallness from T001 + LP order -1 kernel + dyadic decay | **STANDARD-INPUT BACKED / acceptable after exact LP interface registration** |
| T005 | v13:prop:mag-bilin | derives paper product estimate from source-audited Smith Cor. 5.7 + Smith adapted product spaces | **SOURCE-AUDIT BACKED** |
| T006 | v13:lem:HodgeH | scalar closure after Riesz/Hölder reductions | **STANDARD-ANALYSIS BRIDGE**; generic Riesz/Hölder interfaces must remain explicit |
| T007 | v13:prop:HHL | aggregates GG/null-form and transverse-Hodge estimates supplied as `hGG,hTor,hDGG,hDTor` | **INTERNAL ANALYTIC BRIDGE PENDING** |
| T008 | v13:lem:Hk | aggregates first-order magnetic, cubic, and `|A|^2` forcing estimates supplied as parameters | **INTERNAL ANALYTIC BRIDGE PENDING** |
| T009 | v13:lem:Mnd | exact dyadic exponent cancellation + composition of Smith/T005 bounds | **KERNEL / connector** |
| T010 | v13:def:envelopes | definitions | **DEFINITION CLOSED** |
| T011 | v13:lem:beta | finite-truncation causal-envelope recursion, exponential budget, monotonicity, slow bounds | **KERNEL SUBSTANTIALLY FORMALIZED**; generic slow-envelope l2 Young remains standard |
| T012 | v13:thm:single | bootstrap algebra from T005/T007/T008/T009/T011 outputs | **CONNECTOR; blocked by T007/T008 analytic bridges** |
| T013 | v13:thm:linear | scalar Young/absorption closure | **CONNECTOR**; upstream forcing estimate must be separately certified |
| T014 | v13:lem:relative-causal | only squares the paper's Bony/Cauchy--Schwarz estimate `hell` | **INTERNAL BONEY BRIDGE PENDING** |
| T015 | v13:lem:weak-firstgen | finite-angular duality + half-space mass aggregation | **STANDARD-ANALYSIS BACKED** |
| T016 | v13:def:WMB | definition/record | **DEFINITION CLOSED** |
| T017 | v14:def:Djoint | exact algebraic interface definition | **DEFINITION CLOSED** |
| T018 | v14:lem:tensor-contract | combines low/high contraction estimates supplied separately | **MULTIPLIER BRIDGE PENDING** |
| T019 | v14:lem:weak-generations | finite-generation induction from T018 | **KERNEL / connector** |
| T020 | v14:thm:weak-Smith | scalar absorption of `K <= C(1+theta K)` | **INTERNAL WEAK-SMITH BOOTSTRAP BRIDGE PENDING** |
| T021 | v14:thm:WMB-close | exact square-root opening of T020 output | **KERNEL / connector** |
| T022 | v13:lem:weak-linear | exact scalar Young absorption | **KERNEL / connector** |
| T023 | v13:lem:relative-WMB | final scalar closure from a Bony/WMB recurrence supplied as `hmid` | **INTERNAL BONEY/WMB BRIDGE PENDING** |
| T024 | v13:lem:causal-linear | final aggregation of near/far slow-envelope convolution bounds | **SEQUENCE-CONVOLUTION BRIDGE PENDING** |
| T025 | v13:lem:Volterra | discrete Gronwall/Volterra argument carried out in Lean | **KERNEL SUBSTANTIALLY FORMALIZED** |

## Earliest unresolved internal cut-set

The first unresolved internal edges in logical order are:

1. **T007-GG**: high-high-to-low Jacobian/null-form multiplier estimate.
2. **T007-Tor**: terms with at least one transverse Hodge factor.
3. **T008**: strong-forcing three-class estimates.
4. **T014**: relative-causal Bony-ordering estimate.
5. **T018**: derived tensor multiplier contractions.
6. **T020**: weak-Smith bootstrap estimate before scalar absorption.
7. **T023**: relative-WMB Bony recurrence.
8. **T024**: near/far slow-envelope convolution bounds.

T012/T013/T019/T021/T022 are not independent red points once their upstream estimates are certified.

## T007 finite-algebra repair

Public file `lean/v13/T007_HHLNullKernel.lean` now formalizes:

- `eta wedge xi = eta wedge (xi-eta)`;
- the polarized Jacobian difference identity;
- the final `Z_*^2 <= Z_*` weakening for `0 <= Z_* <= 1`.

Therefore T007's remaining burden is purely the standard harmonic-analysis realization of these symbols and sequence bounds, not hidden algebra.
