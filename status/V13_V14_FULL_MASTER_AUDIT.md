# W20 v13-v14 full-master audit

Authority: synchronized 133-page W20 manuscript.

## v13 exact proof-bearing inventory — 19 nodes

The W20 v13 nodes map to the compiled migration/source-audit spine as follows:

| Node | Public verification node |
|---|---|
| `v13:prop:Smith-inputs` | T003 source whitelist |
| `v13:lem:lowA` | T004 |
| `v13:prop:mag-bilin` | T005 |
| `v13:lem:HodgeH` | T006 |
| `v13:prop:HHL` | T007 + HHL null-form kernel/source audit |
| `v13:lem:Hk` | T008 source reduction |
| `v13:lem:Mnd` | T009 |
| `v13:lem:beta` | T011 finite causal-envelope construction |
| `v13:thm:single` | T012 |
| `v13:thm:linear` | T013 |
| `v13:lem:relative-causal` | T014 |
| `v13:lem:weak-firstgen` | T015 |
| `v13:lem:weak-linear` | T022 |
| `v13:lem:relative-WMB` | T023 |
| `v13:lem:causal-linear` | T024 |
| `v13:lem:Volterra` | T025 |
| `v13:thm:short-stability` | T026 — repaired and machine-green |
| `v13:thm:long-stability` | T027 |
| `v13:cor:cutset` | dependency-only corollary; exact logical pack in `V13V14_DependencyAssembly.lean` |

Definitions T010/T016 are registered but are not counted in the 19
proof-bearing environments.

All non-algebraic inputs have already been source-classified as exact Smith
2013 inputs or standard harmonic/sequence analysis (Coifman-Meyer, HLS,
Littlewood-Paley, Holder/Bernstein, Young/Cauchy-Schwarz).

## v14 exact proof-bearing inventory — 6 nodes

| Node | Public verification node |
|---|---|
| `v14:lem:tensor-contract` | T018 |
| `v14:lem:weak-generations` | T019 |
| `v14:thm:weak-Smith` | T020 + Smith proof-spine audit |
| `v14:thm:WMB-close` | T021 |
| `v14:cor:stability-unconditional` | logical composition of T021 with T026/T027; Lean dependency assembly added |
| `v14:cor:cutset` | dependency-only audit corollary; Lean dependency pack added |

Definition T017 is registered and not part of the six proof-bearing count.

## Status

Subject to compilation of the newly added dependency-assembly file, v13-v14
have no remaining unclassified internal analytic black box under the declared
verification foundation.

The next genuinely new paper-specific block is v15:
cross-quadratic/mixed forcing algebra, finite smooth transport screen, and the
conditional minimal-one-profile reduction.
