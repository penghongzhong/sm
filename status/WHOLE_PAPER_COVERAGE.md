# Whole-paper Lean coverage ledger

Verification target: `SM_Lean_Min_v4_SYNC_T025_T027_20260918` (36 pages).

Goal: verify the full short-paper scattering chain relative only to explicitly registered standard analysis results and published external theorems. A node is **PASS** only when its Lean statement matches the synchronized short manuscript and compiles without `sorry`, `admit`, custom `axiom`, or an internal paper conclusion smuggled in as a hypothesis.

## Theorem inventory

The theorem-by-theorem manual inventory contains **94 proof-bearing nodes**:

- T001: coefficient budget;
- T002–T003: Smith spaces and exact published-input whitelist;
- T004–T028: weak forcing, causal envelopes, Volterra, short/long stability;
- T029–T057: compactness, realization, wave operator, peeling, TVAN, Palais–Smale, rigidity, finite-S scattering, Wilson/REL-REAL;
- T058–T078: RFCE static / projected-torsion block;
- T079–T092: RFCE dynamic / principal magnetic block;
- T093: Lean-min RFCE closure;
- T094: Lean-min main scattering chain.

Current imported mega-batch: N001–N033 only. N034–N094 still require migration/splitting and exact synchronization.

## Current status

| Range | Meaning | Status |
|---|---|---|
| T001 | coefficient budget | finite algebra compiled previously; full exact analytic interface recheck pending |
| T002–T003 | resolution definition / external source whitelist | pending promotion |
| T004–T028 | weak forcing / causal / Volterra / stability | imported partially through N001–N033; theorem-by-theorem recheck pending |
| T029–T033 | first compactness/realization nodes | imported partially through N001–N033; recheck pending |
| T034–T057 | remaining compactness/realization/rigidity front end | not yet migrated to public verified files |
| T058–T078 | RFCE static | not yet migrated |
| T079–T092 | RFCE dynamic | not yet migrated |
| T093 | RFCE closure | not yet migrated |
| T094 | final main theorem | not yet migrated |

## External-foundation boundary

Allowed foundations are the standard-analysis list stated in the short manuscript plus the exact published Smith results registered in T003. Internal nodes bearing v*/w* source labels are never external axioms.

## Full-paper completion criterion

The verification is complete only when:

1. T001–T094 all have exact synchronized Lean statements;
2. every internal node is proved rather than postulated;
3. every allowed external theorem has an exact source/interface record;
4. the dependency tree reaches T094 with no unverified internal edge;
5. the final TeX/PDF hashes match `status/MANUSCRIPT_SYNC.md`.
