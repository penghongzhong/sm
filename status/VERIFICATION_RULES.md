# Verification rules

## Allowed foundations

The project is not a from-zero foundational formalization. It may depend on:

- Lean/Mathlib foundational logic and standard analysis already formalized there;
- explicitly registered classical analysis results when their exact statement is used;
- explicitly identified theorems from published literature when the manuscript genuinely cites and uses them.

## Forbidden shortcuts

- no `sorry`;
- no `admit`;
- no custom `axiom` declarations for internal paper nodes;
- no replacing a paper theorem by a weaker surrogate while marking it PASS;
- no assuming the desired scattering conclusion, compactness conclusion, rigidity conclusion, or an equivalent internal node;
- no using an external theorem under a broader statement than the published source supports.

## PASS meaning

`PASS` means the exact Lean statement compiled under the pinned environment and is synchronized with the manuscript statement. It does not mean that an external published theorem has been re-proved from first principles.

## User clarification, 2026-10-01 Asia/Shanghai

The verification baseline is recognized standard analysis and authoritative,
rigorously proved external results. Rebuilding analysis from zero is NOT a
requirement. Every retained external result must have an exact source,
theorem identifier, hypotheses and conclusion. The manuscript's own
load-bearing steps and the concrete applicability of every external result
must still be proved. A failed Lean elaboration is an implementation problem,
not a reason to replace a paper-specific step with an unproved interface.
No weakening of the original theorem is permitted.

## Local-only execution preference, 2026-10-01

Use local incremental Lean compilation and local commits/checkpoints. Do not
push or trigger GitHub validation now; defer upload until quota exhaustion
or publication preparation. An environment failure must be recorded as a
blocker, never as PASS. Continue active work autonomously, with approximately
ten-minute substantive progress reports while execution is possible.

## Superseding instruction, 2026-10-01 10:26 Asia/Shanghai

Resume GitHub compilation; do not use the blocked local Lean runtime. Batch
changes after inspecting completed runs, preserve local checkpoints, keep
PR #6 Draft and never merge. Private TeX/PDF remain excluded. This supersedes
the local-only execution preference above.
