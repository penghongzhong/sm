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
