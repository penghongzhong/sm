# Section 2 strict audit — Coulomb coefficients, spacetime curvature, low-frequency budget

Date: 2026-09-27

## Scope

Paper section: `v12:sec:coeff`.

Verification standard:

- definition before use, including symbols nested inside compound formulas;
- no overloaded mathematical object with two incompatible types;
- formula-first proof presentation;
- exact equation/lemma references instead of vague anaphora;
- Lean promotion only for genuinely compiled proof kernels;
- TeX and PDF must compile from the same `paper/CURRENT` source.

## Structural repairs made

1. Defined
   `N_0`, spatial/spacetime index sets, multi-index `beta`, `partial_x^beta`,
   `nabla`, and `Delta` before first use.
2. Removed the old potential collision between the spatial fields `Q_j`
   and the later time field `Q_0`: only `j in {1,2}` is introduced in the
   scalar-to-Coulomb definition; `Q_0[Q]` is introduced only in the electric
   curvature lemma.
3. Preserved the whole-paper meaning
   `A[Q] = (A_1[Q],A_2[Q])` as the spatial Coulomb connection.
4. Introduced the distinct full spacetime connection
   `mathscr A[Q] = (A_0[Q],A_1[Q],A_2[Q])`.
5. Defined convolution, Fourier multipliers, spacetime norms, low-frequency
   projections, and field-dependent low-frequency objects before use.
6. Split compatibility into the explicitly defined predicates
   `C_curv[Q]`, `C_tors[Q]`, and `C_evol[Q]`, then defined `Comp_I(Q)`.
7. Replaced the prose Hodge invocation by the exact formula interface
   `(div X=0, curl X=f, X->0) => X=K*f`.
8. Made field dependence explicit in carrying formulas:
   `A_0[Q]`, `W[Q]`, `V[Q]`, `S_jl[Q]`, `m[Q]`, `Q_0[Q]`.

## Static dependency audit

At the audited commit:

- duplicate labels: 0;
- missing refs/eqrefs/pagerefs: 0;
- Section 2 internal forward references: 0.

## SymPy finite-algebra regression

The following identities were independently checked symbolically:

1. Stereographic curvature:
   [
   \partial_1 a_2-\partial_2 a_1
   -4g^{-2}\operatorname{Im}
     (\overline{\partial_1z}\,\partial_2z)=0.
   ]

2. Electric-divergence substitution:
   [
   -4\sum_{\ell=1}^2
   \left(dS_\ell-\tfrac12 dm_\ell\right)
   -
   \left[-4(dS_1+dS_2)+2(dm_1+dm_2)\right]=0.
   ]

3. Low-frequency constants:
   [
   4\cdot2\cdot2+2\cdot2=20,
   \qquad
   4\cdot2\cdot2+2\cdot2\cdot2=24.
   ]

Result: PASS.

## GitHub Lean status

Dedicated workflow: `Section 2 Lean CI`.

Compiled with no `sorry`, `admit`, or custom `axiom` declarations:

- `lean/verified/T001_CoefficientBudget.lean`: PASS;
- `lean/section2/S2_CoefficientConstant.lean`: PASS;
- `lean/section2/S2_ElectricIdentityKernel.lean`: PASS;
- `lean/section2/S2_LowFrequencyBudgetKernel.lean`: PASS.

The electric and low-frequency files are deliberately named **Kernel**:
their PASS certifies the finite algebra / constant bookkeeping, not yet the
full Fréchet/distribution/Fourier analysis layer.

## Remaining Section 2 formalization obligations

These are explicit, not hidden assumptions:

1. formalize the stereographic differential identity leading to
   `v12:eq:chart-curv-proof` at the function/derivative level;
2. formalize the standard Hodge uniqueness interface used in
   `v12:eq:Hodge-uniqueness-input`, or register the exact allowed external
   analysis theorem if retained as an interface;
3. formalize the covariant product-rule line in `v12:eq:S-derivative`;
4. connect the Mathlib Plancherel/multiplier layer to
   `v12:eq:Tjl-L2`, `v12:eq:Plem-L2`, and `v12:eq:Plem-derivative`;
5. connect the registered HLS input to the exact paper norm objects.

Until these are closed, Section 2 is **formula/definition closed and finite-kernel Lean PASS**, not yet full analytic Lean PASS.
