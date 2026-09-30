# W20 W2 full-master audit

> **Historical audit — certification withdrawn.** The GREEN labels and
> whole-block conclusions below record an earlier, insufficient standard of
> evidence. They are not current full-statement certificates. See
> `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
> `WHOLE_PAPER_COVERAGE.md`; actual objects, internal proof steps and concrete
> external-theorem hypotheses must still be checked against the full manuscript.


Verification authority:
\`stereo_scalar_scattering_v20_W20_LeanSync_v2\`.

Exact W2 proof-bearing inventory: **3 nodes**.

## 1. \`w2:lem:constant\`

After the parabolic normalization
\(t=t_*+2^{-2k}\tau\), \(x=x_*+2^{-k}Y\), \(m=k-\Lambda\),
the three derivative bounds scale to
\(2^{-2\Lambda}\), \(2^{-3\Lambda}\), and \(2^{-2\Lambda}\).
Those exponent identities are compiled in
\`lean/w2/W2_NormalizedWindowKernels.lean\`.
Line integration is ordinary FTC.  The constant connection is then removed by
the exact affine phase; this is ordinary product/chain-rule algebra.

**Status: GREEN.**

## 2. \`w2:prop:localL4\`

Despite the historical label, the retained lemma asserts only the exact
conjugated equation
\[
(i\partial_\tau+\Delta)v
=e^{-i\Phi}F+2ib\cdot\nabla v+i(\operatorname{div}b)v+|b|^2v-b_0v.
\]
It does **not** assert the withdrawn local \(L^4\) estimate.  The statement is
finite covariant/product-rule algebra.

**Status: GREEN.**

## 3. \`w2:lem:no-sup-sum\`

The diagonal array \(a_{j,n}=1_{j=n}\) gives column sum one and row supremum
one.  Finite \(N\) versions are machine checked; letting \(N\to\infty\)
proves no uniform sum/sup exchange can hold.

**Status: GREEN.**

## W2 boundary

The manuscript explicitly withdraws the old local-L4 and URS compression
claims.  Those remarks are guardrails, not proof-bearing theorems.
The corrected localization/source and coherent-square-function analysis begins
in W3.
