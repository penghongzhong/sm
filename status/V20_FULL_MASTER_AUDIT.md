# W20 v20 full-master audit

> **Historical audit — certification withdrawn.** The GREEN labels and
> whole-block conclusions below record an earlier, insufficient standard of
> evidence. They are not current full-statement certificates. See
> `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
> `WHOLE_PAPER_COVERAGE.md`; actual objects, internal proof steps and concrete
> external-theorem hypotheses must still be checked against the full manuscript.


Verification authority:
\`stereo_scalar_scattering_v20_W20_LeanSync_v2\`.

Exact v20 proof-bearing inventory: **4 nodes**.

## 1. \`v20:lem:forcing-window\`

The proof recombines already-certified v13 estimates:

- \(H_k\): v13 Hk strong forcing;
- \(|A_k|^2Q_k\): coefficient \(L^4\) + Holder/LP;
- high-high magnetic part: v13 HHL;
- deep-low non-high-high part: v13 Mnd plus causal envelopes.

No new PDE estimate is introduced in v20.

**Status: GREEN relative to the v13 source boundary.**

## 2. \`v20:lem:N-tail\`

The global \(N^0\) space is the completion of time-compact,
finite-frequency smooth forcing. Time restriction is contractive in every
forcing atom. Approximation by a compact-time element gives tail absolute
continuity.

**Status: GREEN relative to standard norm-completion facts.**

## 3. \`v20:thm:finiteS-scattering\`

Finite global \(S^0\) gives finite global \(L^4\), hence a finite small-window
partition. Node 1 gives \(\mathscr F[Q]\in N^0(\mathbb R)\).
The free Smith/Duhamel estimate and node 2 make the interaction-picture
Duhamel integral Cauchy in \(L^2\). Tail linearization uses the same estimate.
The finite bookkeeping is compiled in \`V20_ScatteringKernels.lean\`.

**Status: GREEN relative to the registered free Smith/Strichartz estimate and
standard Banach completeness.**

## 4. \`v20:cor:subcritical-scattering\`

v17 rough-subcritical flow supplies finite global \(S^0\); node 3 gives
two-sided free scattering.

**Status: GREEN.**

## Boundary

The later \(\mathrm{MAGFREE}_{20}\) and
\(\mathrm{SELF\!-WILSON}_{20}\) objects are definitions/remarks, not among
the four proof-bearing v20 nodes. The manuscript explicitly retracts the old
unproved implication
\(\mathrm{MAGFREE}_{20}\Rightarrow\mathrm{TVAN}_{19}\).

Therefore v20 verification does **not** close TVAN. The next proof-bearing
block is W1, where the actual true-radiation/wave-operator construction begins.
