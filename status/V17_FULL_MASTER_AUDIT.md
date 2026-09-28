# W20 v17 full-master audit

Authority: synchronized 133-page W20 manuscript.

Exact v17 proof-bearing inventory: 7 nodes.

## 1. v17:lem:Coulomb-unique

Public migration contains:
- pointwise gauge factor nonvanishing;
- gradient-zero conclusion;
- constant-phase assembly from the standard connected-domain
  distribution theorem;
- positive-real Hilbert pairing normalization fixing the unit phase.

Status: **GREEN relative to the standard distribution fact
"zero gradient on a connected domain implies constant."**

## 2. v17:thm:strong-Coulomb-density

The migration contains the Hilbert polarization/strong convergence closure.
External inputs are explicitly:
- smooth \(W^{1,2}\) density of degree-zero Sobolev maps (Bethuel);
- standard weak subsequence compactness;
- v16 weak realization and Coulomb uniqueness.

Status: **GREEN relative to those published/standard inputs.**

## 3. v17:thm:rough-subcritical-flow

Paper mechanism:
- strong initial-data density from node 2;
- strict energy gap \(E_0<E_1<E_c\);
- smooth global bound by the definition of \(E_c\);
- full-\(N^0\) stability gives a Cauchy family on every finite interval;
- Banach completeness/diagonal exhaustion gives the rough flow;
- v12 closure gives the equation and v16 gives pointwise-in-time realization.

The scalar Cauchy estimate is isolated in
\`lean/v17/V17_DynamicSupportKernels.lean\`.

Status: **GREEN/YELLOW boundary** — no new PDE estimate is hidden, but the
exact Banach-space completion/interval exhaustion is retained as a standard
functional-analysis interface.

## 4. v17:cor:subcritical-profile-flow

The strict profile energy inequality is already present in the migration and
is repeated as a full-master support kernel.  The corollary is direct
composition of bounded static realization with node 3.

Status: **GREEN once node 3 is accepted under its registered standard
completion interface.**

## 5. v17:prop:smooth-screened-collision

Paper-specific nontrivial content:
- transport phase differentiation along the carrier ray;
- uniform derivative bounds after the carrier-coordinate change of variables;
- \(L_t^1L_x^2\) residual cost \(O(\tau_M)\);
- exit phase converges to the canonical Wilson/Radon screen;
- the short post-collision bridge costs only the endpoint \(o(1)\) mismatch.

The carrier-size cancellation is already v15 GREEN and the residual-length
bookkeeping is kernelized here.

Status: **YELLOW** — the exact carrier-coordinate/Wilson exit-limit interface
still needs a source-typed formal statement.

## 6. v17:thm:rough-screen-diagonal

The diagonal two-error bookkeeping is kernelized.  Remaining analytic inputs
are exactly:
- fixed-smooth-level collision residual -> 0 from node 5;
- smooth profile approximation in \(S^0\) from node 3;
- v16 screen Lipschitz continuity;
- full-\(N^0\) stability.

Status: **YELLOW**, blocked only by the exact node-5 collision interface and
the standard diagonal-selection realization.

## 7. v17:cor:cutset

Dependency-only corollary.  Once nodes 1-6 are closed, the remaining profile
front is exactly
\[
\mathrm{CRIT\!-FLOW}_{17}+\mathrm{ESC\!-RAD}_{17}.
\]

## First v17 red/yellow cut-set

The first genuinely paper-specific unclosed verification item is therefore
the **smooth screened collision exit-limit**, not rough-flow existence or
Coulomb density.
