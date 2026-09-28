# v17 smooth screened-collision standard interfaces

This ledger fixes the external-analysis boundary for
\`v17:prop:smooth-screened-collision\`.

## C1 — FTC along an affine characteristic

For smooth compactly supported \(F\),

\[
\chi_M(t,x)=\int_{-\infty}^{t}
 F_M(s,x-2M(t-s)\omega)\,ds
\]

satisfies

\[
(\partial_t+2M\omega\cdot\nabla)\chi_M=F_M(t,x).
\]

This is ordinary one-dimensional FTC plus the chain rule.

## C2 — Ray change of variables

At the outgoing time in carrier coordinates,

\[
2M\int A_b(s,y+2M\omega s)\cdot\omega\,ds
=
\int A_b\!\left(\frac{\sigma-y_\parallel}{2M},
 \sigma\omega+y_\perp\omega^\perp\right)\cdot\omega\,d\sigma .
\]

The Jacobian cancellation is machine checked in
\`V17_ScreenCollisionKernels.lean\`.

## C3 — Compact-support dominated convergence

For fixed smooth compactly supported \(A_b\), the integrand in C2 converges
pointwise to its \(t=0\) value and is dominated on one fixed compact
\(\sigma\)-interval.  DCT therefore yields the outgoing ray integral.
Spatial derivatives are handled identically because all derivatives are
smooth and compactly supported.

The \(V_b\) term lacks the prefactor \(2M\), hence after the same substitution
it has an explicit \(1/(2M)\) and tends to zero.

## C4 — Short-interval forcing estimate

Uniform smooth \(L_x^2\) control on an interval \(J\) gives

\[
\|F\|_{L_t^1L_x^2(J)}
\le |J|\,\|F\|_{L_t^\infty L_x^2(J)}.
\]

Here \(|J|=2\tau_M\to0\).  \(L_t^1L_x^2\) is already one of the admitted
\(N^0\) forcing atoms in the manuscript.

## C5 — Canonical ray/Radon phase identification

The v16 canonical screen is the fixed \(-\infty\)-normalized primitive of the
curvature Radon transform.  The line integral of the canonical Coulomb
connection along the ray has the same transverse derivative; hence the two
differ by a constant phase.  The canonical endpoint convention fixes this
constant.  This is the ordinary FTC/Stokes identity applied to the already
certified Coulomb-Hodge connection.

No nonlinear scattering statement is included in C1--C5.
