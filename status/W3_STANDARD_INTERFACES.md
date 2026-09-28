# W3 standard/external interface audit

## Keel--Tao free Strichartz

Only the free \(2D\) endpoint-admissible \((q,r)=(4,4)\) estimate and its
dual Duhamel \(L^{4/3}\to L^4\) form are used in W3.
No magnetic Strichartz estimate is imported.

## Littlewood--Paley

W3 uses the standard \(L^4\) square-function equivalence and its
\(L^{4/3}\) dual/range forms, plus finite-frequency reconstruction.

## Mixed Hölder

The lateral product estimate uses only the \(G_k\)-norm components already
defined in v13 and the reciprocal exponent identities
\(1/3+1/6=1/2\).

## Bounded real-potential self-adjointness

For the potential guardrail, a bounded real multiplication operator is a
bounded self-adjoint perturbation of the self-adjoint Laplacian, so the
resulting Schrödinger group is unitary.

## Generic Hilbert/operator facts

- Cauchy--Schwarz;
- \(T^*T=I\Rightarrow TT^*\) is an orthogonal projection;
- cocycle composition for an already-existing unitary propagator;
- finite-dimensional matrix differentiation.

No statement that a rough self-generated magnetic connection automatically
has global dispersive estimates is included in these interfaces.
