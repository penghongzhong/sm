# Exact V12 source trace and certification boundary

Reference manuscript: private LeanSync v4, Theorem 7.2.
This file is audit metadata, not a manuscript publication or a PDE certificate.

## Objects before estimates

I=[a,b], T=b-a>=0; X=R^2; H=C^2.
K_N is the existing inverse-Fourier Schwartz cutoff kernel.
Q(t) takes values in L2(X;H).
F_j(t) takes values in L2(X;H), j=1,2.
G(t) takes values in L^(4/3)(X;H).
C_b=C_b(X;H) with its supremum norm.

L_Delta=i [convolution by Delta K_N]: L2 -> C_b.
L_j=2 [convolution by partial_j K_N]: L2 -> C_b.
L_0=-i [convolution by K_N]: L^(4/3) -> C_b.
S_N(t)=L_Delta Q(t)+L_1 F_1(t)+L_2 F_2(t)+L_0 G(t).
U_N(t)=K_N*Q(t), using the existing actual BCF representative.

## Analytic budget represented in Lean

B_N = ||L_Delta|| T^(3/4) ||Q||_{L_t^infinity L_x^2}
    + sum_j ||L_j|| T^(1/4) ||F_j||_{L_t^2 L_x^2}
    + ||L_0|| ||G||_{L_t^(4/3) L_x^(4/3)}.

The source theorem proves ||S_N||_{L_t^(4/3) C_b} <= B_N.
The Lean implementation keeps the finite ENNReal budget until taking toReal.

Its hypotheses are source-space membership and measurability, not the desired
source estimate. The terminal derivative theorem assumes the exact identity
HasDerivAt U_N (S_N(t)) t and derives
||U_N(t)-U_N(s)||_{C_b} <= B_N |t-s|^(1/4)
using an actual Bochner interval integral and FTC.

## Spatial equicontinuity

For k in L2(X), f_i in L2(X;H), sup_i ||f_i||<=M, set
b_{x0}(x)=||pairing|| M ||k(x0-.)-k(x-.)||_2.
L2 translation continuity implies b_{x0}(x)->0 as x->x0.
The actual convolution distance bound implies
forall i, ||k*f_i(x0)-k*f_i(x)||<=b_{x0}(x).
Hence the actual convolution family is equicontinuous.
No spatial modulus, Bernstein derivative bound or equicontinuity is an input.

## Reverse dependencies still to discharge

Paper fixedN-sources uses the actual products
F_j=A_j[Q]Q and G=V[Q]Q+W[Q]conjugate(Q).
The coefficient lemma yields their spacetime norms, and Fubini must realize
the same functions as the time-valued Lp objects in the source theorem.
Those applications are not certified merely by naming generic F,G.

The distributional Coulomb PDE must produce the actual integral identity
U_N(t)-U_N(s)=integral_s^t S_N(tau) d tau in C_b.
A distributional identity and Lp source bounds do not, by themselves, license
an unproved pointwise Banach-valued derivative at every time and endpoint.
A weak-derivative/absolute-continuity argument or the manuscript's precise
smooth function-space regularity must discharge this boundary. The new
HasDerivAt theorem is a sufficient conditional bridge, not a substitute.

After that: combine the two moduli on each compact spacetime cylinder;
instantiate the actual local L2 representative and hCompact; apply the common
radius/frequency subsequence; prove measurable gluing; verify Theorem 7.1.

## Finite arithmetic check

Eight rational-exponent identities were actually evaluated with SymPy and
all residuals were zero. See V12_SYMPY_TIME_SOURCE_20260930.log.
This does not certify any analytic theorem, PDE identity or compactness step.
