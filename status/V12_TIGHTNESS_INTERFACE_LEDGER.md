# v12:thm:tightness — exact remaining analytic interfaces after the local-L2 bridge

Private manuscript: `stereo_scalar_scattering_v20_W20_LeanSync_v4`, printed
Theorem 7.2, PDF pages 12--13.

This ledger does NOT declare the theorem closed.  It identifies the exact
standard-analysis inputs still needed after the actual Bochner-L2/common-
subsequence Lean bridge.

## A. Finite-slab L2 from the energy bound

Manuscript hypothesis:
[
sup_n|Q_n|_{L_t^infty L_x^2(I	imesmathbb R^2)}le M,qquad |I|<infty.
]

Required conclusion:
[
Q_nin L^2(I	imesmathbb R^2;mathbb C^2),qquad
|Q_n|_{L^2_{t,x}}le |I|^{1/2}M.
]

This is exactly Tonelli/Fubini plus the finite-measure embedding
(L_t^infty(I;L_x^2)hookrightarrow L_t^2(I;L_x^2)).  No PDE input is
hidden here.

## B. Spatial Littlewood--Paley cutoff

The operator in the manuscript is the spatial Fourier multiplier
(P_{le N}), acting only in (x) for every time (t).

Allowed standard facts:
1. Plancherel on spatial (L_x^2);
2. multiplication by a bounded cutoff symbol is an (L_x^2) contraction;
3. Fubini/Tonelli promotes the fiberwise operator to a continuous linear map
   on the finite-slab (L^2_{t,x}).

Mathlib contains the L2 Fourier isometry in
`Mathlib/Analysis/Fourier/LpSpace.lean`:
`norm_fourier_eq` via `Lp.fourierTransformₗᵢ`.
The current Lean bridge now requires (P_N) to be a continuous linear map;
it is no longer an arbitrary function.

## C. Exact manuscript tail quantifier

The manuscript assumption is
[
delta_N:=sup_n|(1-P_{le N})Q_n|_{L^2(I	imesmathbb R^2)}
longrightarrow0.
]

The public Lean file `V12_FrequencyTailAdapter.lean` defines the same
conditional supremum and proves:
- boundedness of the range from a uniform L2 bound and (|P_N|le1);
- each individual tail is bounded by that supremum;
- convergence of the manuscript supremum gives the `hTail` input used by
  the common-subsequence theorem.

This item is considered verified only after its CI run is green.

## D. Fixed-cutoff local compactness

For fixed (N,R), manuscript estimates give:
[
sup_{n,t}|
abla^rP_{le N}Q_n(t)|_inftyle C_{N,r}M,
]
and
[
|P_{le N}Q_n(t)-P_{le N}Q_n(s)|_infty
le C_{N,I,M,Z}|t-s|^{1/4}.
]

On the compact cylinder (I	imesoverline{B_{R+1}}), these imply
uniform boundedness and equicontinuity.  The allowed standard theorem is
Arzela--Ascoli.  Mathlib implementation:
`Mathlib/Topology/UniformSpace/Ascoli.lean`, in particular
`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` and
`ArzelaAscoli.isCompact_of_equicontinuous`.

Uniform convergence on the finite-measure cylinder implies local L2
convergence by
[
|f|_{L^2(D_R)}le |D_R|^{1/2}|f|_{L^infty(D_R)}.
]

What remains is to instantiate these standard statements with the actual
fixed-cutoff representatives; this is an internal application bridge, not a
new PDE theorem.

## E. Compatibility and gluing

The new public module `V12_LocalLimitCompatibility.lean` defines actual
nested L2 restrictions between (D_S) and (D_R) for (Rle S), proves
restriction composition, and proves that limits obtained from the same
subsequence are compatible.

After that machine result is green, only the measurable representative
gluing on the countable exhaustion remains.  This is standard measure-theory
gluing but is not yet represented as a compiled theorem.

## Certification boundary

Theorem 7.2 may be called fully verified under the user's allowed foundation
only after:
- the Ascoli-to-local-L2 compactness generator compiles without `sorryAx`;
- A/B/D are hypothesis-matched to the actual manuscript objects, not merely
  named in prose;
- the actual fixed-cutoff continuous representatives and the
  \(|t-s|^{1/4}\) time modulus are formalized;
- measurable gluing is discharged;
- the resulting strong local limit is fed into Theorem 7.1's exact
  hypotheses.

No percentage is inferred from this ledger.
