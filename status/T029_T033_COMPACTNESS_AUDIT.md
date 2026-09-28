# T029–T033 compactness / weak-realization audit

Verification authority: synchronized 133-page W20 manuscript.

## T029–T030 — explicit stereographic triad and differentiated-frame identities

The migration batch does not treat these as external hypotheses.  It defines the stereographic triad explicitly and proves the differentiated identities coordinate-by-coordinate:

- `v16_lem_dN0`
- `v16_lem_de10`
- `v16_lem_de20`
- `v16_lem_a0frame`
- `v16_lem_frame_N`
- `v16_lem_frame_E1`
- `v16_lem_frame_E2`
- `v16_lem_frame_A`
- `v16_lem_energy_triad_pointwise`

The proofs use only quotient/product differentiation already separated at the paper level, elementary field algebra, and
`sin^2+cos^2=1`.

Classification: **INTERNAL ALGEBRA FORMALIZED**.

## T031 — weak Coulomb realization

`WeakCoulombRealization` is a data structure recording:
- the exponent `4/3 < p < 2`;
- orientation/frame/divergence residuals;
- their exact vanishing.

Classification: **DEFINITION CLOSED**.

## T032 — frame compactness quantitative bounds

Paper node: `v16:lem:frame-compactness`.

The paper uses:
1. T001: `||B_n||_1 <= 2 M^2`;
2. the standard endpoint Riesz-potential estimate
   `I_1 : L^1(R^2) -> L^{2,∞}(R^2)`;
3. on each finite-measure ball, the standard Lorentz embedding
   `L^{2,∞} -> L^p`, `p<2`;
4. T030 differentiated-frame identities.

The current Lean theorem `v16_lem_frame_compactness` formalizes the complete scalar norm bookkeeping after items 2–3 are supplied as standard-analysis interfaces.

Classification: **STANDARD-ANALYSIS REDUCED**.

## T033 — weak-profile realization

Paper node: `v16:thm:weak-profile-realization`.

The manuscript proof has the following exact compactness chain.

Fix `4/3 < p < 2`, set
[
p'=rac{p}{p-1},qquad p^*=rac{2p}{2-p},
]
and note `p' < p^*`.

From T032 and local compactness:
- `N_n -> N` strongly in every finite `L^q_loc`;
- `E_{a,n} -> E_a` strongly in every `L^q_loc` with `q<p^*`;
- `A_n ⇀ A` weakly in `L^p_loc`;
- after a subsequence, the frame vectors converge almost everywhere, preserving the orthonormal/orientation relations.

The frame equations then pass to the limit by two weak–strong pairings:
- `Q_{j,n} ⇀ Phi_j` in `L^2` paired with strong `E_{a,n},N_n` in local `L^2`;
- `A_{j,n} ⇀ A_j` in `L^p` paired with strong `E_{a,n}` in local `L^{p'}`, made possible by `p'<p^*`.

Weak divergence convergence gives `div A = 0`.
The limiting differentiated-frame equations then imply
[
A_j=E_1cdotpartial_jE_2,
]
and T030 gives pointwise
[
|partial_jN|^2=4|Phi_j|^2,
]
hence the exact energy identity.

### Current Lean coverage defect

The current migration theorem `v16_thm_weak_profile_realization` receives
`hON_limit`, `hDiv_limit`, `hFrameN_limit`, `hFrameE1_limit`, and
`hFrameE2_limit` as theorem parameters.

These are **not** admissible new axioms for full-paper certification.  They are the outputs of the standard compactness/weak–strong passage above and must be represented by typed standard-analysis interfaces or directly formalized.

Current classification:

- final realization packing + exact energy algebra: **LEAN KERNEL PRESENT**;
- exponent algebra `p'<p^*`: to be Lean-kernelized;
- Banach–Alaoglu / Rellich / diagonal extraction: **STANDARD COMPACTNESS INTERFACE PENDING**;
- weak×strong product passage in distributions: **STANDARD FUNCTIONAL-ANALYSIS INTERFACE PENDING**;
- preservation of the finite-dimensional frame relations under a.e. convergence: **ELEMENTARY LIMIT BRIDGE PENDING**.

Therefore **T033 is not yet full Lean PASS**.  It is the first substantive compactness bridge after the v13–v14 source reductions.
