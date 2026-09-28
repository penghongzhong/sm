# T008 strong-forcing source audit

Paper node: `v13:lem:Hk`.

The migration theorem `v13_lem_Hk` currently receives three paper-line estimates
`hfirst`, `hcubic`, and `hAquad` as scalar parameters.  Under full-paper verification these are not new axioms.

## Exact decomposition

The manuscript defines
[
H_k
=2i[P_k(Acdot
abla Q)-A_kcdot
abla Q_k]
 +P_k(VQ+W\bar Q)-|A_k|^2Q_k.
]

The deep-low principal term has already been moved to the left-hand magnetic operator.  The remaining terms fall into exactly three classes.

## Class 1: nondeep first-order magnetic / commutator terms

After fixed-gap dyadic localization, the bilinear symbols have uniform Coifman-Meyer derivative bounds.

Registered external theorem:
A. Benyi, *On a Class of Bilinear Pseudodifferential Operators*, J. Funct. Spaces 2013, Theorem A, at ((p_1,p_2,p)=(4,4,2)).

Combined with time Holder, T001 (|B|_2lesssim Z^2), and the fixed-gap `l^1` frequency kernel, this gives the manuscript estimate
[
|H_k^{(1)}|_{L^{4/3}_{t,x}}
lesssim_Lambda Z^2(kappa*g)_k.
]

## Class 2: cubic zero-order terms

[
A_0Q,quad |Q|^2Q,quad W\bar Q
]
are Riesz/Coifman-Meyer trilinear expressions.  Their dyadic estimates are exactly reduced to the already source-audited:
- Smith Lemma 3.10;
- Smith Corollary 3.11;
with the manuscript's (delta<1/40) slow envelope.

No final `H_k` estimate is imported from Smith.

## Class 3: `|A_k|^2 Q_k`

This uses only Holder plus T001:
[
|P_k(|A_k|^2Q)|_{4/3}
lesssim |A|_4^2(kappa*g)_k
lesssim_E Z^2(kappa*g)_k,
]
because the conserved mass-size (M) is bounded on the fixed energy sublevel.

## Conclusion

The three scalar hypotheses in the current T008 migration theorem are source-reducible to already registered standard/published inputs and T001.

Classification:

**T008 ANALYTICALLY SOURCE-REDUCED; no new internal red point.**

A future tighter Lean implementation should replace the three scalar parameters by a typed multiplier/sequence interface, but doing so does not require a new manuscript theorem.
