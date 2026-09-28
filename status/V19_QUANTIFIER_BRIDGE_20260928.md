# v19 Lemma 14.7 quantifier bridge — exact current boundary

Authority: private synchronized W20 manuscript, LeanSync v4/v19 Lemma 14.7.

## Machine target added in this batch

The theorem statement requires

\[
\exists (c_n)\subset S^1\;\forall f\in L^2,\qquad
\|A_n f-c_n f\|_2\to0,
\]

with the phase sequence fixed **before** the test vector.

The public Lean file now contains a direct operator-level bridge:

1. one fixed unit-modulus sequence \(c_n\);
2. uniform operator contraction \(\|A_n\|\le1\);
3. convergence on one dense test class;
4. extension to every vector with the same \(c_n\);
5. compactness of \(S^1\) and a further phase-convergent subsequence;
6. preservation of all strong limits along that subsequence.

No conclusion is supplied as an input hypothesis.

## What remains before Lemma 14.7 is fully certified

The remaining paper-specific inputs are earlier in the proof, not in the
density/quantifier step:

- instantiate the fixed unit-ball anchor phase from the actual local
  \(W^{1,2}\) multiplier;
- feed Poincare + the unit-modulus variance identity into the actual ball
  means;
- bounded-time branch: instantiate free-group strong continuity and the local
  tail estimate;
- escaping-time branch: instantiate the pseudo-conformal/Fourier identity,
  dominated convergence and Plancherel for the actual operators;
- identify those two branches with the manuscript's conjugated symmetry
  operator \(h_n^{-1}m_nh_n\).

Thus this batch closes the **quantifier/density/subsequence** end of Lemma 14.7,
but does not yet declare the whole lemma machine-closed.
