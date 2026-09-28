# Semantic verification correction — 2026-09-28

This audit supersedes blanket full-theorem GREEN claims in the earlier
V12/V13_V14/V15_V16/V17/V18/V19/V20/W1 audit ledgers. It does not revoke a
successful compiler run or assert that the manuscript theorems are false.
It corrects what that compiler evidence actually establishes.

## Confirmed defects in the verification evidence

At source commit 0d3576457826e10d12f6c2ab9524166a2528e70a:

1. `v12_IMS_forcing_kernel` assumed `LAf - wTf + wTf = F` and returned that
   same hypothesis. It did not derive source synthesis from the IMS identity.
2. `v12_closure_product_difference_kernel` and
   `v12_closure_hodge_far_kernel` likewise repeated their desired inequalities
   as hypotheses. Their compilation supplied no proof of those estimates.
3. Generic propositional assembly (arbitrary `WMB`, `Scatter`, `GPEEL`, etc.)
   verifies implication composition only, unless a separate checked theorem
   instantiates those propositions with the actual manuscript statements.
4. Listing FTC, HLS, Poincare, DCT, Rellich, or a published PDE theorem in
   Markdown does not instantiate that result for the paper's concrete fields,
   norms, domains, regularity assumptions and limiting quantifiers.

Consequently old totals such as v12 12/12 GREEN or v19 13/13 GREEN are not
established full-theorem coverage counts. No full-paper completion percentage
is certified by this audit. The user's allowed foundation is unchanged:
precise standard-analysis and published-theorem inputs are permitted; the
paper-specific bridges to their exact hypotheses still have to be checked.

## This batch

- `V12_IMSKernel.lean`: removes the conclusion-as-input from source synthesis;
  adds actual idempotence of a map composed with its left inverse.
- `V12_CompactnessKernels.lean`: replaces the two tautological estimates with
  a complex product-difference inequality and a genuine finite-sum norm bound;
  adds a sequential complex product limit. These are explicitly partial.
- `V12_FrequencyTightnessLimit.lean`: proves Cauchyness and existence of a
  limit in a complete metric space from uniform cutoff approximation and
  Cauchyness of each fixed cutoff. Target convergence is not a hypothesis.
- `V19_AnchoredPhaseNormalization.lean`: checks unit-phase normalization,
  variance control and sequential anchor-transfer estimates.

Compiler status for this new batch must be read from its actual subsequent
GitHub Actions job; this file does not predeclare it PASS.

## Manuscript issue at v19:lem:phase-profile-constant

The statement requires one phase sequence that works for every test function.
The v2 proof chose ball radii using each test function and did not explicitly
ensure that its phase sequence was independent of that choice.
The repair fixes the phase from the normalized mean on one unit ball first,
then compares every larger-ball phase on the common unit ball. It gives
larger-ball convergence for the same phase sequence before selecting a test.
This is a repair of the proof's quantifier order, not a counterexample to the
lemma. The private manuscript revision and its hashes are recorded separately.

## Exact current boundary

Machine compilation of support files and full W20 statement certification are
separate columns. Kernel work has reached the W sections, but a continuous
full-statement certification frontier through v12 has NOT been established.
Outstanding examples include the actual L2/Bochner/Fourier realizations of the
v12 operators, the concrete cutoff subsequence, and the v19 local-to-global
operator instantiation. The later RFCE/rigidity/main-theorem chain also needs
an exact transitive dependency audit. Do not replace these tasks by counting
file names, occurrences of paper labels, or Markdown GREEN rows.
