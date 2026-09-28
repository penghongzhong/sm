# T003 Smith published-input source audit

Paper node: `v13:prop:Smith-inputs`.

External source:

Paul Smith, *Conditional global regularity of Schrödinger maps: subthreshold dispersed energy*, Analysis & PDE 6 (2013), no. 3, 601–686.

## Allowed source tags

| Lean tag | Smith source | Exact scope retained |
|---|---|---|
| `prop36_main_linear` | Proposition 3.6 | frequency-localized free Schrödinger linear estimate `G_k <- L2 data + N_k forcing` |
| `lemma39_N_bilinear` | Lemma 3.9, (3-10) | `N_k` high-output/deep-low bilinear estimate, with the published frequency restriction |
| `lemma39_L2_bilinear` | Lemma 3.9, (3-11) | `L2_{t,x}` bilinear estimate with the published half-gap decay |
| `lemma310_trilinear` | Lemma 3.10 | trilinear `N_k` estimate with Smith's published coefficient `C_{k,k1,k2,k3}` |
| `cor311_envelope_sum` | Corollary 3.11 | summation of the Lemma 3.10 coefficients against frequency envelopes |
| `section5_modified_product_spaces` | Section 5, especially the definitions preceding (5-31) | modified forcing/solution spaces used for the adapted product form; Smith explicitly chooses the `N_k`-based norms **with the local-smoothing/maximal-function forcing component omitted** |
| `cor57_abstract_bilinear` | Corollary 5.7, (5-23) | abstract bilinear Strichartz under the published Fourier-support, small real magnetic-potential, narrow-direction, adapted-form, and controlled-derived-sequence hypotheses |

Smith states that `delta = 1/40` suffices for the paper's frequency envelopes. The manuscript's `0 < delta < 1/40` restriction is therefore not an enlargement of the published range.

## Explicitly forbidden as Smith-published tags

The following are **not** admitted by T003:

- `freePlus_Duhamel_derived`: the `N_k^+` linear estimate is derived in the manuscript from Proposition 3.6 plus the standard Duhamel/`L1_t L2_x` atom; it is not mislabeled as a Smith proposition.
- `caloricGauge_global`
- `heatFlow_global`
- `finalSchrodingerMap_regularity`

Thus no later theorem may obtain the paper's caloric/global/scattering conclusions merely by requesting a generic "Smith input".

## Audit result

`v13_prop_Smith_inputs` has the correct source boundary.

Classification: **SOURCE-AUDIT PASS**.

This status certifies the external-theorem whitelist only; it does not by itself certify later internal uses of the allowed tags. Each later use must still retain the published hypotheses.
