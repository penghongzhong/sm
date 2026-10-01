# Local verification checkpoint — 2026-10-01

User instruction: local Lean verification and local preservation only for now.
Do not push or trigger GitHub validation; defer upload until quota exhaustion
or publication preparation. PR #6 remains Draft; never merge or change visibility.
Private manuscript sources and PDFs must remain outside the public repository.

## Actual execution status

Pinned official Lean 4.35.0-rc3 Linux toolchain was downloaded and extracted.
Running `bin/lean --version` exits 1 with `error: failed to locate application`.
Setting the officially documented `LEAN_SYSROOT` to the installation directory
also exits 1 with the same message. This is a compiler startup/environment
blocker, before any project proof is checked. No runtime permission bypass
was attempted. The archive ownership warnings are separate from this error.

No new local Lean PASS is claimed. Last inspected completed validation remains
Run 169: 134/152 files passed, 18 failed. This is NOT paper coverage.
Run 170 was already running before the local-only instruction; its result
has not been retrieved since that instruction.

## Preserved uncompiled candidates

Eleven new modules after remote commit 2960301188b6c29ac9586c6a2388aad71c5436d1:
YNS real-cylinder integrals; YZZBZ raw potential formula; YZZGR original
advective distribution tests; YZZKT distribution extension; YZZNE distribution
PDE closure; YZZSD all-real coefficient convergence; YZZSE spatial-constraint
extension; YZZSF coefficient extension; YZZU original constraint closure;
YZZV compatible local closure; YZZW closed-slab local closure.
All carry prefix V12_. These are candidates, not certified theorems.

The new route tests original weak divergence with the concrete product qψ.
It avoids imposing additional joint smoothness of A or continuity of A0.
Original PDE/compatibility assumptions still require exact manuscript matching.
Theorem 7.1, Theorem 7.2, and the later dependency tree remain OPEN.

## Audit and resumption

LOCAL_DEPENDENCY_AUDIT_20261001.json records forward and reverse imports
for 171 Lean files. Static import existence/order and forbidden-token scans
found no errors; these checks do not replace Lean elaboration or semantic audit.
First restore ordinary supported local Lean execution, then compile the five
Run 169 root fixes, their dependants, and the new candidate chain incrementally.
Retain recognized analysis and precisely registered authoritative results;
prove all manuscript-specific load-bearing steps and application conditions.

Latest private manuscript is v21 WeakDivergence, 140 pages, already saved.
Its 207 original theorem/lemma/proposition/corollary statements are unchanged.
It records the pending verification status rather than asserting completion.

## Superseded at 10:26 Asia/Shanghai

User reauthorized GitHub compilation. Run170 actually completed:142/160 PASS,
18FAIL. Six direct roots: FC measurable-section equality; SZZ star measurability;
WW direction abbreviation; GP beta reduction; HP redundant dsimp; J integral
addition normalization. Repairs and 11 saved candidates await the next run.
No full-paper certification follows from these counts.

## Actual Run174 and batch175 (2026-10-01T04:03Z)

Run174 completed FAILURE:175/189 PASS,14 FAIL,3 direct roots,11 dependent
failures,8 new PASS and no regressions. Latest private saved manuscript v25
(141pages,207 unchanged original statements); its status records Run173 and
will be synchronized separately. Run175 submission contains BV/GW/KT fixes,
T implicit-AE-restriction fix, four literal function-space candidates and
one single-field budget candidate. Full7.1/7.2 and whole paper remain OPEN.
GitHub compilation only; PR6 remains Draft/open/unmerged.
