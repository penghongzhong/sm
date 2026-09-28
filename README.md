# Schrödinger Maps — Lean Verification

Public Lean verification workspace for selected proof-bearing components of a Schrödinger maps scattering project.

## Scope

This repository intentionally contains **Lean verification code only** together with the minimal Lean/Lake/CI configuration needed to compile it.

It does **not** contain the research manuscript, TeX source, PDF, or unpublished proof notes.

## Verification policy

- No `sorry`, `admit`, or custom `axiom` declarations.
- Published/standard external interfaces must be explicitly identified in the Lean sources.
- Internal proof-bearing nodes are intended to be proved rather than postulated.
- GitHub Actions recompiles the public Lean verification files.

## Current public snapshot

Source verification snapshot: private working branch `section2-strict-sync`, commit `0681282c197012f204785bccabcd5057668bfd95`.

The public repository is a verification mirror only; the manuscript remains separate and private.
