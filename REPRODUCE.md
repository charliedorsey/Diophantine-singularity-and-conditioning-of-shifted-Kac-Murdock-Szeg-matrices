# Reproducing the shifted KMS paper and formalization

The offline interactive site opens with `OPEN_ME.html` without installing anything.

## Lean 4.34.0

Install Lean using Elan, then in a terminal:

```sh
cd lean_project
lake exe cache get
lake build KMS ShiftedKMS
```

The dependency is locked to Mathlib v4.34.0 and commit
`5ed2965256430c3649e86755f9576b54eca72435` by
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

A separate, completed independent source build and 51-declaration axiom audit
are documented in `VERIFICATION.md`. This archive contains the *same Lean
source and build configuration*. Reproducing the build on another machine is a
new check; the public archive does not include machine-specific build logs.

## LaTeX

```sh
cd manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error shifted_kms.tex
```

The embedded PDF/TeX are byte-for-byte equal to the files published at
https://doi.org/10.5281/zenodo.23486307. See `site/reproduce.html` for the
human-readable instructions and the theorem atlas for 28 formal counterparts.
