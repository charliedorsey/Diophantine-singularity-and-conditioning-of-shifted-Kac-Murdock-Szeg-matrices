# Shifted KMS matrices — Lean 4 and interactive companion

**Author:** Charlie Dorsey, independent researcher. **Companion release:** 3.4.0, 19 October 2026.

Start with **`OPEN_ME.html`** (or `site/index.html`). The entire reading experience is self-contained and runs offline, including the interactive numerical explorer.

## Accompanying research preprint

**Diophantine singularity and conditioning of shifted Kac–Murdock–Szegő matrices** (2026), unrefereed research preprint,
Zenodo DOI: [https://doi.org/10.5281/zenodo.23486307](https://doi.org/10.5281/zenodo.23486307).

The manuscript PDF (`manuscript/shifted_kms.pdf`) and LaTeX source (`manuscript/shifted_kms.tex`) are included **byte-for-byte as deposited** at that DOI, so the companion also works as an offline reading edition. The paper is the primary scholarly reference. The companion is a distinct software/educational object; it does not assert arXiv acceptance or peer review.

## What's included

- `site/index.html`: accessible overview and four entry routes;
- `site/proof_guide.html`: the mathematical argument in eight navigable steps;
- `site/theorems.html`: 28 numbered paper results linked to exact Lean declarations;
- `site/source/`: browsable Lean source with stable local line anchors;
- `site/interactive/index.html`: original offline interactive numerical explorer, with conservative finite-precision labeling;
- `site/for_curious_readers.html`: a separate younger-readers essay;
- `lean_project/`: Lean 4.34.0 source with pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`;
- `REPRODUCE.md` and `VERIFICATION.md`: build instructions and exact-source verification evidence.

## Reproduction and proof status

```sh
cd lean_project
lake exe cache get
lake build KMS ShiftedKMS
```

An **independent pinned Lean build on 19 October 2026** completed 8,952 jobs successfully, with an axiom audit of 51 selected declarations reporting only `propext`, `Classical.choice` and `Quot.sound`. This release's Lean source, build configuration and Mathlib pin are **byte-for-byte identical** to those compiled inputs. See `VERIFICATION.md` for the exact evidence scope and commands. Checksums are provided in `SHA256SUMS`; verify from the extracted archive root with `shasum -a 256 -c SHA256SUMS` (macOS) or `sha256sum -c SHA256SUMS` (Linux).

Lean checks formal statements and proofs against its trusted foundations, **not** mathematical novelty, publication priority or the accuracy of every informal paraphrase. The online Mathlib dependency may require a network connection to rebuild; offline *reading* does not.

## Citation, licenses and contribution account

The companion is a separate research-software object from the manuscript preprint. Its `CITATION.cff` describes software release 3.4.0 and references the paper's DOI. A companion DOI can be added to the repository/record metadata once minted; no unassigned DOI is claimed here.

This is a **mixed-license archive**: original code under **Apache-2.0** and original paper and explanatory/visual content under **CC BY 4.0**. See `LICENSE.md`, `COPYRIGHT.txt` and `LICENSES/` for exact scope. Dependencies fetched by Lake have their own licenses.

Generative AI participated substantially in research, proof development, writing, **all Lean code**, interactive software and release preparation. Charlie Dorsey supplied research direction, skeptical editing and publication responsibility. Manuel Bogoya supplied limited readability feedback without endorsing the mathematics. The detailed authorship and scope notes are at `site/scope.html` and in the manuscript.

## About the interactive edition

This ZIP includes an offline adaptation of the original explorer also published at https://charliedorsey.com/research/one-sine-two-numbers/. Its draggable triangle, parameters and real-time plots are illustrative: floating-point near-hits and short rational approximations are **not exact certificates** of singularity or long-term Diophantine behavior. No online script or CDN is required to explore it locally.
