# Exact-source Lean verification — KMS companion v3.4.0

**Independent compiler court:** 19 October 2026 (Brannoc / local pinned Lean replay).
**Scope:** mathematical Lean source and pinned build environment, not originality or peer review.

| Item | Verified result |
| --- | --- |
| Compiler | Lean 4.34.0 |
| Mathlib revision | `5ed2965256430c3649e86755f9576b54eca72435` |
| Command | `lake build KMS ShiftedKMS` |
| Build outcome | **PASS — 8,952 jobs** |
| Axiom audit | **51 selected declarations** |
| Axioms reported | `propext`, `Classical.choice`, `Quot.sound` only |
| Omitted proof axiom | No `sorryAx` in the audited declarations |
| Independently compiled input archive SHA-256 | `1c95820646d8237b715078ff43f113355f1ba0d25d164eb6f810a2feee220b74` |
| This v3.4 Lean proof source | **Byte-for-byte unchanged** from that input |

The 51-declaration audit includes the numbered paper-result counterparts and
additional matrix, inverse, phase, conditioning and probability-measure lemmas.
This report states what the original independent compiler and axiom receipts
actually certify. The **website, metadata and licensing updates** of this release
do not modify any `.lean` source file or any pinned build configuration. The
underlying compiler logs and private host paths are not bundled; the source,
imports and exact toolchain are provided for independent reproduction.

To reproduce the proof on your machine:

```sh
cd lean_project
lake exe cache get
lake build KMS ShiftedKMS
```

To sample axioms after building, create a temporary `Check.lean` file
containing:

```lean
import KMS.PaperStatements
#print axioms ShiftedKMS.PaperStatement.thm_det
#print axioms ShiftedKMS.PaperStatement.thm_main_conditioning
```

Then run `lake env lean Check.lean`. The site theorem atlas points to the source
statements. The source-level verifier does not certify historical priority,
novelty, correctness of the plain-English summary or the Zenodo website.

**Manuscript identity:** published PDF MD5 `583f5bdb215c0fb0e6c5321abc01476a`; published TeX MD5 `d4a001098370a1a437edcfadaca85951`, exactly matching the embedded files at https://doi.org/10.5281/zenodo.23486307.
