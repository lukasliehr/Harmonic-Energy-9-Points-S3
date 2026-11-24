# LeanCode

The Lean code of the verification: the statement, the checkers with their soundness theorems, and
the analytic part of the proof. The certificates on which the checkers run are the Lean modules of
[Certificates](../Certificates). The folder is the source directory of three Lake libraries; the
module `S3N9.Statement` is the file `S3N9/Statement.lean`.

| Path | Files | Lines | Contents |
| --- | ---: | ---: | --- |
| [S3N9](S3N9), [S3N9.lean](S3N9.lean) | 21 | 5,102 | The theorem for nine points on the three-sphere: statement, two small certificates, analytic part. |
| [CAP](CAP) | 56 | 19,426 | Checkers for the Lean kernel with their soundness theorems. |
| [CAPNumeral](CAPNumeral), [CAPNumeral.lean](CAPNumeral.lean) | 2 | 78 | The notation `hex% "…"` for large natural numbers. |

## How a computational statement is verified

A *checker* is a function with values in `Bool` that computes with natural numbers. Its
*soundness theorem* states what follows mathematically if the checker returns `true`. A module of
[Certificates](../Certificates) contains data and the theorem `checker data = true`, which the
Lean kernel proves by evaluating the checker (`decide +kernel`).

The checkers are the files [CAP/Core/Packed.lean](CAP/Core/Packed.lean),
[CAP/UniPos/Kernel.lean](CAP/UniPos/Kernel.lean), [CAP/UniPos/PolyKernel.lean](CAP/UniPos/PolyKernel.lean),
[CAP/Wsos/Kernel.lean](CAP/Wsos/Kernel.lean), [CAP/Wsos/Cert.lean](CAP/Wsos/Cert.lean),
[CAP/Wsos/CertKernel.lean](CAP/Wsos/CertKernel.lean) and [CAP/VR/Kernel.lean](CAP/VR/Kernel.lean).
They import no file of Mathlib, so that a module with data loads in a fraction of a second.

No file uses `native_decide`, `sorry` or an additional axiom. Most files of the folder `S3N9` test
during the build that their main theorems depend on the axioms `propext`, `Classical.choice` and
`Quot.sound` only (`#guard_msgs in #print axioms …`).

## The folder S3N9

The labels (C1) to (C8) and (A1) to (A11) are those of
[AnalyticArguments/analytic_arguments.pdf](../AnalyticArguments/analytic_arguments.pdf).

| File | Contents |
| --- | --- |
| [Statement.lean](S3N9/Statement.lean) | The theorem as a proposition, `S3N9.Harmonic9`, in coordinates `Fin 9 → Fin 4 → ℝ`. It imports two files of Mathlib only. |
| [Separation.lean](S3N9/Separation.lean) | (C1): the certificate of the linear programming bound and the theorem `S3N9.separation`. |
| [GramSchmidtCells.lean](S3N9/GramSchmidtCells.lean) | (C5): the conditions on the constants of a Gram–Schmidt cell, `GSCell.Valid`, and their proof for the two sets of constants. |
| [Cstar.lean](S3N9/Cstar.lean) | (A1): the pentagon with the orthogonal square, its 36 distances and its energy $35/2$. |
| [Basic.lean](S3N9/Basic.lean) | (A2), (A3): configurations in coordinates and in Euclidean space; the energy does not depend on the labelling; separated configurations; the near pairs are disjoint. |
| [Chain.lean](S3N9/Chain.lean) | (A3): chains, the labellings that order the near pairs. |
| [Claims.lean](S3N9/Claims.lean), [Cover.lean](S3N9/Cover.lean) | (A4), (A5): pair claims; a chain lies in a pair claim. |
| [Cells.lean](S3N9/Cells.lean), [Cells54.lean](S3N9/Cells54.lean) | (A4): the 113 claims of the cells as data, and the theorem `cells54`. |
| [Fit.lean](S3N9/Fit.lean) | (A5): the comparison of a claim of the library with a claim of a certificate, decided by the kernel, and its soundness. |
| [L3k2.lean](S3N9/L3k2.lean) | (A6): the last cell before its core: the ring split, the selected-edge claims, the core. |
| [Frame.lean](S3N9/Frame.lean), [CellAlgebra.lean](S3N9/CellAlgebra.lean), [CellLemma.lean](S3N9/CellLemma.lean) | (A7): the Gram–Schmidt frame of a configuration and the cell lemma. |
| [Piece.lean](S3N9/Piece.lean), [Leaves.lean](S3N9/Leaves.lean) | (A7): from a cell to the piece of a virtual-root certificate; the leaves of the core. |
| [Core.lean](S3N9/Core.lean) | (A8), (A9): the cover of the core by the leaves, and the theorem of the last cell. |
| [Minimum.lean](S3N9/Minimum.lean) | (A11): the lower bound, with the contacts in the case of equality. |
| [Equality.lean](S3N9/Equality.lean) | (A10), (A11): rigidity, and `S3N9.harmonic9_of`, the theorem from the six statements that the certificates provide. |

## The folder CAP

| Path | Contents |
| --- | --- |
| [Core](CAP/Core) | Vectors and polynomials as packed natural numbers. |
| [UniPos](CAP/UniPos) | The sign of a polynomial in one variable on an interval. |
| [Wsos](CAP/Wsos) | The typed three-point bound on the three-sphere: the checker of a triple type (`Kernel.lean`), the checks of a certificate and of a claim (`CertKernel.lean`), their soundness, and the theorems `typed_bound`, `energy_gt` and `energy_gt_claim`. |
| [VR](CAP/VR) | The virtual-root bound: the checker (`Kernel.lean`), its soundness, the theorem `energy_gt` (`Sphere.lean`), exact certificates (`Exact.lean`) and the contacts (`Contact.lean`). |
| [Schema/LP](CAP/Schema/LP) | The linear programming bound on the three-sphere with a marked pair, `lp_marked`; its kernels as sums of squares. |
| [Schema/ThreePoint](CAP/Schema/ThreePoint) | A lemma on sums over pairs and triples of points. |
| [Transport](CAP/Transport) | The name under which the certificate modules import `hex%`. |

`hex% "1f"` denotes the same natural number as `0x1f` and is read in time that is linear in its
length up to a logarithmic factor. The reader is an elaborator, which Lake compiles to native
code; it only produces a numeral, and the kernel checks every theorem about that numeral.

## Names in the comments

The files were developed in a repository that contains the verification of several theorems, and
their comments use its names.

| Name | Meaning |
| --- | --- |
| `T8` | The theorem for nine points on the three-sphere. |
| the source, the paper; `lma:…`, `prop:…`, `thm:…`, `def:…` | The text from which the proof was formalized, and the labels of its statements. It is not part of this repository; the arguments are stated in [AnalyticArguments](../AnalyticArguments). |
| rows C1 to C8 and A1 to A11 of `S3N9/README.md` | The statements (C1) to (C8) and (A1) to (A11) of [AnalyticArguments/analytic_arguments.pdf](../AnalyticArguments/analytic_arguments.pdf). |
| the conditions (C1) to (C5) of a cell | The conditions (V1) to (V5) of Section 2.4 of that note, the structure `GSCell.Valid`. |
| `E2`, `E3`, `E14`, …; the schemas `S1` to `S4` | Kinds of checkers of the library, for example `E3` for the sign of a polynomial, and kinds of certificates: `S1` the linear programming bound, `S3` the typed three-point bound, `S4` the virtual-root bound. |
| generated modules, leaves, statement modules; `T8N`, `T8V`, `T8X`, `T8A`, `T8S`, `T8VS` | The modules of [Certificates](../Certificates) and their namespaces. |
| `caps/…`, `certgen/…`, `scaling/…`, `bench/…`, the write-up | Documents and programs of the development repository, which are not part of this repository. |

## Differences from the development repository

This folder contains the files of the development repository that the proof imports. They are
unchanged, with one exception: two sentences of the comment at the head of
[S3N9/Statement.lean](S3N9/Statement.lean) referred to documents that are not part of this
repository and were replaced.
