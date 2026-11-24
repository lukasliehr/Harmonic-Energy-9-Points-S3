# Certificates

The computational part of the proof consists of eight statements, (C1) to (C8); they are stated in
[AnalyticArguments/analytic_arguments.pdf](../AnalyticArguments/analytic_arguments.pdf), Section 2.
Each of them is established by certificates: exact data on which the Lean kernel evaluates a checker.
The checkers and the theorems that derive a mathematical statement from an accepted check are in
[LeanCode](../LeanCode). This folder holds the data: 406 Lean modules with 454 MB of source.

| Folder | Statement | Modules | Main theorems |
| --- | --- | ---: | --- |
| [Typed](Typed) | (C2), (C3), (C4): 110 typed three-point certificates and the certificate of the first cell. Each bounds the energy by $35/2$ on the domain that it declares and on its claims; the certificates have 120 claims, which cover 54 of the 55 cells and six parts of the last cell | 223 | `T8N.W<i>.energy`, `T8N.W<i>.energy_claim<k>`, `T8N.WL0.energy_claim0` |
| [VirtualRoot](VirtualRoot) | (C6): 11 virtual-root certificates with margin, for eleven parts of the last cell | 173 | `T8V.<leaf>.energy` |
| [Sharp](Sharp) | (C7), (C8): the sharp virtual-root certificate for the part of the last cell that contains the minimizer. Its bound is $35/2$, and a configuration of this part with energy $35/2$ has the inner products of the minimizer | 9 | `T8X.I3.energy`, `T8X.I3.contacts` |
| [Theorem](Theorem) | the hypotheses of the analytic part, and the theorem in coordinates | 1 | `T8A.harmonic9` |

The certificates of the statements (C1) and (C5) consist of a few numbers each: a polynomial of degree 3
with a matrix of order 3 and five Bernstein coefficients for the separation, and two sets of twelve
constants for the Gram–Schmidt cells. They are contained, with their proofs, in the library files
[LeanCode/S3N9/Separation.lean](../LeanCode/S3N9/Separation.lean) and
[LeanCode/S3N9/GramSchmidtCells.lean](../LeanCode/S3N9/GramSchmidtCells.lean).

## Data modules and statement modules

A **data module** contains natural numbers in hexadecimal notation (`hex% "…"`), a few definitions that
arrange them, and theorems of the form `check data = true := by decide +kernel`: the Lean kernel evaluates
the checker on the data. There are 402 data modules with 5,426 such theorems. A data module imports the
checkers and the reader of the numerals only, and no file of Mathlib.

A **statement module** applies the soundness theorems of the library to the checks of the data modules and
obtains statements about configurations of points. Comparisons of small data, such as the numbers of points
of the classes, are evaluated by the kernel there as well (591 evaluations). It ends with a test that its theorems depend on the
axioms `propext`, `Classical.choice` and `Quot.sound` only (`#guard_msgs in #print axioms …`). The four
statement modules are the files to read:

| Module | Contents |
| --- | --- |
| [Typed/T8S.lean](Typed/T8S.lean) | For each of the 111 certificates the theorem `energy`, on the domain that the certificate declares, and for each of its claims the theorem `energy_claim<k>`, whose hypotheses are intervals for the inner products alone. |
| [VirtualRoot/T8VS.lean](VirtualRoot/T8VS.lean) | For each of the 11 certificates the theorem `energy`, on the piece of the certificate. |
| [Sharp/I3S.lean](Sharp/I3S.lean) | The theorems `energy` and `contacts` of the sharp certificate. |
| [Theorem/T8A.lean](Theorem/T8A.lean) | For every claim and every leaf of the analytic part, the comparison with a certificate and the bound that follows; then `T8A.minimum9` and `T8A.harmonic9 : S3N9.Harmonic9`. |

Every Lean file below this folder is a module of the Lake library `Certificates`; the module
`Certificates.Typed.W0` is the file `Typed/W0.lean`. The header of a module names the program that wrote
it. These programs are not part of this repository, and nothing in the verification depends on them: Lean
checks the modules as they are.

## The modules of a certificate

| Folder | Module | Contents |
| --- | --- | --- |
| `Typed` | `W<i>C` | The parameters, the rooted blocks with their Gram matrices (`gram<a>_<k>`), the domain, and the sign conditions of the pair types (`signs_ok`). |
| | `W<i>` | The triple types with the identity and the positivity of each (`ok<abc>`), the bound (`bound_ok`), the domain (`dom_ok`) and the claims (`claim<k>_ok`). |
| | `WL0C`, `WL0` | The same for the certificate of the first cell, which has one class of nine points. |
| `VirtualRoot` | `<leaf>C` | The data that all identities share, the identities of the labels (`labels_ok`) and the bound (`bound_ok`). |
| | `<leaf>R<i>` | The identity of the record type `i` (`ok<i>`). |
| | `<leaf>M` | The identities of the minorants (`mok<i>`) and the checks of the classes of the labels (`cok<l>`). |
| `Sharp` | `I3C`, `I3R<i>`, `I3M` | The same for the sharp certificate, whose identities hold exactly; `I3M` also contains the checks of the contacts (`ct<i>`). |

The leaves of the virtual-root certificates are `QW0`, `WX1` to `WX5` and `WY1` to `WY5`.

## Tables

| File | Contents |
| --- | --- |
| [Typed/certificates.tsv](Typed/certificates.tsv) | One line for each of the 111 certificates: its module, its degree, the sizes of its classes, the numbers of its triple types, sign conditions and claims, and its bound. |
| [Typed/claims.tsv](Typed/claims.tsv) | One line for each of the 120 claims: its cell, its theorem, the sizes of its classes and the intervals of its pair types. |
| [VirtualRoot/certificates.tsv](VirtualRoot/certificates.tsv) | One line for each of the 11 certificates: its leaf, its theorem, its guards, its record types and its bound. |

The smallest bound of a typed certificate is $35/2 + 9.2\cdot10^{-5}$, and the smallest bound of a
virtual-root certificate with margin is $35/2 + 2.36\cdot10^{-4}$. The tables are not read by Lean.
