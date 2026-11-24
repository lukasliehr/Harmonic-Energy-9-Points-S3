# AnalyticArguments

The arguments of the proof.

| File | Contents |
| --- | --- |
| [analytic_arguments.pdf](analytic_arguments.pdf), [analytic_arguments.tex](analytic_arguments.tex) | The proof in the form that Lean verifies: the theorem, the statements that Lean takes from the certificates, and the analytic arguments that lead from these statements to the theorem, with the names of their Lean theorems. |

The proof has a computational part and an analytic part.

* Section 2 states the eight statements (C1) to (C8) of the computational part: the separation of
  the points, the typed three-point certificates with their claims, the constants of the
  Gram–Schmidt cells, the virtual-root certificates, the sharp certificate and the contacts. It
  states the two bounds behind the certificates as theorems about points of the three-sphere and
  describes what the Lean kernel checks. The certificates are those of
  [Certificates](../Certificates).
* Section 3 contains the analytic arguments, the statements (A1) to (A11): the energy of the
  minimizer; near pairs and chains; the 55 cells and their claims; the last cell with its ring
  split, its selected edges and its core; the Gram–Schmidt frame and the cell lemma; the lower
  bound; the case of equality. The Lean files are those of
  [LeanCode/S3N9](../LeanCode/S3N9).
* Section 4 lists the parts of the proof in Lean.
