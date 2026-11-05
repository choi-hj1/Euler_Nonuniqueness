# Cubical Sperner and Brouwer foundations

The modules in `EulerNonuniqueness/General/Brouwer/` adapt the cubical-Sperner proof of the unit-cube fixed-point theorem from [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4), source commit `11a9f041246d28374edae384241757f9a0cbd5e4`. The upstream project distributes this code under the [MIT license](LICENSE), introduced in upstream commit `770940ddf9878cf61952ed53d910b92bca841838`.

The adaptation isolates declarations in `EulerNonuniqueness.General.Brouwer`, updates imports, and ports the proofs to the project's pinned Lean and Mathlib versions. Upstream's implicit-parameter elaboration is local to these modules. These are proof-bearing source modules, not assumed fixed-point axioms; their statements and dependencies undergo the same kernel and axiom checks as the Euler development.
