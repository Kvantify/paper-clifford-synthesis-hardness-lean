# Clifford synthesis complexity

This Lean project formalizes NP-completeness of Clifford gate-count
minimization with full qubit connectivity and no ancillas. Circuits act on
binary symplectic tableaux, with generator signs in the weighted model.
The hardness reduction starts with
Frontier's positive exact-one-in-three SAT hardness theorem and uses a
specified-endpoint Hamiltonian path problem on induced grid graphs.
[Clifford synthesis is NP-complete](https://arxiv.org/abs/2610.40886)

## Results

Lean Comparator checks the declarations in [Specification.lean](Specification.lean).
The languages and encodings are in
[DecisionProblems.lean](CliffordFrontier/DecisionProblems.lean) and
[SignedProblem.lean](CliffordFrontier/SignedProblem.lean).

| Decision problem | Target encoding | Result |
| --- | --- | --- |
| CNOT count with free single-qubit Cliffords, with or without free SWAPs | Block-diagonal tableau | NP-complete |
| CNOT count with free single-qubit Cliffords, with or without free SWAPs | Three-block target | NP-complete |
| CNOT-only synthesis | Block-diagonal tableau | NP-complete |
| CNOT count with free single-qubit Cliffords, with or without free SWAPs | Full symplectic tableau | NP-complete |
| Fixed two-qubit gate family with free single-qubit Cliffords, with or without free SWAPs | Full symplectic tableau | NP-complete |
| Fixed single-qubit and two-qubit gate costs, with or without free SWAPs | Full signed tableau | NP-complete |

The phase-free gate-family results assume a gate locally Clifford-equivalent
to CNOT. The signed results assume that CNOT itself is available and that the
fixed two-qubit gate cost is positive. The single-qubit gate cost may be zero.
The gate-family and signed results also cover the restrictions to three-block
targets `diag(A, (A⁻¹)ᵀ)` with `A` lower unitriangular and `(A - I)³ = 0`.
The signed restriction uses zero generator signs.

The NP verifiers check the full target tableau, including generator signs in
the signed model. A quadratic CNOT synthesis bound, compression of free local
gates, and a bound on the number of final SWAPs give polynomial-length
certificates even when the binary budget is large.

## Build and verify

Install [elan](https://github.com/leanprover/elan). The toolchain file
selects the version of Lean, Lake, and Comparator. Lake fetches
[cslib-frontier](https://github.com/cslib-community/cslib-frontier) and its
transitive dependencies at the revisions in `lake-manifest.json`.

Build the proof library from this directory.

```sh
lake build
```

Run the checked examples and the library-wide axiom audit.

```sh
lake test
```

The [checked examples](CliffordTests/Synthesis.lean) use ordinary imports to
exercise the phase-free and signed decoders and instantiate the signed
NP-completeness result with explicit gate weights and an available CNOT.

For Comparator verification on Linux, install
[Bubblewrap](https://github.com/containers/bubblewrap) and make sure `bwrap` is
on your `PATH`. `lake comparator` invokes `bwrap` automatically to build and
export the specification and proof modules separately in isolation.

```sh
lake comparator
```

Comparator compares the selected statements and their definitions and checks
the proofs in Lean's kernel. The only permitted axioms
are `propext`, `Classical.choice`, and `Quot.sound`.
The admitted statements in `Specification.lean` are Comparator inputs.
The proof library and its tests build independently of that file.

For source and style checks, run the following after Lake has fetched the dependencies.

```sh
python3 scripts/check_source.py
lake lint
lake exe lint-style
```

The source check verifies module headers, imports, bibliography entries,
and proof hygiene using the pinned Frontier checker. See the
[Frontier contribution guide](https://github.com/cslib-community/cslib-frontier/blob/main/CONTRIBUTING.md)
for Lean API and proof conventions.

## Source layout

| Directory | Contents |
| --- | --- |
| `CliffordFrontier` | Decision languages, verifiers, and complexity theorems |
| `CliffordSynthesis` | Gate semantics, symplectic algebra, and the grid-to-synthesis reduction |
| `GridProblems` | Induced grid graphs and their Hamiltonian path and cycle languages |
| `GridHardness` | Positive one-in-three SAT reduction and grid construction |
| `CliffordComplexity` | Program combinators with Frontier polynomial-time certificates |

## License and references

The source is released under the [Apache License 2.0](LICENSE). Mathematical
sources cited in the Lean files are listed in [references.bib](references.bib).

The bounded transvection argument in
[SynthesisBound.lean](CliffordFrontier/SynthesisBound.lean) uses portions of
Mathlib's matrix elimination proof, copyright 2021 Sébastien Gouëzel.
