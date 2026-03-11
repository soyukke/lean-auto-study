# AutoStudy

AutoStudy is a Lean 4 + Mathlib project for formalizing mathematics and physics.

## Contents

### Mathematics
- **Irrationality of `sqrt(2)`** (`AutoStudy/Sqrt2Irrational.lean`) - a proof using Mathlib's `irrational_sqrt_two` and a direct proof by infinite descent

### Classical Mechanics
- **One-dimensional energy conservation** (`AutoStudy/EnergyConservation.lean`) - a proof that total energy satisfies `dE/dt = 0` under Newton's equation of motion

### Density Functional Theory (DFT)
This repository includes a growing Lean formalization of the mathematical foundations of density functional theory.

- **Basic definitions** (`AutoStudy/DFT/Basic.lean`) - inner products, expectation values, eigenstates, and electron density
- **Explicit Hamiltonians** (`AutoStudy/DFT/ExplicitHamiltonian.lean`) - structured `T + V_ext + V_ee` Hamiltonians and expectation decomposition
- **Hohenberg-Kohn first theorem** (`AutoStudy/DFT/HohenbergKohn.lean`) - uniqueness-style results for external potentials and explicit-Hamiltonian variants
- **Variational principle** (`AutoStudy/DFT/VariationalPrinciple.lean`) - ground-state minimization, strict inequalities for non-degenerate states, and Rayleigh-Ritz style lemmas
- **Hohenberg-Kohn second theorem** (`AutoStudy/DFT/HohenbergKohnSecond.lean`) - energy minimization, `v`-representability, and abstract constrained-search / Levy-Lieb style interfaces
- **Kohn-Sham equations** (`AutoStudy/DFT/KohnSham.lean`) - Kohn-Sham systems, density positivity, particle-number conservation, effective potentials, self-consistency, and Euler-Lagrange style stationarity conditions
- **Three-dimensional many-body DFT layer** (`AutoStudy/DFT/ManyBody3D.lean`) - complex-valued wavefunctions, antisymmetry, `N`-representability, concrete external-energy terms, Hartree-style energy, and abstract/concrete bridges for many-body HK theory
- **Self-adjoint operators** (`AutoStudy/DFT/SelfAdjoint.lean`) - self-adjointness, orthogonality of eigenstates, and matrix-element properties
- **Hellmann-Feynman theorem** (`AutoStudy/DFT/HellmannFeynman.lean`) - energy derivatives from perturbation expectations and eigenvalue perturbation relations
- **Exchange-correlation functionals** (`AutoStudy/DFT/ExchangeCorrelation.lean`) - the `XCFunctional` structure and local / semi-local functionals
- **Coordinate scaling** (`AutoStudy/DFT/Scaling.lean`) - density scaling maps, composition rules, and scaling constraints
- **Functional derivatives** (`AutoStudy/DFT/FunctionalDerivative.lean`) - Gateaux derivatives, linear functionals, additivity, and scalar multiplication
- **Exact constraints** (`AutoStudy/DFT/ExactConstraints.lean`) - nonpositivity, Lieb-Oxford bounds, self-interaction conditions, and uniform-density limits
- **Sum rules** (`AutoStudy/DFT/ExactConstraints/SumRules.lean`) - exchange/correlation hole sum rules and hole nonpositivity
- **Asymptotic properties** (`AutoStudy/DFT/ExactConstraints/Asymptotic.lean`) - long-range behavior `v_xc -> -1/r`, density limits, asymptotic limitations of local potentials, and asymptotically corrected potentials
- **Size consistency** (`AutoStudy/DFT/ExactConstraints/SizeConsistency.lean`) - size consistency, translation invariance, convexity, and positive homogeneity
- **LDA** (`AutoStudy/DFT/LDA.lean`) - local density approximation, nonpositivity results, and compatibility with Lieb-Oxford bounds
- **GGA** (`AutoStudy/DFT/GGA.lean`) - generalized gradient approximation, reduction to LDA, and bounded enhancement factors
- **Constraint comparison table** (`AutoStudy/DFT/Functionals/Comparison.lean`) - type-level comparison of exact constraints for LDA and GGA
- **ACG functional** (`AutoStudy/DFT/Functionals/NewFunctional.lean`) - a GGA + nonlocal-correction functional with proofs of six exact constraints
- **Model potentials** (`AutoStudy/DFT/ModelPotential.lean`) - a framework for defining potentials directly without going through an energy functional
- **LB94** (`AutoStudy/DFT/Functionals/LB94.lean`) - the van Leeuwen-Baerends asymptotically corrected potential, with reduction and asymptotic results
- **LB94 asymptotics** (`AutoStudy/DFT/Functionals/LB94Asymptotic.lean`) - a complete proof of `-1/r` asymptotic decay for exponentially decaying densities
- **Nonlocal correction examples** (`AutoStudy/DFT/Functionals/NLCExamples.lean`) - several concrete instances of `NonLocalCorrection` and consistency checks
- **Variational nonlocal correction** (`AutoStudy/DFT/Functionals/PhysicalNLC.lean`) - a complete variational proof for a discrete-Laplacian-style nonlocal correction
- **Kernel-based nonlocal functional** (`AutoStudy/DFT/Functionals/KernelNLC.lean`) - a complete variational proof for a kernel-based nonlocal correction using Fubini-style symmetry arguments

The current development builds without `sorry`.

## Build

```bash
nix develop --command lake build
```

## Dependencies

- Lean 4 (`v4.29.0-rc4`)
- Mathlib (`v4.29.0-rc4`)
