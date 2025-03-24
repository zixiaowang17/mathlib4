# Plan
This is a plan file on what is being learnt by playing with lean4 with the goal of contributing to semiparametric inference

# Formalization of semiparametric inference
- Probability Theory & Measure Theory – for defining statistical models.
- Functional Analysis & Hilbert Spaces – since semiparametric efficiency relies on functionals, gradients, and tangent spaces.
- Differentiation & Optimization – for influence functions and efficiency bounds.

# Recommended Sections to Read in Mathematics in Lean
- Logic & Proof Techniques (Chapter 3)
    Section 3.1 (Implication and Universal Quantifier)
    Section 3.4 (Conjunction and Iff)
    Section 3.5 (Disjunction)


- Linear Algebra & Hilbert Spaces (Chapter 9)
    9.1 (Vector Spaces and Linear Maps)
    9.2 (Subspaces and Quotients)
    9.3 (Endomorphisms)
    9.4 (Bases and Dimension)

- Measure Theory & Integration (Chapter 12)
    12.2 (Measure Theory)
    12.3 (Integration)


- Differentiation (Chapter 11)
    11.1 (Elementary Differential Calculus)
    11.2 (Differential Calculus in Normed Spaces)

- Algebraic Structures (Chapters 6-8)
    6.2 (Algebraic Structures) – Understanding functionals as part of a structure.
    8.2 (Rings) – Some function spaces involve operations on algebraic structures.

# Next Steps in Lean 4 for Semiparametric Inference

Define a statistical model as a probability space with a measure.
Formalize pathwise differentiability using functional derivatives.
Construct EIFs as elements of a Hilbert space.
Implement one-step estimators using functional calculus.
