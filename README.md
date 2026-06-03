# Infinite tetrads of congruent factorials

This repository contains a Lean formalisation of the main theorem of the manuscript
*Infinite tetrads of congruent factorials* by Octavio A. Agustín-Aquino and
José Hernández Santiago.

The mathematical blueprint and manuscript are human-written. The Lean file
formalises the main construction and verifies the unbounded form of the theorem:

```lean
∀ N : ℕ, ∃ p : ℕ, N < p ∧ HasTetrad p
