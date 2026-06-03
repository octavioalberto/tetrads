# Infinite tetrads of congruent factorials

This repository contains a Lean formalisation of the main theorem of the manuscript
*Infinite tetrads of congruent factorials* by Octavio A. Agustín-Aquino and
José Hernández Santiago.

The mathematical manuscript is human-written, but the main argument was discovered
using ChatGPT 5.5 Pro. The Lean file formalises the main construction and verifies
the unbounded form of the theorem:

```lean
∀ N : ℕ, ∃ p : ℕ, N < p ∧ HasTetrad p
