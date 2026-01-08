# Erdős Problem 13 Formalization

This directory contains the formalization of **Erdős Problem 13** in Lean 4.

## Problem Statement

Let $A \subseteq \{1, \dots, N\}$ be such that there are no $a, b, c \in A$ such that $a \mid (b+c)$ and $a < \min(b, c)$. 
Prove that $|A| \le N/3 + O(1)$.

## Status

- **Source:** [Erdős Problems Database](https://teorth.github.io/erdosproblems/13)
- **Problem Number:** 13
- **OEIS:** [A002264](https://oeis.org/A002264)
- **Status:** Proved (but not previously formalized in Lean according to the database).
- **Formalization:** The statement is formalized in `ErdosProblem13.lean`. The proof is currently left as `sorry`.

## Note

The problem was identified from the list of proved but unformalized problems. The statement was retrieved from the website and translated into Lean.
