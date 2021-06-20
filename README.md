# A Henkin-style completeness proof for the modal logic S5

This repository contains a recent formalization of a Henkin-style completeness proof for the strongest of the five systems of modal logic proposed by Lewis and Langford [2], namely, S5, using the Lean theorem prover. The proof is close to that of Hughes and Cresswell [1], except that it is given for a system based on a different choice of axioms. 

The proof here is constructed for a Hilbert-style axiomatic system that can be described as a Mendelson system augmented with axiom schemes for K, T, S4, B, and the necessitation rule as rule of inference (thus a completeness proof for those weaker normal modal systems can be easily obtained by commenting irrelevant lines). The language of the theory has the false and implication as the only primitive logical connectives and necessity as the only primitive modal operator. 

## References

[1] George Edward Hughes and Max J Cresswell. A new introduction to modal logic. Psychology Press, 1996.

[2] Clarence Irving Lewis and Cooper Harold Langford. Symbolic logic. the century company, new york, 1932, 1959.
