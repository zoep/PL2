# LLM Playground

A space for experimenting in class with LLMs, formal verification and programming languages.

### 1. Merge sort ([`mergesort.v`](mergesort.v), 23/10/2026)

**Prompt:** Can you write an efficient sorting function on lists in Rocq and prove it correct? Do it in a new file.

**Model:** Claude Opus 5.5, effort max

**Result:** merge sort on `list nat`, with a proof (`msort_correct`) that the output is sorted and a permutation of the input. The proof uses no axioms.
