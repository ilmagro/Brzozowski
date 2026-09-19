# Summary
The goal of this repository is to prove the [soundness](Brzozowski.agda#L169-L171) and
the [completeness](Brzozowski.agda#L173-L175) of the Brzozowski derivative in Agda.
The proof is generalized on `Set` (e.g. `Nat`, `Char`) on which decidable equality is defined.
Furthermore, the proof is cubical-compatible and
for this reason some lemmas do not use pattern matching but a custom type
(like [`null?-+ᴿ`](Brzozowski.agda#L56-L73) and [`null?-*ᴿ`](Brzozowski.agda#L75-L92)).

**Closure** and **idempotency** of the **Kleene star** are provided
[too](String/Properties.agda#L14-L30), but are not required for the proof.

## Requirements
**Agda** (agda-stdlib is not required).
