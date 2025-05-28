# Non-idempotent intersection type system

Weakening, renaming, substitution, and subject reduction properties for the non-idempotent intersection type system.

- `ulc.v`
  untyped lambda-calculus
- `nitlc.v`
  non-idempotent intersection type system
- `facts.v`
  generic facts
- `ulc_facts.v`
  facts about the untyped lambda-calculus
- `bag_equiv_facts.v`
  facts about type environment equivalence up to type permutation
- `nitlc_facts.v`
  facts about the non-idempotent intersection type system, including weakening, renaming, substitution, and subject reduction properties.

Verification instructions using Coq 9.0
```
git clone git@github.com:tudo-seal/non-idempotent-intersection.git
cd non-idempotent-intersection
make
```
