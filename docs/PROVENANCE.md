# Provenance

## What the source supplied

The `Nest` family arrived as Lean source text: nineteen theorems,
`Nest19` … `Nest37`, all of the same shape — a chain of `k` propositions
with `k - 1` implications `h1 … h(k-1)`, a hypothesis `hp` for the first
proposition, and the conclusion

```lean
∃ b : B i, b = φ i a
```

Two primitives are used but not defined in that text. Their call shapes
pin their signatures exactly:

| Source usage | Consequence |
| --- | --- |
| `DeepReduction h2 (fun r => r) hq`, with `h2 : Q → R`, `hq : Q`, result `R` | `DeepReduction : (α → β) → (β → β) → α → β` |
| `match ClosedLift A B φ i a with \| ⟨b, rfl⟩ => …` | `ClosedLift` must reduce to `⟨φ i a, rfl⟩` |
| `exact ClosedLift A B φ i a` in a goal `∃ b, b = φ i a` | `ClosedLift`'s type must be that `∃`-statement, definitionally |
| `A B : ι → Type*` | written for a Lean version where `Type*` still parsed |

Those four observations are the whole specification the definitions in
`ReductionCalculus/Core.lean` were written against. `Nest19_source` in
`ReductionCalculus/Examples.lean` is the check that they are right: it is
the source proof body, transcribed, and it elaborates.

## What was transcribed and what was regenerated

The source text was partially truncated when it was supplied. Per theorem:

| Theorem | State in the supplied text | In this repo |
| --- | --- | --- |
| `Nest19` | header and full proof body | body transcribed as `Nest19_source`; statement also in `Nest.lean` |
| `Nest20` | header, then the body jumps in mid-chain | regenerated |
| `Nest21` | header and full proof body | regenerated |
| `Nest22` | header and full proof body | regenerated |
| `Nest23` – `Nest30` | header and the tail of the body only | regenerated |
| `Nest31` | header and full proof body | regenerated |
| `Nest32` | header and full proof body | regenerated |
| `Nest33` | header and full proof body | regenerated |
| `Nest34` | not present | regenerated |
| `Nest35` | header and full proof body | regenerated |
| `Nest36` | header and full proof body | regenerated |
| `Nest37` | header and full proof body | regenerated |

No generated proof is claimed to be byte-identical to an original. The
statements, however, follow the source's naming and shape exactly: same
proposition alphabet (`P … Z`, `AA … ZZ`), same hypothesis names `h1 …`,
same `hp`/`i`/`a` parameters, same conclusion.

## Why the proofs were regenerated rather than copied

Two reasons.

1. The truncated bodies cannot be reconstructed faithfully; guessing at
   them would produce proofs that look original but are not.
2. The family is one lemma applied nineteen times. `nest` in
   `ReductionCalculus/Semantics.lean` states the shared content once, and
   each `Nest k` is that lemma applied to its own chain. Copying nineteen
   independent scripts would obscure that.

The source proof style is preserved where it can be checked: `Nest19_source`
keeps one `have` per position, uses `DeepReduction … (fun x => x)` for the
steps, and ends with the `match ClosedLift … with | ⟨b, rfl⟩` pattern.

## Modernisations

| Change | Reason |
| --- | --- |
| `{ι : Type*}` → `{ι : Type _}` | `Type*` no longer parses in Lean 4.36 |
| leading `intro` dropped from the `Nest19` body | the goal is `∃ b, b = φ i a`; there is nothing to introduce, and the tactic is a no-op or an error depending on version |
| `Chain` / `Reduces` lemmas take `∀ {a b c}` in the signature | recursive calls must generalise the index, not capture the enclosing one |

Nothing else in the transcribed body was altered.

## Verification

Run on the machine that produced this repository:

```
Lean 4.36.0, aarch64-unknown-linux-gnu, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9
lake build                      -> Build completed successfully (14 jobs)
grep -rn "sorry|admit|axiom"    -> no matches
#print axioms Nest19           -> does not depend on any axioms
#print axioms Nest37           -> does not depend on any axioms
#print axioms Nest19_source    -> does not depend on any axioms
#print axioms nest             -> does not depend on any axioms
#print axioms Chain.last       -> depends on axioms: [propext]
```

`propext` appears only through `Fin.induction` in `Chain.last`; every other
checked declaration is axiom-free.
