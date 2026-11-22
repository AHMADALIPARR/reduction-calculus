# Reduction Calculus

A Lean 4 formalisation of two primitives and the theorem family built from
them:

* **`DeepReduction`** — a reduction step followed by a collapse;
* **`ClosedLift`** — the canonical, choice-free lift of `a : A i` along `φ`.

Everything is core Lean 4. There is no Mathlib dependency, no `sorry`, and
no axioms beyond `propext` in a single `Fin.induction` lemma.

```
Lean 4.36.0
lake build          # 14 jobs, no warnings
```

## Status

| Check | Result |
| --- | --- |
| `lake build` | succeeds, no warnings |
| `sorry` / `admit` / `axiom` in sources | none |
| `#print axioms Nest19`, `Nest37`, `nest`, `deepReduce_preserves` | no axioms |
| `Nest` family | 19 / 19 theorems (`Nest19` … `Nest37`) |
| Source proof body (`Nest19`) | elaborates unchanged (`Nest19_source`) |

## The two primitives

```lean
def DeepReduction {α β : Sort _} (f : α → β) (g : β → β) (x : α) : β :=
  g (f x)

def ClosedLift {ι : Sort _} (A B : ι → Type _) (φ : ∀ i, A i → B i)
    (i : ι) (a : A i) : ∃ b : B i, b = φ i a :=
  ⟨φ i a, rfl⟩
```

`DeepReduction f g x` applies the reduction `f` to `x`, then collapses the
result with `g`. The `Nest` proofs pass `g = id`, where the collapse is the
identity and `DeepReduction f id x` is definitionally `f x`
(`DeepReduction_id`).

The collapse slot is what makes the step *deep* rather than a plain
application. `deepReduce f g n x` performs `n` steps of `f` and collapses
once, and the one-step primitive is its `n = 1` case:

```lean
theorem deepReduce_one (f g : α → α) (x : α) :
    deepReduce f g 1 x = DeepReduction f g x
```

`ClosedLift` returns the `∃`-statement that concludes every `Nest`
theorem, with the canonical witness. It is *closed* because the fibre over
`φ i a` is a subsingleton:

```lean
theorem ClosedLift_subsingleton (a : A i) :
    Subsingleton { b : B i // b = φ i a }
```

so the lift makes no choice, no choice principle is involved, and any two
witnesses are equal (`ClosedLift_uniq`).

## Semantics

The development states what the primitives mean rather than only how they
are written.

**Reduction is a reflexive–transitive closure.** `Reduces r a b` means "`a`
reduces to `b` in zero or more `r`-steps"; it is closed under composition
(`Reduces.trans`), monotone in the step relation (`Reduces.mono`), and
stable under prefixing and appending steps.

**Implication is the canonical step.** `ImpStep p q := p → q`, and

```lean
theorem reduces_imp (h : Reduces ImpStep p q) : p → q
```

is the soundness theorem: a chain of implications is an implication.
Reduction cannot manufacture a conclusion that does not follow.

**Invariants are preserved.** If every step and the collapse preserve `p`,
then every deep reduction does:

```lean
theorem deepReduce_preserves (hf : ∀ x, p x → p (f x)) (hg : ∀ x, p x → p (g x)) :
    ∀ n x, p x → p (deepReduce f g n x)
```

and in a `ReductionSystem` the same statement is
`ReductionSystem.invariant`.

**The `Nest` schema.** One theorem covers the whole family:

```lean
theorem nest (h : Reduces ImpStep p q) (hp : p) (i : ι) (a : A i) :
    q ∧ ∃ b : B i, b = φ i a
```

A chain of implications from `p` to `q`, a proof of `p`, and an element
`a : A i` give `q` together with the closed lift of `a`. Every `Nest k` is
this theorem applied to a chain of length `k`.

**The conclusion is closed.** `nest_lift_unique` shows any two witnesses of
the `Nest` conclusion are equal, so the lift half carries no information
beyond the value `φ i a`. The `Nest` theorems are therefore exactly
"the chain reduces, and the lift exists" — nothing more is claimed.

## The `Nest` family

`Nest19` … `Nest37` are chains of implications of increasing length, each
concluding with the closed lift. The proposition variables follow a fixed
37-name alphabet — `P … Z`, then `AA … ZZ` — which is exactly the alphabet
used by the source proofs.

| Theorem | Propositions | Implications | Conclusion |
| --- | --- | --- | --- |
| `Nest19` | `P … HH` (19) | 18 | `∃ b : B i, b = φ i a` |
| `Nest20` | `P … II` (20) | 19 | same |
| … | … | … | … |
| `Nest37` | `P … ZZ` (37) | 36 | same |

Each theorem is generated, not hand-written, and every proof is the same
two lines:

```lean
have hchain : Reduces ImpStep P HH :=
  Reduces.step h1 <| … <| Reduces.refl HH
exact (nest A B φ hchain hp i a).2
```

so the family is an instance of one lemma rather than 19 independent
arguments. Regenerate with:

```sh
python3 scripts/gen_nest.py > ReductionCalculus/Nest.lean
```

## Layout

| File | Contents |
| --- | --- |
| `ReductionCalculus/Core.lean` | `DeepReduction`, `deepReduce`, `iterateStep`, `ClosedLift`, and their lemmas |
| `ReductionCalculus/Chain.lean` | `Reduces`, `ImpStep`, `reduces_imp`, `Chain` |
| `ReductionCalculus/Semantics.lean` | `ReductionSystem`, `invariant`, the `nest` schema |
| `ReductionCalculus/Nest.lean` | `Nest19` … `Nest37` (generated) |
| `ReductionCalculus/Examples.lean` | the source `Nest19` proof, plus concrete computations |
| `scripts/gen_nest.py` | generator for `Nest.lean` |
| `docs/PROVENANCE.md` | what was transcribed, what was regenerated, and why |

## Build

```sh
lake build
```

The toolchain is pinned in `lean-toolchain` to `leanprover/lean4:v4.36.0`.
Nothing outside Lean's prelude is imported.

To check a single theorem:

```sh
cat > /tmp/check.lean <<'EOF'
import ReductionCalculus
#print axioms ReductionCalculus.Nest37
EOF
lake env lean /tmp/check.lean
```

## Provenance and scope

The theorems come from a `Nest19` … `Nest37` development supplied as source
text. That text was partially truncated, so the family was regenerated from
its shared pattern; see `docs/PROVENANCE.md` for exactly what was
transcribed and what was not.

Three modernisations were required to build on Lean 4.36:

1. `{ι : Type*}` → `{ι : Type _}` — `Type*` no longer parses in Lean 4.36.
2. The leading `intro` was dropped from the `Nest19` proof body; the goal is
   an `∃`, so there is nothing to introduce.
3. `Chain` and `Reduces` lemmas are stated with `∀ {a b c}` in the
   signature so recursive calls generalise properly.

This project does **not** claim to be a model of any particular calculus
beyond implication reduction, does not reproduce the original proofs
byte-for-byte, and does not add automation beyond core tactics
(`rfl`, `simp`, `decide`, `omega`-free). The `Nest` conclusions are closed,
so they should not be read as carrying information beyond `φ i a`.
