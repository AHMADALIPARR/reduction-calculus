# Reduction Calculus

[![build](https://github.com/AHMADALIPARR/reduction-calculus/actions/workflows/build.yml/badge.svg)](https://github.com/AHMADALIPARR/reduction-calculus/actions/workflows/build.yml)
[![Lean](https://img.shields.io/badge/Lean-4.36.0-3178c6?style=flat-square)](lean-toolchain)
[![theorems](https://img.shields.io/badge/theorems-19%2F19-success?style=flat-square)](ReductionCalculus/Nest.lean)
[![sorry](https://img.shields.io/badge/sorry-free-success?style=flat-square)](docs/PROVENANCE.md)
[![axioms](https://img.shields.io/badge/axioms-propext%20only-yellow?style=flat-square)](docs/PROVENANCE.md)
[![dependencies](https://img.shields.io/badge/dependencies-0-lightgrey?style=flat-square)](lake-manifest.json)
[![version](https://img.shields.io/badge/version-0.1.0-blueviolet?style=flat-square)](https://github.com/AHMADALIPARR/reduction-calculus/releases/tag/v0.1.0)

**A two-rule calculus for chains, with two mathematical primitives, in core
Lean 4.**

The whole development is one schema (`nest`), two rules — chain composition
and closed-lift elimination — and nineteen instances (`Nest19` … `Nest37`).
Every theorem is a consequence of those two rules; nothing else is used.

No Mathlib. No `sorry`. No axioms beyond `propext`, and only in the three
`Chain` lemmas that go through `Fin.induction`.

```lean
lake build   -- 14 jobs, no warnings
```

---

## At a glance

| Declaration | What it says | File |
| --- | --- | --- |
| `DeepReduction f g x` | `g (f x)` — one step, then collapse | `Core.lean` |
| `iterateStep f n` | monoid action of `(Nat, +, 0)` on `α → α` | `Core.lean` |
| `deepReduce f g n` | `g ∘ iterateStep f n` — `n` steps, then collapse | `Core.lean` |
| `deepReduce_preserves` | invariants survive every deep reduction | `Core.lean` |
| `ClosedLift A B φ i a` | `∃ b, b = φ i a`, with the canonical witness | `Core.lean` |
| `ClosedLift_subsingleton` | the fibre is a subsingleton ⇒ no choice | `Core.lean` |
| `Reduces r a b` | reflexive–transitive closure of `r` | `Chain.lean` |
| `ImpStep p q` | implication as a one-step reduction | `Chain.lean` |
| `reduces_imp` | soundness: a chain of implications is an implication | `Chain.lean` |
| `reduces_imp_iff` | completeness: `Reduces ImpStep` **is** `→` | `Chain.lean` |
| `Chain P` | the `Fin`-indexed `have`-chain as an object | `Chain.lean` |
| `Chain.toReduces` | a chain *is* a reduction | `Chain.lean` |
| `Chain.apply` | reaching position `k` = reducing to position `k` | `Chain.lean` |
| `ReductionSystem.invariant` | invariants survive reduction | `Semantics.lean` |
| `nest` | the schema: reduction ∧ closed lift | `Semantics.lean` |
| `Nest19` … `Nest37` | nineteen instances | `Nest.lean` |

---

## 1. The calculus

### 1.1 Two rules

The `Nest` proofs contain exactly two kinds of step.

**Chain rule.** Unary eliminations compose:

```
        p → q        q → r
        ─────────────────             (Reduces.trans, Reduces.single)
              p → r
```

In the source this is the `have`-chain: `hq`, `hr`, `hs`, … each consuming
the previous. In Lean it is `Reduces`, whose `trans` is composition and
whose `single` is one step.

**Closed-lift rule.** A relation that is total, functional, and has
subsingleton fibres may be introduced and eliminated definitionally:

```
        b = φ i a
       ───────────                    (fibre is a subsingleton)
      ∃ b, b = φ i a
```

In the source this is the `match ClosedLift … with | ⟨b, rfl⟩` at the end of
each proof.

Everything in `Nest.lean` is these two rules applied in sequence. There is
no third ingredient.

### 1.2 Why the `match` computes

```lean
match ClosedLift A B φ i a with
| ⟨b, rfl⟩ => ...
```

This is **not** case analysis. `ClosedLift A B φ i a` is *definitionally*
`⟨φ i a, rfl⟩`, so the match has exactly one possible branch and reduces
without inspecting anything:

```lean
theorem ClosedLift_def … : ClosedLift A B φ i a = ⟨φ i a, rfl⟩ := rfl
```

The same definitional fact is why

* `exact ClosedLift A B φ i a` proves the goal `∃ b, b = φ i a`;
* `ClosedLift_comp` holds by `rfl` (lifting twice is lifting the composite);
* the eliminator `ClosedLift_elim` is a plain `Exists.elim`.

That is the *closed* in `ClosedLift`: the eliminator is forced, so the
calculus carries no commuting conversion, no case split, and no choice
obligation at the lift.

---

## 2. The primitives

### 2.1 `DeepReduction` — one step and a collapse

```lean
def DeepReduction {α β : Sort _} (f : α → β) (g : β → β) (x : α) : β := g (f x)
```

The `Nest` proofs always pass `g = id`, where `DeepReduction f id x` is
definitionally `f x` (`DeepReduction_id`). The collapse slot is what makes
the step *deep* rather than a plain application: the iterated form applies
`g` once, at the end.

| Lemma | Statement |
| --- | --- |
| `DeepReduction_def` | `DeepReduction f g x = g (f x)` |
| `DeepReduction_id` | `DeepReduction f id x = f x` |
| `DeepReduction_congr` | respects equality of `f`, `g`, `x` |
| `DeepReduction_comp` | `DeepReduction f g (k x) = g (f (k x))` |
| `DeepReduction_collapse` | equal collapses give equal reductions |

### 2.2 `iterateStep` — the monoid action

```lean
def iterateStep (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateStep f n (f x)
```

`iterateStep` is a monoid action of `(Nat, +, 0)` on the monoid of
endofunctions `(α → α, ∘, id)`:

```lean
theorem iterateStep_zero_eq_id (f) : iterateStep f 0 = id
theorem iterateStep_comp (f) (m n) : iterateStep f (m + n) = iterateStep f n ∘ iterateStep f m
theorem iterateStep_add  (f) (m n) (x) : iterateStep f (m + n) x = iterateStep f n (iterateStep f m x)
```

### 2.3 `deepReduce` — the fold

```lean
def deepReduce (f g : α → α) (n : Nat) (x : α) : α := g (iterateStep f n x)
```

So, definitionally,

```lean
theorem deepReduce_eq_comp (f g) (n) : deepReduce f g n = g ∘ iterateStep f n
```

`n` steps of `f`, one collapse. The one-step primitive is its `n = 1` case:

```lean
theorem deepReduce_one (f g) (x) : deepReduce f g 1 x = DeepReduction f g x
```

### 2.4 Invariants

The semantic content of "reduction": a predicate preserved by the step and
by the collapse is preserved by every deep reduction.

```lean
theorem deepReduce_preserves (hf : ∀ x, p x → p (f x)) (hg : ∀ x, p x → p (g x)) :
    ∀ n x, p x → p (deepReduce f g n x)
```

with the same statement in a `ReductionSystem` as `ReductionSystem.invariant`.

### 2.5 `ClosedLift` — the canonical lift

```lean
def ClosedLift (A B : ι → Type _) (φ : ∀ i, A i → B i) (i : ι) (a : A i) :
    ∃ b : B i, b = φ i a := ⟨φ i a, rfl⟩
```

Its semantics is exactly the triple *total / functional / subsingleton
fibres*:

| Property | Lemma |
| --- | --- |
| **total** — every `a` has a lift | `ClosedLift_exists` |
| **functional** — two witnesses are equal | `ClosedLift_uniq` |
| **subsingleton fibres** — the fibre has one point | `ClosedLift_subsingleton` |
| **functorial** — lifting twice is lifting the composite | `ClosedLift_comp` |

Total + functional means the lift is the graph of a function, namely
`a ↦ φ i a`; subsingleton fibres mean the graph is *canonical*, so
selecting the witness never invokes choice.

---

## 3. Reduction

### 3.1 `Reduces` is a closure

```lean
inductive Reduces (r : α → α → Prop) : α → α → Prop
  | refl (a) : Reduces r a a
  | step : r a b → Reduces r b c → Reduces r a c
```

Algebraically, `Reduces` takes a relation to the preorder it generates:

| Property | Lemma |
| --- | --- |
| reflexivity | `Reduces.refl`, `Reduces.zero` |
| transitivity | `Reduces.trans` |
| one-step inclusion | `Reduces.single` |
| monotonicity in `r` (functoriality) | `Reduces.mono` |
| prefix / append a step | `Reduces.head`, `Reduces.tail` |

### 3.2 Implication is the canonical step

```lean
def ImpStep (p q : Prop) : Prop := p → q
```

The calculus is both sound and complete for implication chains:

```lean
theorem reduces_imp      (h : Reduces ImpStep p q) : p → q     -- soundness
theorem reduces_imp_single (h : p → q) : Reduces ImpStep p q   -- one step
theorem reduces_imp_iff  : Reduces ImpStep p q ↔ (p → q)       -- they coincide
```

`reduces_imp_iff` is the important one: **the closure of implication is
implication.** Reduction cannot manufacture a conclusion that does not
follow, and it loses nothing either — `→` is already closed under
composition.

### 3.3 `Chain` — the `have`-chain as an object

```lean
structure Chain {n : Nat} (P : Fin (n + 1) → Prop) : Prop where
  step : ∀ k : Fin n, P k.castSucc → P k.succ
```

`Chain` is the shape of the source proofs: one implication per adjacent pair
of positions. The bridge to `Reduces` is a theorem, not an analogy:

```lean
theorem Chain.toReduces_aux (c : Chain P) : ∀ k, Reduces ImpStep (P 0) (P k)
theorem Chain.toReduces     (c : Chain P) : Reduces ImpStep (P 0) (P (Fin.last n))
theorem Chain.apply         (c : Chain P) (h₀ : P 0) : ∀ k, P k
```

`apply` is not a second induction. It is `toReduces_aux` followed by
soundness:

```lean
fun k => reduces_imp (c.toReduces_aux k) h₀
```

Reaching position `k` and reducing the chain to position `k` are the same
fact. This is where the two presentations of §1.1 are identified.

---

## 4. The schema

One theorem covers the entire family:

```lean
theorem nest (h : Reduces ImpStep p q) (hp : p) (i : ι) (a : A i) :
    q ∧ ∃ b : B i, b = φ i a :=
  ⟨reduces_imp h hp, ClosedLift A B φ i a⟩
```

Read it as the two rules composed: the first component is the chain rule
discharged by soundness, the second is the closed lift. Every `Nest k` is
this theorem applied to its own chain:

```lean
have hchain : Reduces ImpStep P HH :=
  Reduces.step h1 <| … <| Reduces.refl HH
exact (nest A B φ hchain hp i a).2
```

The `.2` is not an accident of the source statement: the `Nest` conclusion
is the *lift half* only. The reduction half is proved on the way, and
`nest_reduce` / `nest_lift` expose each half separately.

**The conclusion is closed.** `nest_lift_unique` shows any two witnesses of
the `Nest` conclusion are equal, so the lift carries no information beyond
`φ i a`. The `Nest` theorems say exactly "the chain reduces, and the lift
exists" — no more.

---

## 5. The `Nest` family

`Nest19` … `Nest37` are chains of implications of increasing length, each
concluding with the closed lift. Proposition variables follow a fixed
37-name alphabet — `P … Z`, then `AA … ZZ` — exactly as in the source.

| Theorem | Propositions | Implications | Conclusion |
| --- | --- | --- | --- |
| `Nest19` | `P … HH` (19) | 18 | `∃ b : B i, b = φ i a` |
| `Nest20` | `P … II` (20) | 19 | same |
| `Nest25` | `P … NN` (25) | 24 | same |
| `Nest31` | `P … TT` (31) | 30 | same |
| `Nest37` | `P … ZZ` (37) | 36 | same |

All nineteen are generated from one template and all nineteen proofs are
the same two lines, so the family is an instance of a lemma rather than
nineteen independent arguments. Regenerate with:

```sh
python3 scripts/gen_nest.py > ReductionCalculus/Nest.lean
```

CI fails if the committed file and the generator disagree.

---

## 6. Verification

| Check | Result |
| --- | --- |
| `lake build` from clean (`rm -rf .lake`) | `Build completed successfully (14 jobs)`, no warnings |
| `sorry` / `admit` / `axiom` in sources | none |
| `#print axioms Nest19`, `Nest37`, `Nest19_source`, `nest` | no axioms |
| `#print axioms Chain.toReduces`, `Chain.apply`, `Chain.last` | `propext` |
| `Nest` family | 19 / 19 |
| Source proof body (`Nest19`) | elaborates unchanged (`Nest19_source`) |

`propext` appears only through `Fin.induction` in the three `Chain` lemmas.
Every other checked declaration is axiom-free. The workflow in
`.github/workflows/build.yml` runs the `sorry` scan, the axiom audit, and the
generator check on every push.

---

## 7. Build

```sh
lake build
```

The toolchain is pinned in `lean-toolchain` to `leanprover/lean4:v4.36.0`.
Nothing outside Lean's prelude is imported, so the build is fast and has no
dependencies to resolve.

Check a single theorem:

```sh
cat > /tmp/check.lean <<'EOF'
import ReductionCalculus
#print axioms ReductionCalculus.Nest37
EOF
lake env lean /tmp/check.lean
```

---

## 8. Layout

| File | Contents |
| --- | --- |
| `ReductionCalculus/Core.lean` | `DeepReduction`, `iterateStep`, `deepReduce`, invariants, `ClosedLift` |
| `ReductionCalculus/Chain.lean` | `Reduces`, `ImpStep`, soundness/completeness, `Chain` and its bridge |
| `ReductionCalculus/Semantics.lean` | `ReductionSystem`, `invariant`, the `nest` schema |
| `ReductionCalculus/Nest.lean` | `Nest19` … `Nest37` (generated) |
| `ReductionCalculus/Examples.lean` | the source `Nest19` body, plus concrete computations |
| `scripts/gen_nest.py` | generator for `Nest.lean` |
| `docs/PROVENANCE.md` | what was transcribed, what was regenerated, and why |
| `.github/workflows/build.yml` | build, `sorry` scan, axiom audit, generator check |

---

## 9. Design notes

The individual ingredients — reflexive–transitive closure, subsingleton
fibres, invariant preservation — are elementary. The design claim of this
repository is the *presentation*:

1. **Two rules, one schema.** The nineteen theorems are not nineteen
   results; they are one schema applied nineteen times. A reader who
   understands `nest` has understood the family.
2. **The two presentations are identified by theorem.** `Chain` (the
   `have`-chain) and `Reduces` (the closure) are related by
   `Chain.toReduces`, and `Chain.apply` is derived from it rather than
   reproved. The chain's induction *is* the reduction's transitivity.
3. **The lift's elimination is definitional.** Because `ClosedLift` reduces
   to `⟨φ i a, rfl⟩`, the `match` in the source computes, and the lift is
   canonical without choice. The calculus therefore has no commuting
   conversion at the lift.
4. **Soundness and completeness are both stated.** `reduces_imp_iff` pins
   the reduction relation to `→` from both sides, so the semantics is not
   only "reduction is safe" but "reduction is exactly implication chains".

No priority or novelty claim in the mathematical literature is made here;
the claim is about the organisation of this development, and every claim in
this README is backed by a named declaration.

---

## 10. Scope and non-claims

* **Not a general reduction-system theory.** The development is about
  implication chains and canonical lifts. `ReductionSystem` is a small
  structure for stating invariants, not a framework.
* **Not byte-identical to the source.** The supplied text was partially
  truncated; `Nest.lean` is generated. `Nest19_source` preserves one proof
  body verbatim as a compatibility check. See `docs/PROVENANCE.md`.
* **The `Nest` conclusion is closed.** It carries no information beyond
  `φ i a`; it should not be read as a strengthening.
* **No automation beyond core tactics.** `rfl`, `simp`, `decide`,
  `funext`, `induction`. No Mathlib, no `aesop`, no custom tactic.
* **`propext` is used** in three `Chain` lemmas, through `Fin.induction`.

---

## 11. Provenance

The `Nest` family arrived as source text using two undefined primitives,
`DeepReduction` and `ClosedLift`. Their call shapes pin their signatures
exactly; `Nest19_source` in `ReductionCalculus/Examples.lean` is the source
proof body transcribed and checked against the definitions in this
repository.

What was transcribed, what was regenerated, and the three modernisations
required by Lean 4.36 are documented in [`docs/PROVENANCE.md`](docs/PROVENANCE.md).
