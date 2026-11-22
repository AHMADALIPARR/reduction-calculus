/-
# Reduction Calculus — core primitives

This file fixes the two primitives that the `Nest` family is written against:

* `DeepReduction` — one reduction step followed by a collapse;
* `ClosedLift`    — the canonical lift of `a : A i` along `φ`.

Both are defined so that the `Nest` proofs typecheck with the exact call
shapes they use:

```lean
have hr : R := DeepReduction h2 (fun r => r) hq
match ClosedLift A B φ i a with | ⟨b, rfl⟩ => ...
```

Nothing here is imported beyond Lean's prelude: the whole development is
kernel-checked core Lean with no Mathlib dependency.
-/

/-!
`ClosedLift` is deliberately a `def`, not a `theorem`: the source proofs
`match` on it and expect `⟨φ i a, rfl⟩` definitionally, which requires the
body to unfold. Hence the linter is switched off for this file.
-/
set_option linter.defProp false

namespace ReductionCalculus

/-! ## Deep reduction -/

/-- A single deep-reduction step.

`DeepReduction f g x` applies the reduction `f` to `x`, then collapses the
result with the endomorphism `g`.

The `Nest` proofs always pass `g = id`, where the collapse is the identity
and `DeepReduction f id x` is definitionally `f x`. The collapse slot is
what makes the step *deep* rather than a plain application: `deepReduce`
below iterates `f` and applies `g` to the accumulated value, and
`DeepReduction` is its one-step case (`deepReduce_one`). -/
def DeepReduction {α β : Sort _} (f : α → β) (g : β → β) (x : α) : β :=
  g (f x)

/-- The defining equation of `DeepReduction`. -/
theorem DeepReduction_def {α β : Sort _} (f : α → β) (g : β → β) (x : α) :
    DeepReduction f g x = g (f x) :=
  rfl

/-- With the identity collapse a deep reduction is the reduction itself.
This is the form used by every `Nest` proof. -/
@[simp] theorem DeepReduction_id {α β : Sort _} (f : α → β) (x : α) :
    DeepReduction f id x = f x :=
  rfl

/-- Deep reduction respects equality of its three arguments. -/
theorem DeepReduction_congr {α β : Sort _} {f f' : α → β} {g g' : β → β} {x x' : α}
    (hf : f = f') (hg : g = g') (hx : x = x') :
    DeepReduction f g x = DeepReduction f' g' x' := by
  rw [hf, hg, hx]

/-- Reducing a pre-composed input is reducing the composite input. -/
theorem DeepReduction_comp {α β γ : Sort _} (f : α → β) (g : β → β) (k : γ → α) (x : γ) :
    DeepReduction f g (k x) = g (f (k x)) :=
  rfl

/-- Two collapses that agree on the reduced value give the same deep
reduction. -/
theorem DeepReduction_collapse {α β : Sort _} (f : α → β) (g g' : β → β) (x : α)
    (h : ∀ y, g y = g' y) : DeepReduction f g x = DeepReduction f g' x :=
  h (f x)

/-! ## Iterated reduction

`DeepReduction` is one step. The *deep* part is the iteration below: `n`
steps of `f`, then one collapse. -/

/-- `iterateStep f n x` applies `f` exactly `n` times to `x`. -/
def iterateStep {α : Sort _} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateStep f n (f x)

@[simp] theorem iterateStep_zero (f : α → α) (x : α) : iterateStep f 0 x = x :=
  rfl

/-- `n + 1` steps is one step followed by `n` steps. -/
theorem iterateStep_succ (f : α → α) (n : Nat) (x : α) :
    iterateStep f (n + 1) x = f (iterateStep f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- Iterations add. -/
theorem iterateStep_add (f : α → α) (m n : Nat) (x : α) :
    iterateStep f (m + n) x = iterateStep f n (iterateStep f m x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [Nat.add_succ, iterateStep_succ, ih]

/-- `deepReduce f g n x` performs `n` reduction steps of `f` on `x` and then
collapses the accumulated value with `g`. -/
def deepReduce {α : Sort _} (f g : α → α) (n : Nat) (x : α) : α :=
  g (iterateStep f n x)

@[simp] theorem deepReduce_zero (f g : α → α) (x : α) : deepReduce f g 0 x = g x :=
  rfl

/-- Depth one is exactly `DeepReduction`: the iterated form generalises the
one-step primitive used by the `Nest` proofs. -/
theorem deepReduce_one (f g : α → α) (x : α) :
    deepReduce f g 1 x = DeepReduction f g x :=
  rfl

/-- Peeling one step off a deep reduction. -/
theorem deepReduce_succ (f g : α → α) (n : Nat) (x : α) :
    deepReduce f g (n + 1) x = deepReduce f g n (f x) :=
  rfl

/-- Two deep reductions of depth `m` and `n` are one reduction of depth
`m + n`, collapsed once. -/
theorem deepReduce_add (f g : α → α) (m n : Nat) (x : α) :
    deepReduce f g (m + n) x = g (iterateStep f n (iterateStep f m x)) := by
  simp [deepReduce, iterateStep_add]

/-! ## Invariants

The semantic content of "reduction": a predicate preserved by the step and
by the collapse is preserved by every deep reduction. -/

/-- Iterated steps preserve an invariant of the step. -/
theorem iterateStep_preserves {α : Sort _} {p : α → Prop} (f : α → α)
    (hf : ∀ x, p x → p (f x)) : ∀ n x, p x → p (iterateStep f n x)
  | 0, _, hx => hx
  | n + 1, x, hx => iterateStep_preserves f hf n (f x) (hf x hx)

/-- Deep reduction preserves invariants of both the step and the collapse. -/
theorem deepReduce_preserves {α : Sort _} {p : α → Prop} (f g : α → α)
    (hf : ∀ x, p x → p (f x)) (hg : ∀ x, p x → p (g x)) :
    ∀ n x, p x → p (deepReduce f g n x)
  | 0, x, hx => hg x hx
  | n + 1, x, hx => deepReduce_preserves f g hf hg n (f x) (hf x hx)

/-! ## The closed lift -/

/-- The closed lift of `a : A i` along `φ : ∀ i, A i → B i`.

The result is the `∃`-statement that is the conclusion of every `Nest`
theorem, with the canonical witness `φ i a`.

The lift is *closed* because the fibre `{ b : B i // b = φ i a }` is a
subsingleton (`ClosedLift_subsingleton`): the lift makes no choice, so no
choice principle is involved, and any two witnesses are equal
(`ClosedLift_uniq`). -/
def ClosedLift {ι : Sort _} (A B : ι → Type _) (φ : ∀ i, A i → B i) (i : ι) (a : A i) :
    ∃ b : B i, b = φ i a :=
  ⟨φ i a, rfl⟩

/-- The lift is definitionally the canonical witness. -/
theorem ClosedLift_def {ι : Sort _} (A B : ι → Type _) (φ : ∀ i, A i → B i)
    (i : ι) (a : A i) :
    ClosedLift A B φ i a = ⟨φ i a, rfl⟩ :=
  rfl

/-- Every element of `A i` has a lift. -/
theorem ClosedLift_exists {ι : Sort _} (A B : ι → Type _) (φ : ∀ i, A i → B i)
    (i : ι) (a : A i) : ∃ b : B i, b = φ i a :=
  ClosedLift A B φ i a

/-- The fibre of the lift is a subsingleton: this is what "closed" means. -/
theorem ClosedLift_subsingleton {ι : Sort _} (A B : ι → Type _) (φ : ∀ i, A i → B i)
    (i : ι) (a : A i) : Subsingleton { b : B i // b = φ i a } :=
  ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩

/-- Two witnesses of the same fibre are equal. -/
theorem ClosedLift_uniq {ι : Sort _} {A B : ι → Type _} {φ : ∀ i, A i → B i}
    {i : ι} {a : A i} {b₁ b₂ : B i} (h₁ : b₁ = φ i a) (h₂ : b₂ = φ i a) : b₁ = b₂ :=
  h₁.trans h₂.symm

/-- Lifting twice is lifting along the composite, definitionally. -/
theorem ClosedLift_comp {ι : Sort _} (A B C : ι → Type _) (φ : ∀ i, A i → B i)
    (ψ : ∀ i, B i → C i) (i : ι) (a : A i) :
    ClosedLift A C (fun i a => ψ i (φ i a)) i a = ⟨ψ i (φ i a), rfl⟩ :=
  rfl

/-- Eliminating a closed lift: this is the `match ClosedLift … with | ⟨b, rfl⟩`
pattern used in the `Nest` proofs, as a lemma. -/
theorem ClosedLift_elim {ι : Sort _} {A B : ι → Type _} {φ : ∀ i, A i → B i}
    {i : ι} {a : A i} {C : Prop} (h : ∀ b : B i, b = φ i a → C) : C :=
  (ClosedLift A B φ i a).elim h

end ReductionCalculus
