/-
# Reduction Calculus — semantics

What the primitives *mean*, stated as theorems rather than prose.

* A **reduction system** is a carrier with a one-step relation; `Reduces`
  is its reflexive–transitive closure.
* **Invariants** are preserved along reduction (`ReductionSystem.invariant`).
* The **`Nest` schema** (`nest`) is the single theorem that every concrete
  `Nest k` in `ReductionCalculus.Nest` instantiates: a chain of
  implications from `p` to `q`, a proof of `p`, and an element `a : A i`
  yield `q` together with the closed lift of `a`.
-/

import ReductionCalculus.Core
import ReductionCalculus.Chain

namespace ReductionCalculus

/-! ## Reduction systems -/

/-- A reduction system: a carrier together with a one-step reduction
relation. -/
structure ReductionSystem (α : Sort _) where
  /-- The one-step reduction relation. -/
  step : α → α → Prop

namespace ReductionSystem

variable {α : Sort _} (S : ReductionSystem α)

/-- The reduction relation of `S`: zero or more steps. -/
def Reduces (a b : α) : Prop :=
  ReductionCalculus.Reduces S.step a b

/-- Reductions in a system compose. -/
theorem reduces_trans {a b c : α} (h₁ : S.Reduces a b) (h₂ : S.Reduces b c) :
    S.Reduces a c :=
  ReductionCalculus.Reduces.trans h₁ h₂

/-- **Invariants.** A predicate preserved by every step is preserved by
every reduction. -/
theorem invariant {p : α → Prop} (h : ∀ a b, S.step a b → p a → p b) :
    ∀ {a b : α}, ReductionCalculus.Reduces S.step a b → p a → p b
  | _, _, .refl _, hp => hp
  | _, _, .step h₁ h₂, hp => invariant h h₂ (h _ _ h₁ hp)

end ReductionSystem

/-! ## The Nest schema -/

/-- **The abstract content of every `Nest k` theorem.**

A chain of implications `p → ⋯ → q`, a proof of `p`, and an element
`a : A i` give `q` (soundness of the chain) together with the closed lift
of `a`. Each concrete `Nest k` in `ReductionCalculus.Nest` is this theorem
applied to a chain of length `k`. -/
theorem nest {ι : Sort _} (A B : ι → Type _) (φ : ∀ i, A i → B i)
    {p q : Prop} (h : Reduces ImpStep p q) (hp : p) (i : ι) (a : A i) :
    q ∧ ∃ b : B i, b = φ i a :=
  ⟨reduces_imp h hp, ClosedLift A B φ i a⟩

/-- The lift half of the schema on its own: exactly the conclusion of a
`Nest k` theorem. -/
theorem nest_lift {ι : Sort _} (A B : ι → Type _) (φ : ∀ i, A i → B i)
    (i : ι) (a : A i) : ∃ b : B i, b = φ i a :=
  ClosedLift A B φ i a

/-- The `Nest` conclusion is closed: any two of its witnesses are equal, so
it carries no information beyond the value `φ i a`. This is why the lift
needs no choice principle. -/
theorem nest_lift_unique {ι : Sort _} {A B : ι → Type _} {φ : ∀ i, A i → B i}
    {i : ι} {a : A i} {b₁ b₂ : B i} (h₁ : b₁ = φ i a) (h₂ : b₂ = φ i a) : b₁ = b₂ :=
  h₁.trans h₂.symm

/-- The reduction half of the schema on its own. -/
theorem nest_reduce {p q : Prop} (h : Reduces ImpStep p q) (hp : p) : q :=
  reduces_imp h hp

end ReductionCalculus
