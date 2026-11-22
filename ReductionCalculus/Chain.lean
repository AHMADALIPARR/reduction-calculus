/-
# Reduction Calculus — chains

Two views of the same object:

* `Reduces r a b` — the reflexive–transitive closure of a step relation,
  i.e. "`a` reduces to `b` in zero or more steps". This is the abstract
  notion of a reduction chain.
* `Chain P` — a finite chain of propositions, one implication per adjacent
  pair. This is the literal shape of the `have`-chains in the `Nest`
  proofs: one `have` per position.

Implication is the canonical step (`ImpStep`), and `reduces_imp` is the
soundness theorem that turns a chain of implications back into an
implication.
-/

namespace ReductionCalculus

/-! ## The reduction relation -/

/-- `Reduces r a b` is the reflexive–transitive closure of `r`:
`a` reduces to `b` in zero or more steps. -/
inductive Reduces {α : Sort _} (r : α → α → Prop) : α → α → Prop where
  /-- Zero steps. -/
  | refl (a : α) : Reduces r a a
  /-- One step, then any number of further steps. -/
  | step {a b c : α} : r a b → Reduces r b c → Reduces r a c

namespace Reduces

variable {α : Sort _} {r s : α → α → Prop} {a b c : α}

/-- Reduction chains compose. -/
theorem trans : ∀ {a b c : α}, Reduces r a b → Reduces r b c → Reduces r a c
  | _, _, _, .refl _, h₂ => h₂
  | _, _, _, .step h h', h₂ => .step h (trans h' h₂)

/-- A single step is a reduction. -/
theorem single (h : r a b) : Reduces r a b :=
  .step h (.refl b)

/-- Zero steps, as a theorem. -/
theorem zero : Reduces r a a :=
  .refl a

/-- Reduction is monotone in the step relation. -/
theorem mono (h : ∀ a b, r a b → s a b) : ∀ {a b : α}, Reduces r a b → Reduces s a b
  | _, _, .refl _ => .refl _
  | _, _, .step h₁ h₂ => .step (h _ _ h₁) (mono h h₂)

/-- Prefix a reduction with a step. -/
theorem head (h : r a b) (hr : Reduces r b c) : Reduces r a c :=
  .step h hr

/-- Append a step to a reduction. -/
theorem tail (hr : Reduces r a b) (h : r b c) : Reduces r a c :=
  trans hr (single h)

end Reduces

/-! ## Implication as a reduction step -/

/-- Implication, read as a one-step reduction on `Prop`. -/
def ImpStep (p q : Prop) : Prop :=
  p → q

/-- `ImpStep` is implication, definitionally. -/
theorem ImpStep.def (p q : Prop) : ImpStep p q = (p → q) :=
  rfl

/-- **Soundness of implication reduction.** A chain of implications is an
implication: reduction cannot manufacture a conclusion that does not
follow. This is the semantic content that every `Nest k` theorem
discharges. -/
theorem reduces_imp {p q : Prop} (h : Reduces ImpStep p q) : p → q :=
  match h with
  | .refl _ => fun hp => hp
  | .step h₁ h₂ => fun hp => reduces_imp h₂ (h₁ hp)

/-- A single implication is a one-step reduction chain. -/
theorem reduces_imp_single {p q : Prop} (h : p → q) : Reduces ImpStep p q :=
  .step h (.refl q)

/-! ## Finite chains -/

/-- A chain of `n + 1` propositions in which each position implies the next.

`Chain` is the `have`-chain of the `Nest` proofs as a first-class object:
`step k` is the implication from position `k` to position `k + 1`. -/
structure Chain {n : Nat} (P : Fin (n + 1) → Prop) : Prop where
  /-- The implication from position `k` to position `k + 1`. -/
  step : ∀ k : Fin n, P k.castSucc → P k.succ

namespace Chain

variable {n : Nat} {P : Fin (n + 1) → Prop}

/-- Every position of a chain is reached from position `0`. -/
theorem apply (c : Chain P) (h₀ : P 0) : ∀ k : Fin (n + 1), P k :=
  Fin.induction h₀ (fun k ih => c.step k ih)

/-- The last proposition of a chain follows from the first. -/
theorem last (c : Chain P) (h₀ : P 0) : P (Fin.last n) :=
  c.apply h₀ (Fin.last n)

end Chain

end ReductionCalculus
