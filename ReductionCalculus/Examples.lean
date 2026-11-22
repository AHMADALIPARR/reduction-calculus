/-
# Reduction Calculus — examples and source-compatibility checks

Two things are checked here:

1. **Source compatibility.** `Nest19_source` is the `Nest19` proof body
   transcribed from the source, kept in its original style: one `have` per
   position, `DeepReduction … (fun x => x) …` for the steps, and a
   `match ClosedLift … with | ⟨b, rfl⟩` at the end. If the two primitives
   in `Core.lean` had the wrong signatures, this theorem would not
   elaborate.
2. **Computation.** Small concrete instances of every definition and
   lemma, so the semantics are exercised and not just stated.
-/
import ReductionCalculus.Core
import ReductionCalculus.Chain
import ReductionCalculus.Semantics

namespace ReductionCalculus

/-! ## Source compatibility -/

/-- The `Nest19` proof from the source, transcribed.

The only deviation is the leading `intro`, which has nothing to introduce
on the `∃` goal and is dropped; everything else is the original proof
script. -/
theorem Nest19_source {ι : Type _} (A B : ι → Type _) (φ : ∀ i, A i → B i)
    (P Q R S T U V W X Y Z AA BB CC DD EE FF GG HH : Prop)
    (h1 : P → Q) (h2 : Q → R) (h3 : R → S) (h4 : S → T) (h5 : T → U)
    (h6 : U → V) (h7 : V → W) (h8 : W → X) (h9 : X → Y) (h10 : Y → Z)
    (h11 : Z → AA) (h12 : AA → BB) (h13 : BB → CC) (h14 : CC → DD)
    (h15 : DD → EE) (h16 : EE → FF) (h17 : FF → GG) (h18 : GG → HH)
    (hp : P) (i : ι) (a : A i) :
    ∃ b : B i, b = φ i a := by
  have hq : Q := by exact h1 hp
  have hr : R := DeepReduction h2 (fun r => r) hq
  have hs : S := by
    refine h3 ?_
    exact hr
  have ht : T := by exact h4 hs
  have hu : U := DeepReduction h5 (fun u => u) ht
  have hv : V := by
    refine h6 ?_
    exact hu
  have hw : W := by exact h7 hv
  have hx : X := DeepReduction h8 (fun x => x) hw
  have hy : Y := by
    refine h9 ?_
    exact hx
  have hz : Z := by exact h10 hy
  have haa : AA := DeepReduction h11 (fun aa => aa) hz
  have hbb : BB := by
    refine h12 ?_
    exact haa
  have hcc : CC := by exact h13 hbb
  have hdd : DD := DeepReduction h14 (fun dd => dd) hcc
  have hee : EE := by
    refine h15 ?_
    exact hdd
  have hff : FF := by exact h16 hee
  have hgg : GG := DeepReduction h17 (fun gg => gg) hff
  have hhh : HH := by
    match ClosedLift A B φ i a with
    | ⟨b, hb⟩ =>
      match hb with
      | rfl =>
        refine h18 ?_
        exact hgg
  exact ⟨φ i a, rfl⟩

/-! ## Deep reduction computes -/

/-- Three increments, collapsed by the identity. -/
example : deepReduce (· + 1) id 3 0 = 3 := rfl

/-- The one-step primitive is plain application under the identity collapse. -/
example : DeepReduction (· + 1) id 3 = 4 := rfl

/-- Depth one of the iterated form is the one-step primitive. -/
example (n : Nat) : deepReduce (· + 1) (· + 10) 1 n = n + 11 := rfl

/-! ## Invariants are preserved -/

/-- `n ↦ n + 1` and the identity collapse both preserve `0 ≤ ·`, so every
deep reduction does. -/
example (n : Nat) : 0 ≤ deepReduce (· + 1) id 7 n :=
  deepReduce_preserves (p := fun m => 0 ≤ m) (· + 1) id
    (fun _ _ => Nat.zero_le _) (fun _ h => h) 7 n (Nat.zero_le n)

/-! ## The closed lift -/

/-- The lift in a concrete universe: `ι := Unit`, `A := Nat`, `B := Int`. -/
example : ∃ b : Int, b = (5 : Int) :=
  ClosedLift (fun (_ : Unit) => Nat) (fun (_ : Unit) => Int) (fun _ n => (n : Int)) () 5

/-- Every witness of the fibre is the canonical one. -/
example : (5 : Int) = ((5 : Nat) : Int) :=
  ClosedLift_uniq (φ := fun (_ : Unit) (n : Nat) => (n : Int)) (i := ()) (a := 5) rfl rfl

/-! ## Chains -/

/-- A real chain: `0 < 1`, `0 < 2`, `0 < 3`. -/
theorem ltChain : Chain (fun k : Fin 3 => 0 < (k : Nat) + 1) :=
  ⟨fun _ h => Nat.lt_of_lt_of_le h (Nat.le_succ _)⟩

/-- Every position of the chain is reached. -/
example : ∀ k : Fin 3, 0 < (k : Nat) + 1 :=
  ltChain.apply (by decide)

/-- So is the last position. -/
example : 0 < 3 :=
  ltChain.last (by decide)

/-- The two presentations agree: the chain *is* a reduction from its first
proposition to its last. -/
example : Reduces ImpStep (0 < 1) (0 < 3) :=
  ltChain.toReduces

/-- A chain of implications reduces its endpoints. -/
example : 1 < 2 → 3 < 4 := by
  have h : Reduces ImpStep (1 < 2) (3 < 4) :=
    .step (show 1 < 2 → 2 < 3 from fun _ => by decide)
      (.step (show 2 < 3 → 3 < 4 from fun _ => by decide) (.refl (3 < 4)))
  exact reduces_imp h

/-- A successor chain on `Nat`: `0 → 1 → 2 → 3`. -/
example : Reduces (fun a b : Nat => b = a + 1) 0 3 :=
  .step (show 1 = 0 + 1 from rfl)
    (.step (show 2 = 1 + 1 from rfl)
      (.step (show 3 = 2 + 1 from rfl) (.refl 3)))

/-! ## The `nest` schema -/

/-- The schema in action: a one-step chain plus the closed lift. -/
example : ∃ b : Int, b = (7 : Int) := by
  have hchain : Reduces ImpStep True True :=
    .step (fun _ => trivial) (.refl True)
  exact (nest (fun (_ : Unit) => Nat) (fun (_ : Unit) => Int)
    (fun _ n => (n : Int)) hchain trivial () 7).2

end ReductionCalculus
