import Mathlib.Tactic

/- 1.2.4 Sets and functions -/

/-
Now for some more familiar math: sets and functions.
In set theory, everything is a set. In Lean, everything is a term of
some type, so what is a set? Given a type α, a set of elements of α
is a term s : Set α. And Set α is simply α → Prop: a set is
a predicate, i.e., the property of belonging to it. We
write x ∈ s (typed \in) for "x belongs to s", which is just s x.
Then we have the usual notation:

    Notation      Typed       Meaning
    ------------  ----------  -----------------------------------
    {x | P x}                 the set of x such that P x
    s ⊆ t         \sub        ∀ x, x ∈ s → x ∈ t
    s ∩ t         \inter      {x | x ∈ s ∧ x ∈ t}
    s ∪ t         \union      {x | x ∈ s ∨ x ∈ t}
    s \ t         \\          {x | x ∈ s ∧ x ∉ t}
    sᶜ            \^c         {x | x ∉ s}
    ∅             \empty      {x | False}
    Set.univ                  {x | True}

where x ∉ s (typed \notin) means ¬(x ∈ s). Note that the sets s and
t must be sets of elements of the same type α: in Lean, a set of
natural numbers and a set of real numbers can never be intersected.

The important point is that all of these are definitions, so, to
prove something about sets, we unfold them and we are back to the
logic of 1.2.1. For instance, x ∈ s ∩ t is by definition
x ∈ s ∧ x ∈ t, so we can take it apart with ⟨xs, xt⟩, and prove it
with ⟨xs, xt⟩.
-/

section

variable {α : Type*} (s t u : Set α)

open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨xs, xu⟩
  exact ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left
    exact ⟨xs, xt⟩
  · right
    exact ⟨xs, xu⟩

/-
A few remarks:
    - open Set allows us to write univ instead of Set.univ, and so
      on: everything named Set.something can now be called just
      something. In other words, it opens the namespace Set.
    - Since s ⊆ t is ∀ x, x ∈ s → x ∈ t, rintro x ⟨xs, xu⟩ introduces
      x and takes x ∈ s ∩ u apart, and h xs : x ∈ t.
    - (*) {α : Type*} means that α is a type in any universe (remember
      the (*) about universes in 1.1.2). Mathlib always uses Type*,
      but you can think of it as Type.

How do we prove that two sets are equal? By extensionality: two sets
are equal if they have the same elements. The tactic ext x reduces
s = t to x ∈ s ↔ x ∈ t, for an arbitrary x.
-/

example : s ∩ t = t ∩ s := by
  ext x
  constructor
  · rintro ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩
    exact ⟨xs, xt⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  sorry

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  sorry

example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  sorry

/-
Sets defined by a property work in the same way: x ∈ {x | P x} is,
by definition, P x. Here are the even and the odd natural numbers:
-/

def evens : Set ℕ := {n | Even n}

def odds : Set ℕ := {n | ¬Even n}

example : evens ∪ odds = univ := by
  ext n
  simp only [evens, odds, mem_union, mem_ofPred_eq, mem_univ, iff_true]
  exact em (Even n)

example : evens ∩ odds = ∅ := by
  sorry

/-
Let us move on to functions. In 1.1 we have already seen
that, for types α and β, there is the type α → β of functions from α
to β. Unlike in set theory, a function is not a set of pairs: it is a
primitive notion of the theory, and we evaluate f : α → β at x : α by
writing f x. Given f, we can consider:
    - the image of s : Set α, f '' s = {y | ∃ x, x ∈ s ∧ f x = y},
    - the preimage of v : Set β, f ⁻¹' v = {x | f x ∈ v} (⁻¹ is typed
      \-1).
Again, these are definitions, so y ∈ f '' s is an existential, which
we prove with use, and take apart with
⟨x, xs, rfl⟩.
-/

variable {β : Type*} (f : α → β) (v w : Set β)

example : f ⁻¹' (v ∩ w) = f ⁻¹' v ∩ f ⁻¹' w := by
  ext x
  rfl -- rfl is able to unfold all definitions here

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      exact ⟨x, xs, rfl⟩
    · right
      exact ⟨x, xt, rfl⟩
  · rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
    · exact ⟨x, Or.inl xs, rfl⟩
    · exact ⟨x, Or.inr xt, rfl⟩

/-
In the first example, both sides are equal by definition, so rfl
proves it. In the second one, we proved the same thing as on paper:
"if y = f x with x ∈ s ∪ t, then either x ∈ s, so y ∈ f '' s, or
x ∈ t, so y ∈ f '' t; and conversely".
-/

example : s ⊆ f ⁻¹' (f '' s) := by
  sorry

example : f '' (f ⁻¹' v) ⊆ v := by
  sorry

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

/-
The usual properties of functions are, again, definitions, written
in the language of 1.1:
    - Function.Injective f is ∀ a b, f a = f b → a = b,
    - Function.Surjective f is ∀ b, ∃ a, f a = b,
    - Function.Bijective f is Injective f ∧ Surjective f,
and composition g ∘ f (typed \comp) is fun x => g (f x). If we open
the Function namespace, we can drop the Function. prefix. Let us see one example
with real numbers, where the tools of 1.2.2 come in handy:
-/

open Function

example : Injective (fun x : ℝ => 2 * x + 3) := by
  intro a b h
  dsimp at h
  linarith

example : Surjective (fun x : ℝ => 2 * x + 3) := by
  intro y
  use (y - 3) / 2
  ring

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

example (h : Injective f) : f '' (s ∩ t) = f '' s ∩ f '' t := by
  sorry

example (h : Surjective f) : f '' (f ⁻¹' v) = v := by
  sorry

example {γ : Type*} (g : β → γ) (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  sorry

example {γ : Type*} (g : β → γ) (hf : Surjective f) (hg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry

example {γ : Type*} (g : β → γ) (h : Injective (g ∘ f)) : Injective f := by
  sorry

example : ¬Injective (fun x : ℝ => x ^ 2) := by
  sorry

end
