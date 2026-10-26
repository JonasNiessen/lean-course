import Mathlib

/- 2.2.1 Filters: THE WAY to do convergence in mathlib -/

/-
In analysis there are many notions of limit: limits of sequences,
limits of functions at a point, at infinity, one-sided limits, limits
along a subset, ... and each of them comes with its own versions of
the same theorems (the limit of a sum is the sum of the limits, the
limit of a composition, ...). Mathlib unifies all of them with a
single notion: filters [MIL, 11.1].

A filter on a type α is a collection F of subsets of α (which we
think of as the "big" sets, or the sets which contain "all points
close enough to something"), such that:
    - univ ∈ F,
    - if s ∈ F and s ⊆ t, then t ∈ F,
    - if s ∈ F and t ∈ F, then s ∩ t ∈ F.
By now you can guess what this is in Lean: a structure. Let us define
our own, as we did in 2.1:
-/

structure Filter₁ (α : Type*) where
  sets : Set (Set α)
  univ_sets : Set.univ ∈ sets
  sets_of_superset {s t : Set α} : s ∈ sets → s ⊆ t → t ∈ sets
  inter_sets {s t : Set α} : s ∈ sets → t ∈ sets → s ∩ t ∈ sets

/-
The most important example: on ℕ, the sets which contain all n ≥ N,
for some N. Think of it as "the neighborhoods of ∞". Saying that a
property holds for all the elements of a set of atTop₁ means that it
holds "for n large enough".
-/

def atTop₁ : Filter₁ ℕ where
  sets := {s | ∃ N, ∀ n ≥ N, n ∈ s}
  univ_sets := ⟨0, fun n _ => Set.mem_univ n⟩
  sets_of_superset := by
    rintro s t ⟨N, hN⟩ hst
    exact ⟨N, fun n hn => hst (hN n hn)⟩
  inter_sets := by
    rintro s t ⟨N, hN⟩ ⟨M, hM⟩
    use max N M
    intro n hn
    exact ⟨hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)⟩

/-
Another basic example: given a set s, the principal filter of s is
the collection of all the sets containing s. Define it:
-/

def principal₁ {α : Type*} (s : Set α) : Filter₁ α where
  sets := sorry
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

/-
From now on we use the filters of mathlib, Filter α, which are
defined in the same way. We open the namespaces Filter and Topology
to have access to the notation. The basic filters are:
    - atTop: the filter we just defined, on ℕ (or on ℝ, or on any
      ordered type),
    - 𝓝 x (typed \MCN): the neighborhoods of x, i.e., the sets
      containing an open set around x in a topological space (we will
      discuss topology in 2.2.2),
    - 𝓟 s (typed \MCP): the principal filter of s.
-/

open Filter Topology

#check (atTop : Filter ℕ)
#check (𝓝 (2 : ℝ))
#check mem_atTop_sets -- s ∈ atTop ↔ ∃ a, ∀ b ≥ a, b ∈ s
#check univ_mem       -- univ ∈ f
#check inter_mem      -- s ∈ f → t ∈ f → s ∩ t ∈ f
#check mem_of_superset

/-
If F is a filter, ∀ᶠ x in F, P x means that the set
{x | P x} belongs to F: "P holds for x close enough to F". For
instance, ∀ᶠ n in atTop, P n means that P n holds for all n large
enough, i.e., ∃ N, ∀ n ≥ N, P n. The axioms of filters say that
"eventually" behaves well with ∧ and →:
-/

#check eventually_atTop  -- (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b ≥ a, p b
#check Eventually.and    -- (∀ᶠ x in f, p x) → (∀ᶠ x in f, q x) → ∀ᶠ x in f, p x ∧ q x
#check Eventually.mono   -- (∀ᶠ x in f, p x) → (∀ x, p x → q x) → ∀ᶠ x in f, q x

example : ∀ᶠ n in atTop, 3 ≤ n := by
  rw [eventually_atTop]
  use 3
  intro n hn
  exact hn

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

/-
Compare the last example with the proof that the sum of two
convergent sequences converges in 1.2.3: there we had to take
N = max N₁ N₂ by hand. Here the filter does it for us, once and for
all, in the axiom inter_sets.
-/

example : ∀ᶠ n in atTop, 2 * n ≥ n + 5 := by
  sorry

example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hPQ : ∀ n, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
  sorry

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (h : ∀ n, P n → Q n → R n) : ∀ᶠ n in atTop, R n := by
  sorry

/-
How do we define limits using filters? If f : α → β, F is a filter on α,
and G is a filter on β, then Tendsto f F G means that, for every
V ∈ G, we have f ⁻¹' V ∈ F. In words: "f x is eventually in V, as x
tends to F, for every V in G". For instance:
    - Tendsto u atTop (𝓝 a), for u : ℕ → ℝ, means that the sequence
      u converges to a,
    - Tendsto f (𝓝 x) (𝓝 y), for f : ℝ → ℝ, means that f(t) tends to
      y as t tends to x,
    - Tendsto f atTop atTop, for f : ℝ → ℝ, means that f(t) tends to
      ∞ as t tends to ∞,
and so on. A single definition, and a single collection of theorems
for all of them!
-/

#check tendsto_def  -- Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁

/-
Let us check that Tendsto u atTop (𝓝 a) is the same as the
ConvergesTo of 1.2.3:
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example (s : ℕ → ℝ) (a : ℝ) : ConvergesTo s a ↔ Tendsto s atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  rfl

/-
Here Metric.tendsto_atTop says that Tendsto u atTop (𝓝 a) is
∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε, and dist x y is |x - y| in
ℝ, by definition (see 2.2.2). Now we can use all the theorems of
mathlib about limits. For instance, in 1.2.3 we proved by hand that
the limit of a sum is the sum of the limits. In mathlib:
-/

#check Tendsto.add  -- Tendsto f x (𝓝 a) → Tendsto g x (𝓝 b) →
                    --   Tendsto (fun x => f x + g x) x (𝓝 (a + b))
#check Tendsto.mul
#check Tendsto.const_mul
#check tendsto_const_nhds
#check Tendsto.comp

example (s t : ℕ → ℝ) (a b : ℝ) (hs : Tendsto s atTop (𝓝 a))
    (ht : Tendsto t atTop (𝓝 b)) :
    Tendsto (fun n => s n + t n) atTop (𝓝 (a + b)) :=
  hs.add ht

example (s : ℕ → ℝ) (a : ℝ) (hs : Tendsto s atTop (𝓝 a)) :
    Tendsto (fun n => 3 * s n + 1) atTop (𝓝 (3 * a + 1)) :=
  (hs.const_mul 3).add tendsto_const_nhds

/-
Note that these theorems work for any filter x, not only atTop: they
are about limits of sequences, of functions, ... at the same time.

Now prove the following. For the first one, unfold the definitions
with tendsto_def. For the others, use the theorems above.
-/

example {α β γ : Type*} {F : Filter α} {G : Filter β} {H : Filter γ}
    {f : α → β} {g : β → γ} (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by
  sorry

example (s t : ℕ → ℝ) (a b : ℝ) (hs : Tendsto s atTop (𝓝 a))
    (ht : Tendsto t atTop (𝓝 b)) :
    Tendsto (fun n => s n * t n - 2) atTop (𝓝 (a * b - 2)) := by
  sorry

example (s : ℕ → ℝ) (a : ℝ) (hs : Tendsto s atTop (𝓝 a)) :
    Tendsto (fun n => (s n) ^ 2) atTop (𝓝 (a ^ 2)) := by
  sorry

/-
Finally, a beautiful property of filters is that they are ordered:
F ≤ G means that every set in G is in F (so F is "finer", or "more
concentrated", than G). Then Tendsto f F G is the same as
map f F ≤ G, where map f F is the filter of sets whose preimage is
in F. This is the actual definition in mathlib, and it allows us to
reason about limits with the algebra of filters, instead of ε's.
-/
