import Mathlib

/- 2.2.2 Metric and topological spaces -/

/-
After 2.1, you can guess how metric spaces are
defined in mathlib: there is a class MetricSpace X, extending a class
Dist X which provides the function dist : X → X → ℝ, and containing
the axioms. So, to work in a metric space, we write [MetricSpace X]
[MIL, 11.2]:
-/

open Set Filter Topology

section

variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check dist_nonneg      -- 0 ≤ dist a b
#check dist_self        -- dist a a = 0
#check dist_comm        -- dist x y = dist y x
#check dist_triangle    -- dist x z ≤ dist x y + dist y z
#check dist_eq_zero     -- dist x y = 0 ↔ x = y

example : dist a b ≤ dist a c + dist b c := by
  rw [dist_comm b c]
  exact dist_triangle a c b

/-
And ℝ, ℝⁿ, ℂ, ... are instances of MetricSpace. In ℝ, dist x y is
|x - y|, and this is true by definition (it is the theorem
Real.dist_eq).
-/

example (x y : ℝ) : dist x y = |x - y| :=
  Real.dist_eq x y

example (d : X) : dist a d ≤ dist a b + dist b c + dist c d := by
  sorry

example : 0 ≤ dist a b + dist b a - dist a a := by
  sorry

/-
The open ball of center a and radius r is
Metric.ball a r = {x | dist x a < r}. A set s is open if it contains
a ball around each of its points (Metric.isOpen_iff):
-/

#check Metric.mem_ball     -- y ∈ ball x ε ↔ dist y x < ε
#check Metric.isOpen_iff   -- IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ball x ε ⊆ s
#check Metric.isOpen_ball  -- IsOpen (ball x ε)

example (r s : ℝ) (h : r ≤ s) : Metric.ball a r ⊆ Metric.ball a s := by
  intro x hx
  rw [Metric.mem_ball] at *
  linarith

example (r : ℝ) (hr : 0 < r) : a ∈ Metric.ball a r := by
  sorry

/-
Continuity is defined in mathlib for topological spaces (see below),
but for metric spaces it is the usual ε-δ definition
(Metric.continuous_iff):
-/

#check Metric.continuous_iff
  -- Continuous f ↔ ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a, dist a b < δ → dist (f a) (f b) < ε

example : Continuous (fun x : ℝ => 2 * x) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  use ε / 2
  constructor
  · linarith
  · intro a ha
    rw [Real.dist_eq] at *
    rw [← mul_sub, abs_mul, abs_two]
    linarith

/-
Proving continuity by hand is tedious. In practice, we use the
theorems of mathlib (continuous_id, continuous_const, Continuous.add,
Continuous.mul, Continuous.comp, ...), or better, the tactics
continuity and fun_prop, which apply them automatically:
-/

example : Continuous (fun x : ℝ => x ^ 2 + 3 * Real.sin x) := by
  fun_prop

example : Continuous (fun x : ℝ => 3 * x + 1) := by
  sorry

example : Continuous (fun x : X => dist x a) := by
  sorry

example : Continuous (fun x : ℝ => Real.exp (x ^ 2) * Real.cos x) := by
  sorry

end

/-
A topology on X is a collection of subsets of X,
the open sets, containing univ and closed under finite intersections
and arbitrary unions. Again, this is a class, TopologicalSpace X,
whose main field is the predicate IsOpen : Set X → Prop:
-/

section

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

#check isOpen_univ   -- IsOpen univ
#check IsOpen.inter  -- IsOpen s → IsOpen t → IsOpen (s ∩ t)
#check isOpen_sUnion -- (∀ t ∈ S, IsOpen t) → IsOpen (⋃₀ S)
#check IsOpen.union  -- IsOpen s → IsOpen t → IsOpen (s ∪ t)

/-
A set is closed if its complement is open (this is the definition,
isOpen_compl_iff), and a function is continuous if the preimage of
every open set is open (continuous_def):
-/

#check isOpen_compl_iff  -- IsOpen sᶜ ↔ IsClosed s
#check continuous_def    -- Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

example (f : X → Y) (hf : Continuous f) (s : Set Y) (hs : IsOpen s) :
    IsOpen (f ⁻¹' s) := by
  rw [continuous_def] at hf
  exact hf s hs

/-
Every metric space is a topological space, with the open sets defined
with balls, as above. Now prove the following using the definitions, i.e.,
continuous_def and isOpen_compl_iff:
-/

example (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := by
  sorry

example (f : X → Y) (hf : Continuous f) (s : Set Y) (hs : IsClosed s) :
    IsClosed (f ⁻¹' s) := by
  sorry

example (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∪ t) := by
  sorry

/-
Remember the filter 𝓝 x of 2.2.1: a set s is in 𝓝 x
if it contains an open set containing x (mem_nhds_iff). Then
continuity at a point is a limit:
ContinuousAt f x is Tendsto f (𝓝 x) (𝓝 (f x)). And a function is
continuous if and only if it is continuous at every point:
-/

#check mem_nhds_iff      -- s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t
#check continuous_iff_continuousAt

example (f : X → Y) (hf : Continuous f) (x : X) :
    Tendsto f (𝓝 x) (𝓝 (f x)) :=
  hf.continuousAt

example (s : Set X) (hs : IsOpen s) (x : X) (hx : x ∈ s) : s ∈ 𝓝 x := by
  sorry

end
