import Mathlib

/- 2.2.4 Integration -/

/-
Integration in mathlib is based on measure theory
[MIL, 13]. As you can imagine by now:
    - a σ-algebra on a type α is a class, MeasurableSpace α, whose
      main field is the predicate MeasurableSet : Set α → Prop,
    - a measure on α is a structure, μ : Measure α, and μ s is the
      measure of the set s.
Since a measure can take the value ∞, μ s is not a real number, but
an element of ℝ≥0∞ (typed \R\>=0\infty), the extended nonnegative
real numbers [0, ∞]. In ℝ, and in ℝⁿ, the Lebesgue measure is called
volume.
-/

open Set Filter Topology MeasureTheory ENNReal

section

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

#check MeasurableSet.union   -- MeasurableSet s → MeasurableSet t → MeasurableSet (s ∪ t)
#check MeasurableSet.compl   -- MeasurableSet s → MeasurableSet sᶜ
#check measure_empty         -- μ ∅ = 0
#check measure_mono          -- s ⊆ t → μ s ≤ μ t
#check measure_union_le      -- μ (s ∪ t) ≤ μ s + μ t
#check measure_union         -- Disjoint s t → MeasurableSet t → μ (s ∪ t) = μ s + μ t

example (s t : Set α) : μ (s ∩ t) ≤ μ s :=
  measure_mono inter_subset_left

/-
Note that measure_mono and measure_union_le work for any sets, not
only measurable ones: in mathlib, μ s is defined for every set s
(as the outer measure of s). Measurability is only needed for
equalities, such as measure_union.
-/

example (s t : Set α) : μ s ≤ μ (s ∪ t) := by
  sorry

example (s t u : Set α) : μ (s ∪ t ∪ u) ≤ μ s + μ t + μ u := by
  sorry

end

/-
In the last exercise, gcongr reduces the inequality
μ (s ∪ t) + μ u ≤ μ s + μ t + μ u to μ (s ∪ t) ≤ μ s + μ t, by
"cancelling" the parts which are equal on both sides. Try it!

The Lebesgue measure on ℝ gives the usual values to intervals:
-/

#check Real.volume_Icc  -- volume (Icc a b) = ENNReal.ofReal (b - a)
#check Real.volume_Ioo
#check Real.volume_singleton

example : volume (Icc (0 : ℝ) 2) = 2 := by
  rw [Real.volume_Icc]
  norm_num

example : volume (Ioo (1 : ℝ) 4) = 3 := by
  sorry

example (a : ℝ) : volume ({a} : Set ℝ) = 0 := by
  sorry

/-
Given f : α → E and a measure μ, the (Bochner, or
Lebesgue) integral of f is written ∫ x, f x ∂μ (typed \int and
\partial), and ∫ x in s, f x ∂μ is the integral over the set s. If we
omit ∂μ, the measure is volume. As in 2.2.3, every function has an
integral: if f is not integrable, its integral is 0 by convention. So
theorems about integrals usually need integrability hypotheses:
-/

#check integral_add
#check integral_smul   -- ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ
#check integral_mono

/-
For functions ℝ → ℝ, we usually use the interval integral
∫ x in a..b, f x, which is ∫ x in Ioc a b, f x if a ≤ b, and minus
the integral over Ioc b a otherwise (as usual in calculus). Mathlib
knows the integrals of the usual functions:
-/

#check integral_id     -- ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2
#check integral_pow    -- ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1)
#check integral_sin    -- ∫ x in a..b, sin x = cos a - cos b
#check integral_exp    -- ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a
#check intervalIntegral.integral_const

example : ∫ x in (0 : ℝ)..1, x ^ 2 = 1 / 3 := by
  rw [integral_pow]
  norm_num

example : ∫ x in (0 : ℝ)..Real.pi, Real.sin x = 2 := by
  rw [integral_sin]
  norm_num

/-
Often simp (or norm_num with the right lemmas) can do this directly:
try replacing the proofs above by norm_num [integral_pow]. Now
compute the following integrals:
-/

example : ∫ x in (0 : ℝ)..2, x ^ 3 = 4 := by
  sorry

example : ∫ x in (1 : ℝ)..3, x = 4 := by
  sorry

example : ∫ x in (0 : ℝ)..1, Real.exp x = Real.exp 1 - 1 := by
  sorry

/-
For integrals of sums, we need to prove that the functions are
integrable. For continuous functions, this is
Continuous.intervalIntegrable:
-/

example : ∫ x in (0 : ℝ)..1, (x + x ^ 2) = 5 / 6 := by
  rw [intervalIntegral.integral_add]
  · rw [integral_id, integral_pow]
    norm_num
  · exact continuous_id.intervalIntegrable 0 1
  · exact (continuous_pow 2).intervalIntegrable 0 1

example : ∫ x in (0 : ℝ)..1, (Real.exp x + 2 * x) = Real.exp 1 := by
  sorry

/-
Hint: for 2 * x, use intervalIntegral.integral_const_mul.

Finally, the link between
derivatives and integrals: if f has derivative f' on [a, b], and f'
is integrable, then ∫ x in a..b, f' x = f b - f a.
-/

#check intervalIntegral.integral_eq_sub_of_hasDerivAt
#check intervalIntegral.integral_hasDerivAt_right

example : ∫ x in (0 : ℝ)..1, 2 * x * Real.exp (x ^ 2) = Real.exp 1 - 1 := by
  have h : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => Real.exp (x ^ 2)) (2 * x * Real.exp (x ^ 2)) x := by
    intro x _
    convert (hasDerivAt_pow 2 x).exp using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h]
  · norm_num
  · apply Continuous.intervalIntegrable
    fun_prop
