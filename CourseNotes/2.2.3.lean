import Mathlib

/- 2.2.3 Derivatives -/

/-
Let us now do some calculus with functions f : ℝ → ℝ [MIL, 12.1].
Mathlib knows the usual functions: Real.exp, Real.log, Real.sin,
Real.cos, Real.sqrt, x ^ n, ... and their properties:
-/

open Real Set Filter Topology

#check exp_pos       -- 0 < rexp x
#check exp_add       -- rexp (x + y) = rexp x * rexp y
#check log_exp       -- log (rexp x) = x
#check sin_sq_add_cos_sq
#check exp_le_exp    -- rexp x ≤ rexp y ↔ x ≤ y

/-
(Here rexp is just the notation for Real.exp.)

A caveat: what is Real.sqrt (-1)? In Lean, every function is total:
Real.sqrt has type ℝ → ℝ, so it has to return some real number for
every real number, including the negative ones. Mathlib chooses
Real.sqrt x = 0 for x ≤ 0 (we write √x for Real.sqrt x, typed \sqrt).
The same happens with other functions: x / 0 = 0, Real.log 0 = 0,
and so on. These are "junk values": they are chosen so that the
definitions are as simple as possible, and nobody is supposed to use
them in actual mathematics.
-/

#check sqrt_eq_zero_of_nonpos  -- x ≤ 0 → √x = 0
#check div_zero                -- a / 0 = 0
#check log_zero                -- log 0 = 0

example : √(-1) = 0 := by
  apply sqrt_eq_zero_of_nonpos
  norm_num

/-
This is not a problem, but it has a consequence: the theorems which
are false for the junk values have extra hypotheses. For instance,
(√x) ^ 2 = x only holds for x ≥ 0, so the theorem Real.sq_sqrt needs
the hypothesis 0 ≤ x. On paper, this hypothesis is implicit in
writing √x at all; in Lean, you have to provide it. Thus, in the end,
the math you can do is exactly the same whether you use the classical
partial definition or Lean's total definition of the square root.
-/

#check sq_sqrt  -- 0 ≤ x → √x ^ 2 = x
#check sqrt_sq  -- 0 ≤ x → √(x ^ 2) = x

example (x : ℝ) (hx : 0 ≤ x) : √x ^ 2 = x :=
  sq_sqrt hx

example : ¬ ∀ x : ℝ, √x ^ 2 = x := by
  sorry

example : √(-4) + 2 = 2 := by
  sorry

example (x : ℝ) (hx : 0 ≤ x) : √(x ^ 2) = x := by
  sorry

/-
As with limits, there are several ways to talk about
derivatives:
    - HasDerivAt f f' x means that f is differentiable at x, with
      derivative f'. This is a proposition, defined with limits, i.e.,
      with filters (as everything in analysis!).
    - deriv f x is the derivative of f at x, a real number. As with
      √ above, deriv f x is defined even if f is not differentiable
      at x: in that case, it is 0 by convention (a junk value).
      So, to use deriv f x, we often need to know that f is
      differentiable.
    - DifferentiableAt ℝ f x means that f is differentiable at x, and
      Differentiable ℝ f means that it is differentiable everywhere.
The basic theorems about derivatives are stated with HasDerivAt:
-/

#check hasDerivAt_id    -- HasDerivAt id 1 x
#check hasDerivAt_const -- HasDerivAt (fun x => c) 0 x
#check hasDerivAt_pow   -- HasDerivAt (fun x => x ^ n) (↑n * x ^ (n - 1)) x
#check hasDerivAt_exp   -- HasDerivAt rexp (rexp x) x
#check hasDerivAt_sin   -- HasDerivAt sin (cos x) x
#check HasDerivAt.add   -- HasDerivAt f f' x → HasDerivAt g g' x →
                        --   HasDerivAt (fun x => f x + g x) (f' + g') x
#check HasDerivAt.mul
#check HasDerivAt.comp  -- the chain rule
#check HasDerivAt.sin   -- HasDerivAt f f' x →
                        --   HasDerivAt (fun x => sin (f x)) (cos (f x) * f') x
#check hasDerivAt_id'   -- HasDerivAt (fun x => x) 1 x
#check HasDerivAt.deriv -- HasDerivAt f f' x → deriv f x = f'

example (x : ℝ) : HasDerivAt (fun x => x ^ 2) (2 * x) x := by
  have := hasDerivAt_pow 2 x
  simp at this
  exact this

example (x : ℝ) : HasDerivAt (fun x => x ^ 2 + sin x) (2 * x + cos x) x := by
  apply HasDerivAt.add
  · have := hasDerivAt_pow 2 x
    simpa using this
  · exact hasDerivAt_sin x

/-
Here simpa using this is simp at this, followed by exact this (and
it also simplifies the target). Look at the infoview to see what
simp did. Very often, the derivative given by the theorems is not
exactly the one we want, but it is equal to it: then we use
HasDerivAt.congr_deriv, or we prove it as follows.
-/

example (x : ℝ) : HasDerivAt (fun x => 3 * x ^ 2) (6 * x) x := by
  have h := (hasDerivAt_pow 2 x).const_mul 3
  convert h using 1
  ring

/-
The tactic convert h using 1 closes the goal with h, and leaves as
new goals the differences between the goal and h, here
6 * x = 3 * (↑2 * x ^ (2 - 1)). Try to remove using 1 and see what
happens.

For the exercises, you may find useful the chain rules for the usual
functions, like HasDerivAt.sin above (and HasDerivAt.exp,
HasDerivAt.cos, ...).
-/

example (x : ℝ) : HasDerivAt (fun x => x ^ 3 + 2 * x) (3 * x ^ 2 + 2) x := by
  sorry

example (x : ℝ) : HasDerivAt (fun x => exp x * sin x)
    (exp x * sin x + exp x * cos x) x := by
  sorry

example (x : ℝ) : HasDerivAt (fun x => sin (2 * x)) (2 * cos (2 * x)) x := by
  sorry

/-
For deriv, simp knows many rules, so it can often compute derivatives
by itself (but, as with all uses of simp, check what it did):
-/

example : deriv (fun x : ℝ => sin x) = fun x => cos x := by
  ext x
  simp

example (x : ℝ) : deriv (fun x => x ^ 2) x = 2 * x := by
  simp

example (x : ℝ) : deriv (fun x => exp x + x ^ 3) x = exp x + 3 * x ^ 2 := by
  sorry

example (x : ℝ) : deriv (fun x => x ^ 3 + 2 * x) x = 3 * x ^ 2 + 2 := by
  sorry

/-
Differentiability can be proved with the tactic fun_prop, as
continuity in 2.2.2:
-/

example : Differentiable ℝ (fun x : ℝ => x ^ 2 * exp x) := by
  fun_prop

/-
Of course, mathlib also knows the
theorems of Rolle and of the mean value, the fact that a function
with nonnegative derivative is monotone, and so on:
-/

#check exists_deriv_eq_slope  -- the mean value theorem
#check exists_deriv_eq_zero   -- Rolle's theorem
#check monotone_of_deriv_nonneg

example : Monotone (fun x : ℝ => x + exp x) := by
  apply monotone_of_deriv_nonneg
  · fun_prop
  · intro x
    simp
    positivity

example : Monotone (fun x : ℝ => x ^ 3 + x) := by
  sorry

example (f : ℝ → ℝ) (hf : Differentiable ℝ f) (h : ∀ x, deriv f x = 0) :
    f 0 = f 1 := by
  sorry

/-
    (*) Derivatives in mathlib are defined in much more generality:
    for functions f : E → F between normed spaces (see 2.2.5), the
    derivative at a point is a continuous linear map E →L[𝕜] F,
    fderiv 𝕜 f x (the Fréchet derivative). For f : 𝕜 → F, deriv f x
    is just fderiv 𝕜 f x 1. There is also a whole theory of
    derivatives within a set (HasDerivWithinAt), one-sided
    derivatives, and so on.
-/
