import Mathlib

/- 2.2.5 Normed and Banach spaces -/

/-
To finish, let us put together algebra (2.1) and topology (2.2.2):
normed spaces [MIL, 12.2]. A normed vector space over ℝ is a vector
space E with a norm ‖x‖ (typed \|| or \norm), satisfying the usual
axioms. In mathlib, it is given by two instances:
    - [NormedAddCommGroup E]: an abelian group with a norm, such that
      ‖x‖ = 0 ↔ x = 0, ‖-x‖ = ‖x‖, and ‖x + y‖ ≤ ‖x‖ + ‖y‖. It is
      automatically a metric space, with dist x y = ‖x - y‖.
    - [NormedSpace ℝ E]: the scalar multiplication satisfies
      ‖a • x‖ = |a| * ‖x‖ (more precisely, ≤, which implies the
      equality). This class takes the module structure as a
      parameter, as in 2.1.3.
-/

open Set Filter Topology

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

#check norm_nonneg   -- 0 ≤ ‖a‖
#check norm_eq_zero  -- ‖a‖ = 0 ↔ a = 0
#check norm_neg      -- ‖-a‖ = ‖a‖
#check norm_add_le   -- ‖a + b‖ ≤ ‖a‖ + ‖b‖
#check norm_smul     -- ‖r • x‖ = ‖r‖ * ‖x‖
#check dist_eq_norm  -- dist a b = ‖a - b‖

example (x y : E) : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
  rw [sub_eq_add_neg]
  calc
    ‖x + -y‖ ≤ ‖x‖ + ‖-y‖ := norm_add_le x (-y)
    _ = ‖x‖ + ‖y‖ := by rw [norm_neg]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs]

/-
Note that in norm_smul, ‖r‖ is the norm of r as an element of ℝ,
which is |r| (Real.norm_eq_abs).
-/

example (x y z : E) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
  sorry

example (x : E) : ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := by
  sorry

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ + ‖x - y‖ := by
  sorry

/-
The usual examples are instances: ℝ, ℂ, ℝⁿ (with the Euclidean norm,
EuclideanSpace ℝ (Fin n)), spaces of functions, and so on:
-/

#synth NormedAddCommGroup (EuclideanSpace ℝ (Fin 3))
-- EuclideanSpace ℝ (Fin n) is how ℝ^n looks in mathlib
#synth NormedSpace ℝ ℂ

/-
Banach spaces. A Banach space is a complete normed space: every
Cauchy sequence converges. Completeness is, again, a class,
CompleteSpace E, so a real Banach space is given by
[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]. Every
finite dimensional normed space over ℝ is complete:
-/

#synth CompleteSpace ℝ
#synth CompleteSpace (EuclideanSpace ℝ (Fin 3))
#check cauchySeq_tendsto_of_complete
  -- CauchySeq u → ∃ x, Tendsto u atTop (𝓝 x)

/-
Between normed spaces, the interesting maps
are the continuous linear maps, E →L[ℝ] F. As for the morphisms of
2.1.2 and 2.1.4, they are structures (a linear map, plus a proof of
continuity), with a coercion to functions. Moreover, E →L[ℝ] F is
itself a normed space, with the operator norm ‖f‖, the smallest
constant C such that ‖f x‖ ≤ C * ‖x‖ for all x:
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

#check ContinuousLinearMap.le_opNorm     -- ‖f x‖ ≤ ‖f‖ * ‖x‖
#check ContinuousLinearMap.opNorm_le_bound
  -- 0 ≤ M → (∀ x, ‖f x‖ ≤ M * ‖x‖) → ‖f‖ ≤ M

example (f : E →L[ℝ] F) (x y : E) : ‖f x - f y‖ ≤ ‖f‖ * ‖x - y‖ := by
  rw [← map_sub]
  exact f.le_opNorm (x - y)

/-
Note the use of map_sub, which works for continuous linear maps as
for the morphisms of 2.1.2. Now prove the following:
-/

example (f : E →L[ℝ] F) (x : E) (hx : ‖x‖ ≤ 1) : ‖f x‖ ≤ ‖f‖ := by
  sorry

example (f : E →L[ℝ] F) (a : ℝ) (x : E) : ‖f (a • x)‖ ≤ |a| * ‖f‖ * ‖x‖ := by
  sorry

example (f : E →L[ℝ] F) (u : ℕ → E) (x : E) (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => f (u n)) atTop (𝓝 (f x)) := by
  sorry

/-
    (*) In finite dimension, every linear map is continuous
    (LinearMap.continuous_of_finiteDimensional), and all norms are
    equivalent. In infinite dimension, mathlib has the big theorems
    of functional analysis: Hahn-Banach (exists_extension_norm_eq),
    the open mapping theorem (ContinuousLinearMap.isOpenMap), the
    Banach-Steinhaus theorem (banach_steinhaus), Hilbert spaces
    (InnerProductSpace), and much more.
-/

end
