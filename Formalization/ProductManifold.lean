import Mathlib

/-!
# Exercise 1: Products of smooth manifolds and the `n`-torus

**Source:** Exercise sheet, Exercise 1.1 (screenshot from 2026-11-04).

**Informal statement.**
1. Let `M` be an `m`-dimensional and `N` an `n`-dimensional smooth manifold with smooth atlases
   `(Uᵢ, φᵢ)_{i ∈ I}` and `(Vⱼ, ψⱼ)_{j ∈ J}`. Then `M × N`, with the atlas
   `(Uᵢ × Vⱼ, f_{(i,j)} := φᵢ × ψⱼ)_{(i,j) ∈ I × J}`, is a smooth manifold.
2. The stereographic projections form a smooth atlas on `S¹`. In the same way we get a smooth
   atlas on the `n`-torus `Tⁿ = S¹ × ⋯ × S¹`.

**Informal proof.** For charts `f_{(i,j)}, f_{(k,l)}` the transition map is
`f_{(i,j)} ∘ f_{(k,l)}⁻¹ = (φᵢ ∘ φₖ⁻¹) × (ψⱼ ∘ ψₗ⁻¹)`. Both components are smooth (transition maps of
`M` and `N`), so the product map is smooth.

## Modelling choices (to be checked in the review)

* **Manifold = mathlib's `IsManifold I ∞ M`.** This only asks that all transition maps of the
  atlas are `C^∞`. Hausdorff and second countable are *not* part of it (the exercise does not
  check them either).
* **Model spaces.** Part 1 is stated for arbitrary models with corners `I`, `I'` (this includes
  manifolds with boundary). The exercise's case `ℝᵐ`, `ℝⁿ` is `isManifold_prod_euclidean`. There the
  model of `M × N` is `ℝᵐ × ℝⁿ` (`(𝓡 m).prod (𝓡 n)`), which mathlib does not identify with
  `ℝ^{m+n}`. The exercise makes this identification silently.
* **Atlas of `M × N`.** We use mathlib's product charted space. Its atlas is *by definition* the
  set of all `φ × ψ` (see `mem_atlas_prod_iff`), so it is exactly the exercise's atlas.
* **Transition maps.** In Lean, `e.symm ≫ₕ e'` means "first `e⁻¹`, then `e'`", i.e.
  `e' ∘ e⁻¹`. So `f_{(i,j)} ∘ f_{(k,l)}⁻¹` is `f_{(k,l)}.symm ≫ₕ f_{(i,j)}`.
* **Circle.** `S¹ := sphere (0 : ℝ²) 1` with mathlib's stereographic atlas (`atlas_S1`).
* **Torus.** `Tⁿ := Fin n → S¹` (a finite product indexed by `Fin n`), not an iterated binary
  product `S¹ × (S¹ × ⋯)`. Mathlib has no "finite products of smooth manifolds are smooth"
  result, so Part 2 first proves this (`isManifold_pi`) "in the same way" as Part 1.

## Rule for Phase 2

The point of the exercise is the proof itself. So `isManifold_prod` must **not** be closed
with mathlib's instance `IsManifold.prod` (for example via `inferInstance`). Prove it from
the lemmas below.
-/

open Set
open scoped Manifold ContDiff

namespace Formalization.ProductManifold

/-! ## Part 1: The product of two smooth manifolds -/

section Product

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

-- STATEMENT FROZEN
/-- The atlas of `M × N` consists exactly of the product charts `f = φ × ψ`, where `φ` is a chart of
`M` and `ψ` a chart of `N`. This is the atlas `(Uᵢ × Vⱼ, φᵢ × ψⱼ)` from the exercise.

Proof sketch: unfold the definition of `prodChartedSpace` (`atlas = image2 prod …`). -/
lemma mem_atlas_prod_iff (f : OpenPartialHomeomorph (M × N) (ModelProd H H')) :
    f ∈ atlas (ModelProd H H') (M × N) ↔
      ∃ φ ∈ atlas H M, ∃ ψ ∈ atlas H' N, f = φ.prod ψ :=
  -- `atlas (M × N) = image2 prod (atlas M) (atlas N)` by definition
  ⟨fun ⟨φ, hφ, ψ, hψ, h⟩ ↦ ⟨φ, hφ, ψ, hψ, h.symm⟩,
    fun ⟨φ, hφ, ψ, hψ, h⟩ ↦ ⟨φ, hφ, ψ, hψ, h.symm⟩⟩

-- STATEMENT FROZEN
/-- **Transition maps of product charts.**
`(φ × ψ) ∘ (φ' × ψ')⁻¹ = (φ ∘ φ'⁻¹) × (ψ ∘ ψ'⁻¹)`, as open partial homeomorphisms
(with sources and targets).

Proof sketch: `OpenPartialHomeomorph.prod_symm` and `OpenPartialHomeomorph.prod_trans`. -/
lemma prod_symm_trans_prod (φ φ' : OpenPartialHomeomorph M H) (ψ ψ' : OpenPartialHomeomorph N H') :
    (φ'.prod ψ').symm ≫ₕ (φ.prod ψ) = (φ'.symm ≫ₕ φ).prod (ψ'.symm ≫ₕ ψ) := by
  rw [OpenPartialHomeomorph.prod_symm, OpenPartialHomeomorph.prod_trans]

-- STATEMENT FROZEN
/-- **Products of smooth maps are smooth.** If `e` and `e'` are `C^∞` (with `C^∞` inverse) in the
model spaces, then so is `e × e'` in the product model.

Proof sketch: `ContDiffOn.prodMap`, applied to `e` and `e'` and to their inverses. The domains
match because `range (I.prod I') = range I ×ˢ range I'`. (Mathlib lemma: `contDiffGroupoid_prod`.) -/
lemma prod_mem_contDiffGroupoid {e : OpenPartialHomeomorph H H} {e' : OpenPartialHomeomorph H' H'}
    (he : e ∈ contDiffGroupoid ∞ I) (he' : e' ∈ contDiffGroupoid ∞ I') :
    e.prod e' ∈ contDiffGroupoid ∞ (I.prod I') :=
  contDiffGroupoid_prod he he'

-- STATEMENT FROZEN
/-- **Exercise 1.1, Part 1.** The product of two smooth manifolds, with the product atlas,
is a smooth manifold.

Proof sketch: take two charts `f, g` of `M × N`. By `mem_atlas_prod_iff`, `f = φ × ψ` and `g = φ' × ψ'`.
By `prod_symm_trans_prod` the transition map is `(φ'⁻¹ ≫ φ) × (ψ'⁻¹ ≫ ψ)`. Both factors are in
the `C^∞` groupoid (`StructureGroupoid.compatible` on `M` and `N`), so `prod_mem_contDiffGroupoid`
finishes the proof. Do **not** use the instance `IsManifold.prod`. -/
theorem isManifold_prod [IsManifold I ∞ M] [IsManifold I' ∞ N] :
    IsManifold (I.prod I') ∞ (M × N) := by
  -- The transition maps of the product atlas lie in the `C^∞` groupoid.
  have h : HasGroupoid (M × N) (contDiffGroupoid ∞ (I.prod I')) := by
    refine ⟨fun {f g} hf hg ↦ ?_⟩
    -- `f = φ × ψ` and `g = φ' × ψ'` are product charts
    obtain ⟨φ, hφ, ψ, hψ, rfl⟩ := (mem_atlas_prod_iff f).1 hf
    obtain ⟨φ', hφ', ψ', hψ', rfl⟩ := (mem_atlas_prod_iff g).1 hg
    -- the transition map is the product of the transition maps of `M` and `N`
    rw [prod_symm_trans_prod]
    exact prod_mem_contDiffGroupoid ((contDiffGroupoid ∞ I).compatible hφ hφ')
      ((contDiffGroupoid ∞ I').compatible hψ hψ')
  exact { compatible := h.compatible }

-- STATEMENT FROZEN
/-- The exercise's special case: `M` is `m`-dimensional and `N` is `n`-dimensional
(modelled on `ℝᵐ` and `ℝⁿ`, no boundary).

Proof sketch: special case of `isManifold_prod`. -/
theorem isManifold_prod_euclidean {m n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    [IsManifold (𝓡 m) ∞ M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N] :
    IsManifold ((𝓡 m).prod (𝓡 n)) ∞ (M × N) :=
  isManifold_prod

end Product

/-! ## Part 2a: Finite products of smooth manifolds ("in the same way") -/

section Pi

variable {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {H : ι → Type*} [∀ i, TopologicalSpace (H i)] {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
  {M : ι → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]

-- STATEMENT FROZEN
/-- The atlas of `Π i, M i` consists exactly of the product charts `Π i, φ i`, with
`φ i` a chart of `M i`.

Proof sketch: unfold the definition of `piChartedSpace`. -/
lemma mem_atlas_pi_iff (f : OpenPartialHomeomorph (∀ i, M i) (ModelPi H)) :
    f ∈ atlas (ModelPi H) (∀ i, M i) ↔
      ∃ φ : ∀ i, OpenPartialHomeomorph (M i) (H i),
        (∀ i, φ i ∈ atlas (H i) (M i)) ∧ f = OpenPartialHomeomorph.pi φ :=
  -- `atlas (Π i, M i) = pi '' (Set.pi univ (atlas (M i)))` by definition
  ⟨fun ⟨φ, hφ, h⟩ ↦ ⟨φ, fun i ↦ hφ i trivial, h.symm⟩,
    fun ⟨φ, hφ, h⟩ ↦ ⟨φ, fun i _ ↦ hφ i, h.symm⟩⟩

-- STATEMENT FROZEN
/-- **Transition maps of finite product charts** are the products of the transition maps.

Proof sketch: `ext` on source, `toFun` and `invFun`. Compare `PartialEquiv.pi_symm` and
`PartialEquiv.pi_trans`. -/
lemma pi_symm_trans_pi (φ φ' : ∀ i, OpenPartialHomeomorph (M i) (H i)) :
    (OpenPartialHomeomorph.pi φ').symm ≫ₕ OpenPartialHomeomorph.pi φ =
      OpenPartialHomeomorph.pi (fun i ↦ (φ' i).symm ≫ₕ φ i) := by
  apply OpenPartialHomeomorph.toPartialEquiv_injective
  simp [OpenPartialHomeomorph.pi]

/-- Helper: if each `f i` is `C^∞` on `s i` when read in the model `I i`, then `Π i, f i` is `C^∞`
on `Π i, s i` when read in the product model `ModelWithCorners.pi I`. -/
private lemma contDiffOn_pi_model {f : ∀ i, H i → H i} {s : ∀ i, Set (H i)}
    (h : ∀ i, ContDiffOn ℝ ∞ (I i ∘ f i ∘ (I i).symm) ((I i).symm ⁻¹' s i ∩ range (I i))) :
    ContDiffOn ℝ ∞
      (ModelWithCorners.pi I ∘ (fun (x : ModelPi H) i ↦ f i (x i)) ∘ (ModelWithCorners.pi I).symm)
      ((ModelWithCorners.pi I).symm ⁻¹' Set.pi univ s ∩ range (ModelWithCorners.pi I)) := by
  -- a map into a product is `C^∞` iff every component is
  refine contDiffOn_pi.2 fun i ↦ ?_
  -- the `i`-th component is `(I i ∘ f i ∘ (I i).symm) ∘ (projection to the `i`-th factor)`
  refine (h i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := E) i).contDiff.contDiffOn ?_
  rintro x ⟨hxs, y, rfl⟩
  exact ⟨hxs i trivial, y i, rfl⟩

-- STATEMENT FROZEN
/-- **Finite products of smooth maps are smooth.**

Proof sketch: like `contDiffGroupoid_prod`, with `contDiffOn_pi` instead of `ContDiffOn.prodMap`.
Also uses `range (ModelWithCorners.pi I) = Set.pi univ (fun i ↦ range (I i))`. -/
lemma pi_mem_contDiffGroupoid {e : ∀ i, OpenPartialHomeomorph (H i) (H i)}
    (he : ∀ i, e i ∈ contDiffGroupoid ∞ (I i)) :
    (OpenPartialHomeomorph.pi e : OpenPartialHomeomorph (ModelPi H) (ModelPi H)) ∈
      contDiffGroupoid ∞ (ModelWithCorners.pi I) :=
  -- both `Π e i` and its inverse `Π (e i)⁻¹` are `C^∞` in the model
  ⟨contDiffOn_pi_model fun i ↦ (he i).1, contDiffOn_pi_model fun i ↦ (he i).2⟩

-- STATEMENT FROZEN
/-- **Finite products of smooth manifolds are smooth manifolds.** (Not in mathlib.)

Proof sketch: same as `isManifold_prod`, using `mem_atlas_pi_iff`, `pi_symm_trans_pi` and
`pi_mem_contDiffGroupoid`. -/
theorem isManifold_pi [∀ i, IsManifold (I i) ∞ (M i)] :
    IsManifold (ModelWithCorners.pi I) ∞ (∀ i, M i) := by
  have h : HasGroupoid (∀ i, M i) (contDiffGroupoid ∞ (ModelWithCorners.pi I)) := by
    refine ⟨fun {f g} hf hg ↦ ?_⟩
    -- `f = Π φ i` and `g = Π φ' i` are product charts
    obtain ⟨φ, hφ, rfl⟩ := (mem_atlas_pi_iff f).1 hf
    obtain ⟨φ', hφ', rfl⟩ := (mem_atlas_pi_iff g).1 hg
    -- the transition map is the product of the transition maps of the factors
    rw [pi_symm_trans_pi]
    exact pi_mem_contDiffGroupoid fun i ↦ (contDiffGroupoid ∞ (I i)).compatible (hφ i) (hφ' i)
  exact { compatible := h.compatible }

end Pi

/-! ## Part 2b: The circle and the `n`-torus -/

section Torus

-- STATEMENT FROZEN
/-- The circle `S¹`, as the unit sphere in `ℝ²`. -/
abbrev S1 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

-- STATEMENT FROZEN
/-- The `n`-torus `Tⁿ = S¹ × ⋯ × S¹` (`n` factors), as functions `Fin n → S¹`. -/
abbrev Torus (n : ℕ) : Type := Fin n → S1

/-- Technical: `stereographic'` needs to know `dim ℝ² = 1 + 1`. -/
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

-- STATEMENT FROZEN
/-- The charts of `S¹` are exactly the stereographic projections (from every point `v ∈ S¹`).

Proof sketch: holds by definition (`EuclideanSpace.instChartedSpaceSphere`). -/
lemma atlas_S1 :
    atlas (EuclideanSpace ℝ (Fin 1)) S1 = range (fun v : S1 ↦ stereographic' 1 v) := by
  ext f
  exact ⟨fun ⟨v, h⟩ ↦ ⟨v, h.symm⟩, fun ⟨v, h⟩ ↦ ⟨v, h.symm⟩⟩

-- STATEMENT FROZEN
/-- **From the lecture:** the stereographic atlas makes `S¹` a smooth 1-manifold.

Proof sketch: mathlib already has this (`EuclideanSpace.instIsManifoldSphere`, even analytic `ω`).
`inferInstance` is fine here. -/
lemma isManifold_S1 : IsManifold (𝓡 1) ∞ S1 :=
  -- mathlib: the sphere is even analytic (`ω`), and `ω`-manifolds are `C^∞`-manifolds
  inferInstance

-- STATEMENT FROZEN
/-- **Exercise 1.1, Part 2.** The `n`-torus, with the product of stereographic atlases,
is a smooth `n`-manifold.

Proof sketch: `isManifold_pi` with `isManifold_S1` for every factor. -/
theorem isManifold_torus (n : ℕ) :
    IsManifold (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1) ∞ (Torus n) :=
  -- every factor `S¹` is smooth, so the finite product is smooth
  have := isManifold_S1
  isManifold_pi

end Torus

end Formalization.ProductManifold
