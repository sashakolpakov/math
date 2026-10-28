import Mathlib

/-! # Evaluation Relations -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.EvaluationRelations.CM

/-! Linear relations between finite products of function values persist
under arbitrary linear functionals on the factors. This is the algebraic
step needed to descend local operators to actual adelic functions. -/

open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)] {X : I → Type*}
  (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ)) (he : ∀ i, Function.Injective (e i))

def evaluation (i : I) (x : X i) : V i →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (e i)

omit [Fintype I] [Fintype J] in
include he in
theorem evaluation_span (i : I) :
    Submodule.span ℂ (Set.range (evaluation e i)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro z hz
  have hne : e i z ≠ 0 := by
    intro h
    apply hz
    exact he i (h.trans (map_zero (e i)).symm)
  obtain ⟨x, hx⟩ : ∃ x : X i, e i z x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact ⟨evaluation e i x, ⟨x, rfl⟩, hx⟩

def functionalProduct (u : ∀ i, V i) :
    MultilinearMap ℂ (fun i => V i →ₗ[ℂ] ℂ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap (fun i => LinearMap.applyₗ (u i))

omit [∀ i, FiniteDimensional ℂ (V i)] in
theorem functionalProduct_apply (u : ∀ i, V i) (l : ∀ i, V i →ₗ[ℂ] ℂ) :
    functionalProduct u l = ∏ i, l i (u i) := rfl

include he in
theorem relation_functionals (c : J → ℂ) (u : J → ∀ i, V i)
    (h : ∀ x : ∀ i, X i, ∑ j, c j * ∏ i, e i (u j i) (x i) = 0)
    (l : ∀ i, V i →ₗ[ℂ] ℂ) :
    ∑ j, c j * ∏ i, l i (u j i) = 0 := by
  let T : MultilinearMap ℂ (fun i => V i →ₗ[ℂ] ℂ) ℂ :=
    ∑ j, c j • functionalProduct (u j)
  have hT : T = 0 := by
    apply MultilinearMap.ext_of_span_eq_top (fun i => evaluation_span e he i)
    intro x
    change T (fun i => evaluation e i (x i)) = 0
    simpa only [T, sum_apply, smul_apply, smul_eq_mul,
      functionalProduct_apply, evaluation, LinearMap.comp_apply, LinearMap.proj_apply] using h x
  have hv := congrArg (fun f : MultilinearMap ℂ (fun i => V i →ₗ[ℂ] ℂ) ℂ => f l) hT
  simpa only [T, sum_apply, smul_apply, smul_eq_mul,
    functionalProduct_apply, zero_apply] using hv

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.EvaluationRelations.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.EvaluationRelations.CM.FunctionFamily

/-! A finite family of functions only uses a finite-dimensional subspace,
so relations between its products persist under any local linear operators. -/

open scoped Classical

variable {I J : Type*} [Fintype I] [Fintype J]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {X : I → Type*} (e : ∀ i, V i →ₗ[ℂ] (X i → ℂ))
  (he : ∀ i, Function.Injective (e i))

include he in
theorem relation_functionals (c : J → ℂ) (u : J → ∀ i, V i)
    (h : ∀ x : ∀ i, X i, ∑ j, c j * ∏ i, e i (u j i) (x i) = 0)
    (l : ∀ i, V i →ₗ[ℂ] ℂ) :
    ∑ j, c j * ∏ i, l i (u j i) = 0 := by
  let W (i : I) : Submodule ℂ (V i) := Submodule.span ℂ (Set.range fun j => u j i)
  let (i : I) : FiniteDimensional ℂ (W i) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range fun j => u j i)
  let e' (i : I) : W i →ₗ[ℂ] (X i → ℂ) := (e i).comp (W i).subtype
  have he' (i : I) : Function.Injective (e' i) := (he i).comp Subtype.val_injective
  let u' (j : J) (i : I) : W i := ⟨u j i, Submodule.subset_span ⟨j, rfl⟩⟩
  exact CM.relation_functionals e' he' c u' h
    (fun i => (l i).comp (W i).subtype)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.EvaluationRelations.CM.FunctionFamily

end

end OAI
