import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic

/-! # Exact Sequence Eigenvalues -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ExactSequenceEigenvalues.Construction

/-! Eigenvalues of an operator in an equivariant exact sequence occur
on its subspace or quotient; the same holds after flat scalar extension. -/

open scoped TensorProduct

universe u v w t

theorem eigenvalue_or_of_exact
    {K : Type u} [Field K] {U : Type v} {V : Type w} {W : Type t}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [Module K U] [Module K V] [Module K W]
    (i : U →ₗ[K] V) (p : V →ₗ[K] W) (hi : Function.Injective i)
    (he : Function.Exact i p) (TU : Module.End K U) (TV : Module.End K V) (TW : Module.End K W)
    (hU : ∀ u, i (TU u) = TV (i u)) (hW : ∀ v, p (TV v) = TW (p v))
    (z : K) (hz : TV.HasEigenvalue z) : TU.HasEigenvalue z ∨ TW.HasEigenvalue z := by
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hev : TV v = z • v := Module.End.mem_eigenspace_iff.mp hv.1
  by_cases hp : p v = 0
  · have hm : v ∈ LinearMap.range i := by
      rw [← he.linearMap_ker_eq]
      exact hp
    obtain ⟨u, hu⟩ := hm
    apply Or.inl
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := u)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · apply hi
      rw [hU, hu, hev, map_smul, hu]
    · intro h
      apply hv.2
      rw [← hu, h, map_zero]
  · apply Or.inr
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := p v)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hp⟩
    rw [← hW, hev, map_smul]

theorem baseChange_eigenvalue_or_of_exact
    {R K : Type u} [CommRing R] [Field K] [Algebra R K] [Module.Flat R K]
    {U : Type v} {V : Type w} {W : Type t}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [Module R U] [Module R V] [Module R W]
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (hi : Function.Injective i)
    (he : Function.Exact i p) (hp : Function.Surjective p)
    (TU : Module.End R U) (TV : Module.End R V) (TW : Module.End R W)
    (hU : ∀ u, i (TU u) = TV (i u)) (hW : ∀ v, p (TV v) = TW (p v))
    (z : K) (hz : Module.End.HasEigenvalue (TV.baseChange K) z) :
    Module.End.HasEigenvalue (TU.baseChange K) z ∨ Module.End.HasEigenvalue (TW.baseChange K) z := by
  have hix : Function.Injective (i.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hi
  have hex : Function.Exact (i.baseChange K) (p.baseChange K) :=
    _root_.lTensor_exact K he hp
  apply eigenvalue_or_of_exact (i.baseChange K) (p.baseChange K) hix hex
    (TU.baseChange K) (TV.baseChange K) (TW.baseChange K) ?_ ?_ z hz
  · intro x
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      change r ⊗ₜ[R] i (TU x) = r ⊗ₜ[R] TV (i x)
      rw [hU]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro x
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      change r ⊗ₜ[R] p (TV x) = r ⊗ₜ[R] TW (p x)
      rw [hW]
    | add x y hx hy => simp only [map_add, hx, hy]

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ExactSequenceEigenvalues.Construction
