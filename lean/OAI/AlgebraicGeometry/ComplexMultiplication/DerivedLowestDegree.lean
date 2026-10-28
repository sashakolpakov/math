import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Derived Lowest Degree -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.DerivedLowestDegree

noncomputable section

/-! # Actual derived morphisms into the lowest supported degree

For a complex supported in degrees at least n, every derived morphism from
an object placed in degree n is represented by an actual morphism of complexes.
This applies to the original F¹ de Rham complex after shifting by one.
-/

open _root_.CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

set_option backward.isDefEq.respectTransparency false in
/-- Derived morphisms out of a single object have actual complex representatives
when the target has no terms below that object's degree. -/
theorem derivedMap_surjective_from_single (A : C) (K : CochainComplex C ℤ)
    (n : ℤ) [K.IsStrictlyGE n] :
    Function.Surjective
      (fun f : (CochainComplex.singleFunctor C n).obj A ⟶ K => DerivedCategory.Q.map f) := by
  intro f
  obtain ⟨X, _, _, s, _, g, rfl⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE n n f
  obtain ⟨A₀, ⟨e⟩⟩ := X.exists_iso_single n
  have ⟨φ, hφ⟩ := (CochainComplex.singleFunctor C n).map_surjective (e.inv ≫ s)
  have : IsIso ((DerivedCategory.singleFunctor C n).map φ) := by
    change IsIso (DerivedCategory.Q.map ((CochainComplex.singleFunctor C n).map φ))
    rw [hφ, Functor.map_comp]
    infer_instance
  have : IsIso φ :=
    (NatIso.isIso_map_iff (DerivedCategory.singleFunctorCompHomologyFunctorIso C n) φ).1
      (by dsimp; infer_instance)
  have : IsIso (e.inv ≫ s) := by rw [← hφ]; infer_instance
  have : IsIso s := IsIso.of_isIso_comp_left e.inv s
  exact ⟨inv s ≫ g, by simp only [Functor.map_comp, Functor.map_inv]⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.DerivedLowestDegree
