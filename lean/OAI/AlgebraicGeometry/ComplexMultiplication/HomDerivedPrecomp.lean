import OAI.AlgebraicGeometry.ComplexMultiplication.HomPostcomp

/-! # Hom Derived Precomp -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomDerivedPrecomp

noncomputable section

/-! # Precomposition of original Hom-complex classes and derived morphisms -/

open _root_.CategoryTheory

open _root_.CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Original Hom-complex class precomposition gives actual derived precomposition. -/
theorem cohomologyClassToDerived_precomp {A A' K : CochainComplex C ℤ}
    (g : A' ⟶ A) (n : ℤ) (z : CohomologyClass A K n) :
    HomPostcomp.cohomologyClassToDerived A' K n (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompClass g K n z) =
      DerivedCategory.Q.map g ≫ HomPostcomp.cohomologyClassToDerived A K n z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompClass_mk, HomPostcomp.cohomologyClassToDerived_mk, HomPostcomp.cohomologyClassToDerived_mk,
    Cocycle.equivHomShift_symm_precomp]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomDerivedPrecomp
