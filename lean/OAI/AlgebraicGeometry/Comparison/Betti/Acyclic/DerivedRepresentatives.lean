import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.CocycleNormalization

/-! # Derived Representatives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.DerivedRepresentatives.Ext

noncomputable section

/-! Every derived class in a bounded-below complex of Ext-acyclic objects
has an actual cocycle representative, with the original derived normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]

theorem exists_derived_cocycle_representative (A : C) (K : CochainComplex C ℤ)
    (b : ℤ) [K.IsStrictlyGE b]
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (n : ℤ)
    (a : (DerivedCategory.singleFunctor C 0).obj A ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    ∃ (f : A ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0),
      ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf) DerivedCategory.Q = a := by
  let e := HomDerived.Ext.acyclicHomCohomologyDerivedEquiv A K b hExt n
  obtain ⟨f, hf, he⟩ := AbCochainClasses.Homology.cochainClass_surjective (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n (e.symm a)
  refine ⟨f, hf, ?_⟩
  rw [← CocycleNormalization.Ext.acyclicHomCohomologyDerivedEquiv_class A K b hExt n f hf]
  change e (AbCochainClasses.Homology.cochainClass (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n f hf) = a
  rw [he, e.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.DerivedRepresentatives.Ext
