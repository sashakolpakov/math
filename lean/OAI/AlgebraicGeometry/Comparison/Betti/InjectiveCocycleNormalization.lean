import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.HomCocycleClasses
import OAI.AlgebraicGeometry.Comparison.Betti.SingleCocycleFunctor

/-! # Injective Cocycle Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.InjectiveCocycleNormalization.Ext

noncomputable section

/-! The derived Hom equivalence retains the actual single-complex cocycle representative. -/

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (A : C) (K : CochainComplex C ℤ) [K.IsKInjective] (n : ℤ)

theorem kInjectiveCohomologyClassDerivedEquiv_mk
    (z : Cocycle ((CochainComplex.singleFunctor C 0).obj A) K n) :
    InjectiveHomCohomology.Ext.kInjectiveCohomologyClassDerivedEquiv A K n (CohomologyClass.mk z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  let S := (CochainComplex.singleFunctor C 0).obj A
  let c := Cocycle.equivHomShift.symm z
  change ((DerivedCategory.quotientCompQhIso C).inv.app S ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map c)) ≫
      ((DerivedCategory.quotientCompQhIso C).hom.app (K⟦n⟧) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app K) =
      DerivedCategory.Q.map c ≫ (DerivedCategory.Q.commShiftIso n).hom.app K
  rw [Category.assoc, DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  exact ((DerivedCategory.quotientCompQhIso C).app S).inv_hom_id_assoc _

theorem kInjectiveHomCohomologyDerivedEquiv_class
    (f : A ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    InjectiveHomCohomology.Ext.kInjectiveHomCohomologyDerivedEquiv A K n
      (AbCochainClasses.Homology.cochainClass (IntegerAcyclicHomComplex.Ext.integerHomComplex A K) n f hf) =
        ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf) DerivedCategory.Q := by
  exact (congrArg (InjectiveHomCohomology.Ext.kInjectiveCohomologyClassDerivedEquiv A K n)
    (HomCocycleClasses.Ext.integerHomCohomologyClassEquiv_class A K n f hf)).trans
      (kInjectiveCohomologyClassDerivedEquiv_mk A K n
        (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf))

end

end OAI.AlgebraicGeometry.Comparison.Betti.InjectiveCocycleNormalization.Ext
