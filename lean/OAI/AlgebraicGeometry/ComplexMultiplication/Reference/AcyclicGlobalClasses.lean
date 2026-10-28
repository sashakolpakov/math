import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.LowestDegreeClasses
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.DerivedRepresentatives

/-! # Acyclic Global Classes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AcyclicGlobalClasses

noncomputable section

/-! # Original global classes represent Ext-acyclic hypercohomology in every degree -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry ComplexPoint
open _root_.CochainComplex.HomComplex

universe v u w w'

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C]

/-- The existing normalized cocycle representative gives the original Hom-complex class. -/
theorem cohomologyClassToDerived_surjective_of_term_ext_vanish (A : C)
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyGE b]
    (hExt : ∀ p q, Subsingleton (Ext A (K.X p) (q + 1))) (n : ℤ) :
    Function.Surjective
      (HomPostcomp.cohomologyClassToDerived ((CochainComplex.singleFunctor C 0).obj A) K n) := by
  intro a
  obtain ⟨f, hf, hfa⟩ := Comparison.Betti.Acyclic.DerivedRepresentatives.Ext.exists_derived_cocycle_representative
    A K b hExt n a
  let g := Comparison.Betti.SingleCocycleFunctor.Ext.singleCocycleHom f hf
  refine ⟨CohomologyClass.mk (Cocycle.equivHomShift g), ?_⟩
  rw [HomPostcomp.cohomologyClassToDerived_mk]
  exact (congrArg (fun h : ShiftedHom ((CochainComplex.singleFunctor C 0).obj A) K n =>
    h.map DerivedCategory.Q) (Cocycle.equivHomShift.symm_apply_apply g)).trans hfa

end General

variable (X : Over (Spec (.of ℂ)))

local instance CMOriginalAcyclicGlobalClasses.localInstance1 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _
local instance CMOriginalAcyclicGlobalClasses.localInstance2 : HasExt.{1} (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) := HasExt.standard _

/-- Preserve the original integer-constant source and the original derived transport. -/
theorem homComplexClassToHypercohomology_surjective_of_term_ext_vanish
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (b : ℤ) [K.IsStrictlyGE b]
    (hExt : ∀ p q, Subsingleton (Ext.{1}
      ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj (AddCommGrpCat.of ℤ))
        (K.X p) (q + 1))) (n : ℤ) :
    Function.Surjective (GlobalNaturality.homComplexClassToHypercohomology X K n) := by
  intro α
  let e : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n ≃
      ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n :=
    Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
  let c := DerivedCategory.Q.mapIso (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X)
  obtain ⟨z, hz⟩ := cohomologyClassToDerived_surjective_of_term_ext_vanish
    (C := ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)
    ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj (AddCommGrpCat.of ℤ))
    K b hExt n (c.inv ≫ e α)
  refine ⟨z, ?_⟩
  apply e.injective
  have h₁ := GlobalNaturality.homComplexClassToHypercohomology_equiv X K n z
  exact h₁.trans ((congrArg (fun γ : ShiftedHom
    (DerivedCategory.Q.obj (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))) (DerivedCategory.Q.obj K) n => c.hom ≫ γ) hz).trans
        (c.hom_inv_id_assoc (e α)))

/-- Every original hypercohomology class has an actual global-section class representative. -/
theorem globalSectionsToHypercohomology_surjective_of_term_ext_vanish
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (b : ℤ) [K.IsStrictlyGE b]
    (hExt : ∀ p q, Subsingleton (Ext.{1}
      ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj (AddCommGrpCat.of ℤ))
        (K.X p) (q + 1))) (n : ℤ) :
    Function.Surjective (GlobalNaturality.globalSectionsToHypercohomology X K n) :=
  (homComplexClassToHypercohomology_surjective_of_term_ext_vanish X K b hExt n).comp
    (GlobalNaturality.globalSectionsToHomComplexClass X K n).surjective

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AcyclicGlobalClasses
