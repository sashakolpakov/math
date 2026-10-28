import OAI.AlgebraicGeometry.ComplexMultiplication.DerivedShiftedLowestDegree
import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality

/-! # Lowest Degree Classes -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.LowestDegreeClasses

noncomputable section

/-! # Original lowest-degree hypercohomology classes come from global classes

This uses actual derived morphism representatives and the unchanged original
integer-constant source comparison, rather than a supplied global resolution.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open _root_.CochainComplex.HomComplex

universe v u

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- Lowest-degree derived classes are actual original Hom-complex classes. -/
theorem cohomologyClassToDerived_surjective_from_single (A : C)
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    Function.Surjective
      (HomPostcomp.cohomologyClassToDerived ((CochainComplex.singleFunctor C 0).obj A) K n) := by
  intro f
  obtain ⟨g, rfl⟩ := DerivedShiftedLowestDegree.shiftedDerivedMap_surjective_from_single A K n f
  refine ⟨CohomologyClass.mk (Cocycle.equivHomShift g), ?_⟩
  rw [HomPostcomp.cohomologyClassToDerived_mk]
  exact congrArg (fun h : ShiftedHom ((CochainComplex.singleFunctor C 0).obj A) K n =>
    h.map DerivedCategory.Q) (Cocycle.equivHomShift.symm_apply_apply g)

end General

variable (X : Over (Spec (.of ℂ)))

local instance CMOriginalLowestDegreeClasses.localInstance1 : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

/-- The original integer source transport gives genuine lowest-degree hypercohomology classes. -/
theorem homComplexClassToHypercohomology_surjective_of_isStrictlyGE
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    Function.Surjective (GlobalNaturality.homComplexClassToHypercohomology X K n) := by
  intro α
  let e : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X K n ≃
      ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n :=
    Localization.SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q
  let c := DerivedCategory.Q.mapIso (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X)
  obtain ⟨z, hz⟩ := cohomologyClassToDerived_surjective_from_single (C := ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)
    ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj (AddCommGrpCat.of ℤ))
    K n (c.inv ≫ e α)
  refine ⟨z, ?_⟩
  apply e.injective
  have h₁ : e (GlobalNaturality.homComplexClassToHypercohomology X K n z) =
      c.hom ≫ HomPostcomp.cohomologyClassToDerived
        (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) K n z :=
    GlobalNaturality.homComplexClassToHypercohomology_equiv X K n z
  have h₂ : HomPostcomp.cohomologyClassToDerived
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) K n z =
      c.inv ≫ e α := hz
  exact h₁.trans
    ((congrArg (fun γ : ShiftedHom
      (DerivedCategory.Q.obj (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))))
        (DerivedCategory.Q.obj K) n => c.hom ≫ γ) h₂).trans (c.hom_inv_id_assoc (e α)))

/-- Actual cohomology of the original global-section complex surjects in its lowest degree. -/
theorem globalSectionsToHypercohomology_surjective_of_isStrictlyGE
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    Function.Surjective (GlobalNaturality.globalSectionsToHypercohomology X K n) :=
  (homComplexClassToHypercohomology_surjective_of_isStrictlyGE X K n).comp
    (GlobalNaturality.globalSectionsToHomComplexClass X K n).surjective

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.LowestDegreeClasses
