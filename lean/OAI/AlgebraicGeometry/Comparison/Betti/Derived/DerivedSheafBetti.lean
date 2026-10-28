import OAI.AlgebraicGeometry.Comparison.Betti.SingularInjective
import OAI.AlgebraicGeometry.Comparison.Betti.ConstantSheafSections
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveHomologyExt

/-! # Derived Sheaf Betti -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.DerivedSheafBetti

noncomputable section

/-!
# Derived constant-sheaf cohomology and actual Betti cohomology

The comparison is induced by the original singular cochains, their sheaf
resolution, the normalized injective comparison, and the explicit cocycle
description of derived morphisms. No comparison isomorphism is an input.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
open _root_.TopologicalSpace

variable (M : TopCat.{0})

instance complexSheavesDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves M) :=
  HasDerivedCategory.standard _

instance complexSheavesExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves M) :=
  hasExt_of_hasDerivedCategory _

def constantDerivedCohomology (n : ℕ) : ModuleCat.{1} ℂ :=
  ModuleCat.of ℂ
    ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).obj (ConstantSheafSections.standardConstantSheaf M) ⟶
      ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).obj
        (ConstantSheafSections.standardConstantSheaf M))⟦(n : ℤ)⟧)

variable [StronglyLocallyContractibleSpace M] [MetrizableSpace M]

def singularDerivedConstantLinearEquiv (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) M n ≃ₗ[ℂ] constantDerivedCohomology M n := by
  let Z : ConstantSheafSections.ComplexSheaves M := AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M
  let I : InjectiveResolution Z :=
    SingularInjective.singularInjectiveResolution M
  let K : CochainComplex (ConstantSheafSections.ComplexSheaves M) ℕ := I.cocomplex
  let e₁ := SingularInjective.singularInjectiveSectionsCohomologyIso M n
  let e₂ := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) n).mapIso
    (ConstantSheafSections.constantHomSectionsComplexIso K).symm
  let e₃ := InjectiveHomologyExt.homologyExtLinearEquiv (C := ConstantSheafSections.ComplexSheaves M)
    (R := ℂ) (X := ConstantSheafSections.standardConstantSheaf M) I n
  let e₄ := Ext.homLinearEquiv (C := ConstantSheafSections.ComplexSheaves M) (R := ℂ)
    (X := ConstantSheafSections.standardConstantSheaf M) (Y := Z) (n := n)
  let ec : Z ≅ ConstantSheafSections.standardConstantSheaf M :=
    (Analysis.DifferentialForms.Manifold.DeRhamResolution.constantComplexLocallyConstantIsoOn M).symm
  let et := (shiftFunctor (DerivedCategory (ConstantSheafSections.ComplexSheaves M)) (n : ℤ)).mapIso
    ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves M) 0).mapIso ec)
  exact e₁.toLinearEquiv.trans (e₂.toLinearEquiv.trans
    (e₃.trans (e₄.trans (Linear.homCongr ℂ (Iso.refl _) et))))

/-- The universe lift changes only the universe of the actual singular cohomology. -/
def singularConstantCohomologyIso (n : ℕ) :
    (ModuleCat.uliftFunctor.{1, 0} ℂ).obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) M n) ≅
      constantDerivedCohomology M n :=
  (ULift.moduleEquiv.trans (singularDerivedConstantLinearEquiv M n)).toModuleIso

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.DerivedSheafBetti
