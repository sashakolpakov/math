import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.OperationsIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FamilyGroup.BaseChangeEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.ProductComparisonNaturality

/-! # Geometric Family Group Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual base change of native family operations agrees with base change of their multiplication, inversion, and unit data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {U T : Over S} {A : Over S} (f : U ⟶ T)

def FamilyGroup.Operations.FamilyGroupOperations.geometricBaseChange (D : FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback T.hom).obj A)) :
    FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback U.hom).obj A) :=
  (D.baseChange f.left).ofIso (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).symm

theorem FamilyGroup.Operations.FamilyGroupOperations.geometricBaseChange_laws_iff
    (D : FamilyGroup.Operations.FamilyGroupOperations ((Over.pullback T.hom).obj A)) :
    (D.geometricBaseChange f).Laws ↔ (D.baseChange f.left).Laws :=
  (D.baseChange f.left).ofIso_laws_iff (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).symm

theorem Geometric.GeometricFamilyGroupOperations.familyProductComparison_tensor_natural :
    ((Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom ⊗ₘ (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom) ≫
        (Functor.Monoidal.μIso (Over.pullback f.left)
          ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj A)).hom ≫
        (Over.pullback f.left).map (Functor.Monoidal.μIso (Over.pullback T.hom) A A).hom =
      (Functor.Monoidal.μIso (Over.pullback U.hom) A A).hom ≫
        (Single.ParameterBaseChange.singleParameterBaseChangeIso f (A ⊗ A)).hom := by
  rw [← Category.assoc, Product.ParameterTensorIso.productParameterBaseChangeIso_tensor]
  exact (Family.ProductComparisonNaturality.familyProductComparison_natural f A A).symm

theorem Geometric.GeometricFamilyGroupOperations.familyOperationData_geometricBaseChange
    (m : (Over.pullback T.hom).obj (A ⊗ A) ⟶ (Over.pullback T.hom).obj A)
    (i : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj A) (p : T ⟶ A) :
    (Intrinsic.FamilyOperationData.familyOperationDataEquiv A T ((m, i), p)).geometricBaseChange f =
      Intrinsic.FamilyOperationData.familyOperationDataEquiv A U ((Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange f m,
        Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange f i), f ≫ p) := by
  apply FamilyGroup.Operations.FamilyGroupOperations.ext
  · change (Functor.LaxMonoidal.ε (Over.pullback f.left) ≫
        (Over.pullback f.left).map (Family.PointSectionEquivalence.familyPointSectionEquiv A T p)) ≫
        (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).inv = Family.PointSectionEquivalence.familyPointSectionEquiv A U (f ≫ p)
    rw [← Family.PointSectionNaturality.familyPointSection_natural f A p, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change ((Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom ⊗ₘ (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom) ≫
        (Functor.Monoidal.μIso (Over.pullback f.left)
          ((Over.pullback T.hom).obj A) ((Over.pullback T.hom).obj A)).hom ≫
        (Over.pullback f.left).map ((Functor.Monoidal.μIso (Over.pullback T.hom) A A).hom ≫ m) ≫
        (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).inv =
      (Functor.Monoidal.μIso (Over.pullback U.hom) A A).hom ≫
        (Single.ParameterBaseChange.singleParameterBaseChangeIso f (A ⊗ A)).hom ≫ (Over.pullback f.left).map m ≫
        (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).inv
    rw [Functor.map_comp]
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ (Over.pullback f.left).map m ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).inv)
      (Geometric.GeometricFamilyGroupOperations.familyProductComparison_tensor_natural (A := A) f)
  · rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
