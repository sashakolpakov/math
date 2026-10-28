import OAI.AlgebraicGeometry.Comparison.Betti.Cech.FactorSections
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Functor

/-! # Cech Sections Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechSectionsFunctor

noncomputable section

/-! Global sections of the actual sheaf Čech resolution, naturally in its coefficient sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)

def sheafCechSectionsFunctorIso :
    CechFunctor.sheafCechResolutionFunctor U ⋙ Cech.FactorSections.sheafTopSections.mapHomologicalComplex (.up ℕ) ≅
      TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ cechComplexFunctor U := by
  let A := CechFunctor.sheafCechFactorFunctor (X := X)
  let B : ((Opens X)ᵒᵖ ⥤ TopCat.Sheaf AddCommGrpCat.{0} X) ⥤
      CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ := cechComplexFunctor U
  let C := (Cech.FactorSections.sheafTopSections (X := X)).mapHomologicalComplex (.up ℕ)
  let D := (Functor.whiskeringRight (Opens X)ᵒᵖ
    (TopCat.Sheaf AddCommGrpCat.{0} X) AddCommGrpCat.{0}).obj Cech.FactorSections.sheafTopSections
  let E : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
    cechComplexFunctor U
  exact Functor.associator A B C ≪≫
    Functor.isoWhiskerLeft A (Cech.Functor.cechComplexFunctorComparison Cech.FactorSections.sheafTopSections U) ≪≫
    (Functor.associator A D E).symm ≪≫
    Functor.isoWhiskerRight Cech.FactorSections.sheafCechFactorGlobalFunctorIso E

def sheafCechSectionsIso (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (Cech.FactorSections.sheafTopSections.mapHomologicalComplex (.up ℕ)).obj
        ((CechFunctor.sheafCechResolutionFunctor U).obj F) ≅
      (cechComplexFunctor U).obj F.obj :=
  (sheafCechSectionsFunctorIso U).app F

theorem sheafCechSectionsIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (f : F ⟶ G) :
    (Cech.FactorSections.sheafTopSections.mapHomologicalComplex (.up ℕ)).map
        ((CechFunctor.sheafCechResolutionFunctor U).map f) ≫ (sheafCechSectionsIso U G).hom =
      (sheafCechSectionsIso U F).hom ≫ (cechComplexFunctor U).map f.hom :=
  (sheafCechSectionsFunctorIso U).hom.naturality f

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechSectionsFunctor
