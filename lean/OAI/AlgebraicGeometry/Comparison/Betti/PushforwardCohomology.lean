import OAI.AlgebraicGeometry.Comparison.Betti.PushforwardInjectiveResolution
import OAI.AlgebraicGeometry.Comparison.Betti.PushforwardGlobalSections
import OAI.AlgebraicGeometry.SheafCohomology.Cech.DerivedGlobalSections

/-! # Pushforward Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PushforwardCohomology.Cech

noncomputable section

/-! Cohomology of direct image under local acyclicity, computed through actual resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
  (hlocal : ∀ (V : Opens Y) (y : V), ∃ W : Opens Y, W ≤ V ∧ y.val ∈ W ∧
    ∀ q, Subsingleton (Sheaf.H
      ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat ((Opens.map f).obj W).isOpenEmbedding).obj F) (q + 1)))

local instance (Z : TopCat.{u}) : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Z).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).right_adjoint_additive

def pushforwardRightDerivedGlobalSectionsIso (n : ℕ) :
    ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Y).rightDerived n).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) ≅
    ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived n).obj F := by
  let I : InjectiveResolution F := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
  let GX : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X
  let GY : TopCat.Sheaf AddCommGrpCat.{u} Y ⥤ AddCommGrpCat.{u} :=
    SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Y
  have : GX.Additive := inferInstanceAs (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive
  have : GY.Additive := inferInstanceAs (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Y).Additive
  exact (PushforwardInjectiveResolution.Cech.pushedInjectiveResolution f F hlocal).isoRightDerivedObj
      GY n ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n).mapIso
      (PushforwardGlobalSections.Cech.pushforwardGlobalSectionsComplexIso f I.cocomplex) ≪≫
    (I.isoRightDerivedObj GX n).symm

def pushforwardCohomologyEquiv (n : ℕ) :
    Sheaf.H (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F)) n ≃+
      Sheaf.H (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F) n :=
  (SheafCohomology.Cech.Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections _ n).trans
    ((pushforwardRightDerivedGlobalSectionsIso f F hlocal n).addCommGroupIsoToAddEquiv.trans
      (SheafCohomology.Cech.Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections F n).symm)

include hlocal in
theorem pushforward_cohomology_subsingleton (n : ℕ) [Subsingleton (Sheaf.H F n)] :
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n) :=
  (pushforwardCohomologyEquiv f F hlocal n).injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.PushforwardCohomology.Cech
