import OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardInjectiveResolution
import OAI.AlgebraicGeometry.Comparison.Betti.PushforwardGlobalSections
import OAI.AlgebraicGeometry.SheafCohomology.Cech.DerivedGlobalSections

/-! # Pushforward Cohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardCohomology.Cech

noncomputable section

/-! Actual abelian sheaf cohomology is unchanged by direct image along a closed embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsInducing f)
  (hclosed : IsClosed (Set.range f)) (F : TopCat.Sheaf AddCommGrpCat.{0} X)

include hf hclosed

local instance closedGlobalSections_additive (Z : TopCat.{0}) :
    (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Z).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology Z) AddCommGrpCat.{0}).right_adjoint_additive

def closedPushforwardRightDerivedGlobalSectionsIso (n : ℕ) :
    ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Y).rightDerived n).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) ≅
      ((SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).rightDerived n).obj F := by
  let I : InjectiveResolution F := injectiveResolution (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F)
  let GX : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
    SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X
  let GY : TopCat.Sheaf AddCommGrpCat.{0} Y ⥤ AddCommGrpCat.{0} :=
    SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Y
  have : GX.Additive := inferInstanceAs (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive
  have : GY.Additive := inferInstanceAs (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor Y).Additive
  exact (PushforwardInjectiveResolution.Cech.closedPushedInjectiveResolution f hf hclosed F).isoRightDerivedObj GY n ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n).mapIso
      (PushforwardGlobalSections.Cech.pushforwardGlobalSectionsComplexIso f I.cocomplex) ≪≫
    (I.isoRightDerivedObj GX n).symm

def closedPushforwardCohomologyEquiv (n : ℕ) :
    Sheaf.H (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F)) n ≃+
      Sheaf.H (SheafCohomology.Cech.Compat.TopCat.Sheaf.toSiteSheaf F) n :=
  (SheafCohomology.Cech.Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections _ n).trans
    ((closedPushforwardRightDerivedGlobalSectionsIso f hf hclosed F n).addCommGroupIsoToAddEquiv.trans
      (SheafCohomology.Cech.Compat.TopCat.Sheaf.H.addEquivRightDerivedGlobalSections F n).symm)

theorem closedPushforward_cohomology_subsingleton (n : ℕ) [Subsingleton (Sheaf.H F n)] :
    Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n) :=
  (closedPushforwardCohomologyEquiv f hf hclosed F n).injective.subsingleton

theorem closedSource_cohomology_subsingleton (n : ℕ)
    [Subsingleton (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n)] :
    Subsingleton (Sheaf.H F n) :=
  (closedPushforwardCohomologyEquiv f hf hclosed F n).symm.injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.Closed.PushforwardCohomology.Cech
