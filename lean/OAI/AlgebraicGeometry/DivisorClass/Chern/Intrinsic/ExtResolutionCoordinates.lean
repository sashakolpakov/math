import OAI.AlgebraicGeometry.DivisorClass.Chern.ResolutionExtensionSections
import OAI.AlgebraicGeometry.DivisorClass.Chern.GammaSectionsComparison

/-! # Ext Resolution Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ExtResolutionCoordinates

noncomputable section

/-! Expand the existing native sheaf-cohomology comparison in actual resolution coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open _root_.CochainComplex _root_.CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

local instance nativeExtCoordinates_additive : (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).Additive :=
  (constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).right_adjoint_additive

def nativeExtResolutionEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ) :
    CategoryTheory.Sheaf.H F (n + 1) ≃+
      (FlasqueCechD.abelianDerivedSectionsComplex (injectiveResolution F).cocomplex).homology (n + 1) :=
  let R := injectiveResolution F
  let G := SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X
  let HZ := HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (.up ℤ) (n + 1)
  (R.extAddEquivCohomologyClass (X := Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)).trans
    ((homologyAddEquiv ((singleFunctor (TopCat.Sheaf AddCommGrpCat.{0} X) 0).obj
      (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X)) R.cochainComplex (n + 1)).symm.trans
      (((HZ.mapIso (HomComplexSections.nativeHomComplexSectionsIso R.cochainComplex)).addCommGroupIsoToAddEquiv).trans
        (((HZ.mapIso (ResolutionExtensionSections.resolutionMapExtendIso (G := G) R.cocomplex)).addCommGroupIsoToAddEquiv).trans
          ((((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat
              (show ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ) from rfl)).addCommGroupIsoToAddEquiv))))

theorem nativeInjectiveCohomologyIso_inv_coordinates (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (n : ℕ) (a : CategoryTheory.Sheaf.H F (n + 1)) :
    (GammaSectionsComparison.nativeInjectiveCohomologyIso F n).inv a = nativeExtResolutionEquiv F n a := by
  let R := injectiveResolution F
  let G := SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X
  let : G.Additive := nativeExtCoordinates_additive
  change (R.isoRightDerivedObj G (n + 1)).hom
    ((R.isoRightDerivedObj G (n + 1)).inv (nativeExtResolutionEquiv F n a)) = _
  exact (R.isoRightDerivedObj G (n + 1)).inv_hom_id_apply _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ExtResolutionCoordinates
