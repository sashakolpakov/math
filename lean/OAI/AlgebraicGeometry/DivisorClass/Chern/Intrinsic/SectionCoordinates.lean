import OAI.AlgebraicGeometry.DivisorClass.Chern.GammaSectionsComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionClasses

/-! # Section Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCoordinates

noncomputable section

/-! The native representing-object coordinates agree with actual sections on the top open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem homEquiv_comp_rightAdjointUniq
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G G' : D ⥤ C}
    (A : F ⊣ G) (B : F ⊣ G') {Z : C} {Y : D} (f : F.obj Z ⟶ Y) :
    A.homEquiv Z Y f ≫ (A.rightAdjointUniq B).hom.app Y = B.homEquiv Z Y f := by
  rw [A.homEquiv_unit, B.homEquiv_unit, Category.assoc,
    (A.rightAdjointUniq B).hom.naturality, ← Category.assoc,
    A.unit_rightAdjointUniq_hom_app B]

variable {X : TopCat.{0}}

def nativeSheafHomGlobalEquiv (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ F) ≃+ (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).obj F :=
  ((constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).homAddEquiv
    (AddCommGrpCat.of (ULift ℤ)) F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

theorem nativeSheafHomGlobalEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ F) (g : F ⟶ G) :
    nativeSheafHomGlobalEquiv G (f ≫ g) =
      (SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf.globalSectionsFunctor X).map g (nativeSheafHomGlobalEquiv F f) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    ((constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).homEquiv _ _ (f ≫ g)) = _
  rw [(constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}).homEquiv_naturality_right]
  rfl

theorem nativeSheafHomGlobalEquiv_top (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (f : Chern.Sheaf.ResolutionClasses.sheafCohomologySource X ⟶ F) :
    (CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{0} isTerminalTop).hom.app F (nativeSheafHomGlobalEquiv F f) =
        Chern.Sheaf.ResolutionClasses.sheafHomGlobalEquiv F f := by
  let A := constantSheafΓAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0}
  let B := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop
  have he := homEquiv_comp_rightAdjointUniq A B f
  have hv := ConcreteCategory.congr_hom he (ULift.up (1 : ℤ))
  change (A.rightAdjointUniq B).hom.app F
    ((A.homEquiv (AddCommGrpCat.of (ULift ℤ)) F f) (ULift.up (1 : ℤ))) =
      (B.homEquiv (AddCommGrpCat.of (ULift ℤ)) F f) (ULift.up (1 : ℤ)) at hv
  exact hv

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCoordinates
