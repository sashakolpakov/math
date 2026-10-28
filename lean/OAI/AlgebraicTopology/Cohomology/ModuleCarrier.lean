import OAI.Algebra.Modules.ScalarModuleUnderlyingGroup
import OAI.AlgebraicGeometry.Sheaves.ModuleSheafRestrictionCarrier
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalCohomologyExcision

/-! # Module Carrier -/

namespace OAI.AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coefficientCohomologyUnderlying {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M) =
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := by
  dsimp only [AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor, Functor.comp_obj,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.globalCohomologyFunctor, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.globalCohomologyModuleObj]
  exact (Algebra.Modules.ScalarModuleUnderlyingGroup.scalarModuleUnderlyingGroup c
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X n).obj M)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyScalars.ZariskiCohomology.globalSectionsCohomologyAction M n)).trans
      (Algebra.Modules.ScalarModuleUnderlyingGroup.addGroupOfCarrier _).symm

theorem coefficientOpenCohomologyUnderlying {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (U.ι.appTop.hom.comp c) n).obj
        (M.restrict U.ι)) =
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology U) n).obj
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))) := by
  rw [coefficientCohomologyUnderlying, AlgebraicGeometry.Sheaves.ModuleSheafRestrictionCarrier.HilbertConstruction.underlyingModuleSheafRestriction]
private def rebundleAdditiveGroupHom {A B : AddCommGrpCat.{u}} (f : A ⟶ B) :
    AddCommGrpCat.of A ⟶ AddCommGrpCat.of B := AddCommGrpCat.ofHom f.hom

def additiveSheafCohomologyMap {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).obj F) ⟶
    AddCommGrpCat.of ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).obj G) :=
  rebundleAdditiveGroupHom ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).map f)

theorem coefficientCohomologyUnderlying_smul {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) (r : R) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj M).smul r ≫
        eqToHom (coefficientCohomologyUnderlying c M n) =
      eqToHom (coefficientCohomologyUnderlying c M n) ≫
        additiveSheafCohomologyMap
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars.globalModuleScalar M (c r))) n := by
  exact Algebra.Modules.ScalarModuleUnderlyingGroup.scalarModuleUnderlyingGroup_smul c
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X n).obj M)
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyScalars.ZariskiCohomology.globalSectionsCohomologyAction M n) r

theorem coefficientOpenCohomologyUnderlying_smul {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (n : ℕ) (r : R) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (U.ι.appTop.hom.comp c) n).obj
        (M.restrict U.ι)).smul r ≫ eqToHom (coefficientOpenCohomologyUnderlying c M U n) =
      eqToHom (coefficientOpenCohomologyUnderlying c M U n) ≫
        additiveSheafCohomologyMap
          ((SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map
            (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars.globalModuleScalar (M.restrict U.ι) (U.ι.appTop (c r)))) n := by
  exact coefficientCohomologyUnderlying_smul (U.ι.appTop.hom.comp c) (M.restrict U.ι) n r

theorem moduleOpenCohomologyType {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (n : ℕ) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology.H (M.restrict U.ι) n =
      CategoryTheory.Sheaf.H
        ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).obj
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) n := by
  rfl

theorem moduleOpenCohomologySubsingleton {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (n : ℕ) (h : Subsingleton (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology.H (M.restrict U.ι) n)) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.TopologicalSheafRestriction.IntrinsicCech.restrict AddCommGrpCat U.isOpenEmbedding).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) n) :=
  Eq.mp (congrArg (fun T : Type u => Subsingleton T) (moduleOpenCohomologyType M U n)) h

end

end OAI.AlgebraicTopology.Cohomology.ModuleCarrier.HilbertConstruction
