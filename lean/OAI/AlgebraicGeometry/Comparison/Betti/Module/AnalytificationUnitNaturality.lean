import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationAdditiveUnit

/-! # Analytification Unit Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationUnitNaturality

noncomputable section

/-! The actual additive analytification unit is natural in the algebraic module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def moduleAdditivePresheafMap {M N : SheafOfModules.{0} X.left.ringCatSheaf} (g : M ⟶ N) :
    M.val.presheaf ⟶ N.val.presheaf :=
  ((SheafOfModules.toSheaf X.left.ringCatSheaf).map g).hom

def analytifiedModuleAdditivePresheafMap {M N : SheafOfModules.{0} X.left.ringCatSheaf} (g : M ⟶ N) :
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf ⟶
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj N).val.presheaf :=
  ((SheafOfModules.toSheaf (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)).map
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).map g)).hom

theorem moduleAnalytificationAdditiveUnit_naturality
    {M N : SheafOfModules.{0} X.left.ringCatSheaf} (g : M ⟶ N) :
    AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M ≫
        Functor.whiskerLeft (Opens.map (Analytification.Base.analytificationMap X)).op
          (analytifiedModuleAdditivePresheafMap X g) =
      moduleAdditivePresheafMap X g ≫ AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X N := by
  let A := SheafOfModules.toSheaf X.left.ringCatSheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.left) AddCommGrpCat
  have h := (Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.naturality g
  exact (A.map_comp _ _).symm.trans ((congrArg A.map h.symm).trans (A.map_comp _ _))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationUnitNaturality
