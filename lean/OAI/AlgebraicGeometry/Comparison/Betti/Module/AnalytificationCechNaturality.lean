import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechMap
import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationUnitNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

/-! # Analytification Cech Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechNaturality

noncomputable section

/-! The original native Čech analytification comparison is natural in algebraic modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    {ι : Type} (U : ι → X.left.Opens)

theorem moduleAnalytificationCechMap_naturality
    {M N : SheafOfModules.{0} X.left.ringCatSheaf} (g : M ⟶ N) :
    AnalytificationCechMap.moduleAnalytificationCechMap X M U ≫
        (cechComplexFunctor (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))).map
          (AnalytificationUnitNaturality.analytifiedModuleAdditivePresheafMap X g) =
      (cechComplexFunctor U).map (AnalytificationUnitNaturality.moduleAdditivePresheafMap X g) ≫
        AnalytificationCechMap.moduleAnalytificationCechMap X N U := by
  let C := cechComplexFunctor (A := AddCommGrpCat) U
  let A := cechComplexFunctor (A := AddCommGrpCat) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))
  let p := AnalytificationUnitNaturality.moduleAdditivePresheafMap X g
  let q := AnalytificationUnitNaturality.analytifiedModuleAdditivePresheafMap X g
  let r := Functor.whiskerLeft (Opens.map (Analytification.Base.analytificationMap X)).op q
  let uM := AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X M
  let uN := AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X N
  let eM := (AdditiveCechImage.additiveCechDirectImageIso (Analytification.Base.analytificationMap X) U
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M).val.presheaf).hom
  let eN := (AdditiveCechImage.additiveCechDirectImageIso (Analytification.Base.analytificationMap X) U
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj N).val.presheaf).hom
  have hn : C.map r ≫ eN = eM ≫ A.map q :=
    AdditiveCechImage.additiveCechDirectImageIso_naturality (Analytification.Base.analytificationMap X) U q
  have hu : uM ≫ r = p ≫ uN := AnalytificationUnitNaturality.moduleAnalytificationAdditiveUnit_naturality X g
  exact (Category.assoc (C.map uM) eM (A.map q)).trans
    ((congrArg (C.map uM ≫ ·) hn.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ eN) ((C.map_comp uM r).symm.trans
          ((congrArg C.map hu).trans (C.map_comp p uN)))).trans (Category.assoc _ _ _))))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechNaturality
