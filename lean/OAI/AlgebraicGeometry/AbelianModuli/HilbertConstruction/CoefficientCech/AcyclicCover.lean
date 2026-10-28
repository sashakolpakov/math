import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.HomologyScalars
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CohomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyFunctor

/-! # Acyclic Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AcyclicCover

noncomputable section

/-! A fixed acyclic cover computes genuine coefficient cohomology naturally, without requiring its opens to be affine. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (c : R →+* Γ(X, ⊤)) {ι : Type u} (U : ι → X.Opens)
variable (hU : iSup U = ⊤)

def coefficientCechAcyclicCoverAddIso (M : X.Modules)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    (Module.ProductForget.moduleForget R).obj ((Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).homology (n + 1)) ≅
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (n + 1)).obj M :=
  HomologyForget.coefficientCechComplexHomologyForgetIso c M U (n + 1) ≪≫
    IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) hU hM n

theorem coefficientCechAcyclicCoverAddIso_naturality
    {M N : X.Modules} (f : M ⟶ N)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (hN : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) (n : ℕ) :
    (Module.ProductForget.moduleForget R).map (HomologicalComplex.homologyMap
        ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map f) (n + 1)) ≫
      (coefficientCechAcyclicCoverAddIso c U hU N hN n).hom =
    (coefficientCechAcyclicCoverAddIso c U hU M hM n).hom ≫
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (n + 1)).map f := by
  apply ConcreteCategory.hom_ext
  intro x
  have h₁ := ConcreteCategory.congr_hom
    (HomologyNaturality.coefficientCechComplexHomologyForgetIso_naturality c f U (n + 1)) x
  have h₂ := ConcreteCategory.congr_hom
    (Cech.CohomologyNaturality.IntrinsicCech.cechHomologySuccIsoOfAcyclicIntersections_naturality U
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f) hU hM hN n)
      ((HomologyForget.coefficientCechComplexHomologyForgetIso c M U (n + 1)).hom x)
  exact (congrArg
    (IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) hU hN n).hom h₁).trans h₂

def coefficientCechAcyclicCoverModuleIso (M : X.Modules)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    (Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U).homology (n + 1) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj M := by
  refine ModuleCat.isoMk (coefficientCechAcyclicCoverAddIso c U hU M hM n) ?_
  intro r
  apply ConcreteCategory.hom_ext
  intro x
  have h := coefficientCechAcyclicCoverAddIso_naturality c U hU
    (Global.ModuleScalars.globalModuleScalar M (c r)) hM hM n
  have hm := HomologyScalars.coefficientCech_globalScalar_homologyMap c M U r (n + 1)
  have hv := ConcreteCategory.congr_hom h x
  have hx := ConcreteCategory.congr_hom hm x
  exact ((congrArg (coefficientCechAcyclicCoverAddIso c U hU M hM n).hom hx).symm.trans hv).symm

theorem coefficientCechAcyclicCoverModuleIso_naturality
    {M N : X.Modules} (f : M ⟶ N)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (hN : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) (n : ℕ) :
    HomologicalComplex.homologyMap ((Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map f) (n + 1) ≫
        (coefficientCechAcyclicCoverModuleIso c U hU N hN n).hom =
      (coefficientCechAcyclicCoverModuleIso c U hU M hM n).hom ≫
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map f := by
  apply (forget₂ (ModuleCat R) AddCommGrpCat).map_injective
  exact coefficientCechAcyclicCoverAddIso_naturality c U hU f hM hN n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AcyclicCover
