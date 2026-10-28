import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCech.AcyclicCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.CohomologyNaturality

/-! # Acyclic Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AcyclicCover

noncomputable section

/-! The ordered complex of one common acyclic cover gives a natural coefficient cohomology comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (c : R →+* Γ(X, ⊤)) {ι : Type u} [LinearOrder ι]
variable (U : ι → X.Opens) (hU : iSup U = ⊤)

def orderedCechAcyclicCoverModuleIso (M : X.Modules)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).homology (n + 1) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj M :=
  (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U (n + 1)).symm ≪≫
    CoefficientCech.AcyclicCover.coefficientCechAcyclicCoverModuleIso c U hU M hM n

theorem orderedCechAcyclicCoverModuleIso_naturality
    {M N : X.Modules} (f : M ⟶ N)
    (hM : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (hN : Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) (n : ℕ) :
    HomologicalComplex.homologyMap ((Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map f) (n + 1) ≫
        (orderedCechAcyclicCoverModuleIso c U hU N hN n).hom =
      (orderedCechAcyclicCoverModuleIso c U hU M hM n).hom ≫
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map f := by
  let α : Intrinsic.CoefficientCechComplex.coefficientCechComplex c M U ⟶ Intrinsic.CoefficientCechComplex.coefficientCechComplex c N U :=
    (Intrinsic.CoefficientCechComplex.coefficientCechComplexFunctor c U).map f
  let β : Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N U :=
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map f
  have h₁ : HomologicalComplex.homologyMap β (n + 1) ≫
      (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c N U (n + 1)).inv =
      (Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U (n + 1)).inv ≫ HomologicalComplex.homologyMap α (n + 1) :=
    CohomologyNaturality.coefficientCechOrderedHomologyIso_inv_naturality c f U (n + 1)
  have h₂ : HomologicalComplex.homologyMap α (n + 1) ≫
      (CoefficientCech.AcyclicCover.coefficientCechAcyclicCoverModuleIso c U hU N hN n).hom =
      (CoefficientCech.AcyclicCover.coefficientCechAcyclicCoverModuleIso c U hU M hM n).hom ≫
        (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map f :=
    CoefficientCech.AcyclicCover.coefficientCechAcyclicCoverModuleIso_naturality c U hU f hM hN n
  change HomologicalComplex.homologyMap β (n + 1) ≫
      ((Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c N U (n + 1)).inv ≫
        (CoefficientCech.AcyclicCover.coefficientCechAcyclicCoverModuleIso c U hU N hN n).hom) =
    ((Ordered.CoefficientCechHomotopyEquivalence.coefficientCechOrderedHomologyIso c M U (n + 1)).inv ≫
      (CoefficientCech.AcyclicCover.coefficientCechAcyclicCoverModuleIso c U hU M hM n).hom) ≫ _
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AcyclicCover
