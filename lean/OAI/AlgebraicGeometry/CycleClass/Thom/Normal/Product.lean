import OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductCoefficientOne
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExteriorCupNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairProductSupport

/-! # Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product

noncomputable section

/-! Products of the actual normalized relative normal classes, under the
actual product of the two normal-coordinate maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductCoefficientOne.Constructions

namespace Constructions.Class

theorem relativeCohomologyMap_degreeCast {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) {n m : ℕ} (h : n = m)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B n) :
    eqToHom (congrArg (fun j => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A j) h)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf m
      (eqToHom (congrArg (fun j => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B j) h) a) := by
  subst h
  rfl

theorem relativeCohomologyMap_targetCast {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B C : Set Y} (h : B = C) (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A C)
    (n : ℕ) (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B n) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf' n
      (eqToHom (congrArg (fun U => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y U n) h) a) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n a := by
  subst h
  rfl

variable {X Y : TopCat.{0}} {A : Set X} {B : Set Y} {p q : ℕ}
variable (f : X ⟶ TopCat.of (Fin p → ℂ)) (g : Y ⟶ TopCat.of (Fin q → ℂ))
variable (hf : Set.MapsTo f A ({0}ᶜ)) (hg : Set.MapsTo g B ({0}ᶜ))

include hf hg in
theorem productNormalMapsTo :
    Set.MapsTo (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (TopCat.of (Fin p → ℂ), TopCat.of (Fin q → ℂ))))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) ({0}ᶜ : Set ((Fin p → ℂ) × (Fin q → ℂ))) := by
  have h := HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg
  rw [HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin p → ℂ)) (TopCat.of (Fin q → ℂ)) 0 0] at h
  exact h

theorem relativeExteriorCup_normalized_pullbacks (hA : IsOpen A) (hB : IsOpen B)
    (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ)) :
    eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n) (Nat.mul_add 2 p q).symm)
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB (2 * p) (2 * q)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p))
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q))) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (TopCat.of (Fin p → ℂ), TopCat.of (Fin q → ℂ))))
      (productNormalMapsTo f g hf hg) (2 * (p + q)) (Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass e) := by
  have hn := HodgeConjecture.DegreeTwo.ExteriorCupNaturality.Constructions.relativeExteriorCup_naturality f g hf hg hA hB
    isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl (2 * p) (2 * q)
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)
  have hm := relativeCohomologyMap_targetCast
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (TopCat.of (Fin p → ℂ), TopCat.of (Fin q → ℂ))))
    (HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin p → ℂ)) (TopCat.of (Fin q → ℂ)) 0 0)
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo f g hf hg) (productNormalMapsTo f g hf hg) (2 * p + 2 * q)
    (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of (Fin p → ℂ)) (TopCat.of (Fin q → ℂ)) ({0}ᶜ) ({0}ᶜ)
      isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl (2 * p) (2 * q)
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q))
  rw [hn, ← hm]
  have hd := relativeCohomologyMap_degreeCast
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (TopCat.of (Fin p → ℂ), TopCat.of (Fin q → ℂ))))
    (productNormalMapsTo f g hf hg) (Nat.mul_add 2 p q).symm (HodgeConjecture.DegreeTwo.LocalProductCup.Constructions.localProductCupClass p q)
  exact hd.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶ (TopCat.of (Fin p → ℂ), TopCat.of (Fin q → ℂ))))
      (productNormalMapsTo f g hf hg) (2 * (p + q)))
    (Local.ProductCoefficientOne.Constructions.localProductCupTop_eq_coordinate p q e))

/-- Concatenate the two actual normal-coordinate maps using complex-linear
coordinates on the sum of the two normal spaces. -/
def combinedNormalMap
    (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ)) :
    TopCat.of (X × Y) ⟶ TopCat.of (Fin (p + q) → ℂ) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶
    (TopCat.of (Fin p → ℂ), TopCat.of (Fin q → ℂ))) ≫ (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom

include hf hg in
theorem combinedNormalMapsTo
    (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ)) :
    Set.MapsTo (combinedNormalMap f g e) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) ({0}ᶜ) :=
  (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e).comp (productNormalMapsTo f g hf hg)

theorem relativeExteriorCup_combinedNormalPullback (hA : IsOpen A) (hB : IsOpen B)
    (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ)) :
    eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (X × Y)) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X Y A B) n) (Nat.mul_add 2 p q).symm)
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup X Y A B hA hB (2 * p) (2 * q)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p))
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q))) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (combinedNormalMap f g e)
      (combinedNormalMapsTo f g hf hg e) (2 * (p + q))
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q)) := by
  rw [relativeExteriorCup_normalized_pullbacks f g hf hg hA hB e]
  unfold Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass
  rw [Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso_hom]
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, g) : (X, Y) ⟶
        (TopCat.of (Fin p → ℂ), TopCat.of (Fin q → ℂ))))
      (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom (productNormalMapsTo f g hf hg)
      (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e) (2 * (p + q)))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q))

variable {M N M' N' E F : Type} [TopologicalSpace N] [TopologicalSpace N']
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {u : M → N} {v : M' → N'} {x : M} {y : M'}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin q → ℂ) v y)

/-- The genuine normal-pair classes have the normalized product class under
the actual product of their normal-coordinate maps. -/
theorem normalPairClass_exteriorProduct
    (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ)) :
    eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (P.neighborhood × Q.neighborhood))
      (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
        P.relativeComplement Q.relativeComplement) n) (Nat.mul_add 2 p q).symm)
      (HodgeConjecture.DegreeTwo.ExteriorCupSmallEvaluation.Constructions.relativeExteriorCup (TopCat.of P.neighborhood) (TopCat.of Q.neighborhood)
        P.relativeComplement Q.relativeComplement
        (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q)
        (2 * p) (2 * q) P.rationalClassFin Q.rationalClassFin) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((P.normalCoordinate, Q.normalCoordinate) :
        (TopCat.of P.neighborhood, TopCat.of Q.neighborhood) ⟶
          (TopCat.of (Fin p → ℂ), TopCat.of (Fin q → ℂ))))
      (productNormalMapsTo P.normalCoordinate Q.normalCoordinate
        P.normalCoordinate_mapsTo Q.normalCoordinate_mapsTo)
      (2 * (p + q)) (Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass e) := by
  rw [P.rationalClassFin_eq_normalPullback, Q.rationalClassFin_eq_normalPullback]
  exact relativeExteriorCup_normalized_pullbacks P.normalCoordinate Q.normalCoordinate
    P.normalCoordinate_mapsTo Q.normalCoordinate_mapsTo
    (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen Q) e

end Constructions.Class

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product
