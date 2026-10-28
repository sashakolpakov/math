import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup

/-! # Intersection Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup

noncomputable section

/-! The actual diagonal cup of normal-coordinate pullbacks is the
normalized class of the concatenated complex normal coordinates. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Even

theorem diagonalComplementMapsTo (X : TopCat.{0}) (A B : Set X) :
    Set.MapsTo (ImageIntersectionCup.Constructions.diagonalMap X) (A ∪ B) (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement X X A B) :=
  fun _ hx => hx

def evenIntersectionCup (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (p q : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A (2 * p))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X B (2 * q)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X (A ∪ B) (2 * (p + q)) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ImageIntersectionCup.Constructions.diagonalMap X)
    (diagonalComplementMapsTo X A B) (2 * (p + q)) (ExteriorImageCup.Constructions.Even.evenExteriorCup X X A B hA hB p q a b)

variable {X : TopCat.{0}} {A B : Set X} {p q : ℕ}
  (f : X ⟶ TopCat.of (Fin p → ℂ)) (g : X ⟶ TopCat.of (Fin q → ℂ))
  (hf : Set.MapsTo f A ({0}ᶜ)) (hg : Set.MapsTo g B ({0}ᶜ))
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

def internalNormalMap : X ⟶ TopCat.of (Fin (p + q) → ℂ) :=
  ImageIntersectionCup.Constructions.diagonalMap X ≫ Product.Constructions.Class.combinedNormalMap f g e

theorem internalNormalMap_apply (x : X) : internalNormalMap f g e x = e (f x, g x) := rfl

include hf hg in
theorem internalNormalMapsTo : Set.MapsTo (internalNormalMap f g e) (A ∪ B) ({0}ᶜ) :=
  (Product.Constructions.Class.combinedNormalMapsTo f g hf hg e).comp (diagonalComplementMapsTo X A B)

theorem evenIntersectionCup_normalized_pullbacks (hA : IsOpen A) (hB : IsOpen B) :
    evenIntersectionCup X A B hA hB p q
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (internalNormalMap f g e)
      (internalNormalMapsTo f g hf hg e) (2 * (p + q)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q)) := by
  have h := Product.Constructions.Class.relativeExteriorCup_combinedNormalPullback f g hf hg hA hB e
  have hp := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ImageIntersectionCup.Constructions.diagonalMap X)
    (diagonalComplementMapsTo X A B) (2 * (p + q))) h
  apply hp.trans
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (ImageIntersectionCup.Constructions.diagonalMap X)
      (Product.Constructions.Class.combinedNormalMap f g e) (diagonalComplementMapsTo X A B)
      (Product.Constructions.Class.combinedNormalMapsTo f g hf hg e) (2 * (p + q))) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q))

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup
