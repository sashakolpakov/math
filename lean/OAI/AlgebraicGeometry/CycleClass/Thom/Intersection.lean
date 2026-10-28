import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.NormalRestriction

/-! # Intersection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Intersection.Constructions

/-! Genuine supported Thom classes multiply under transverse
intersection of closed complex immersions. The only compatibility
hypothesis concerns the actual normal differential. -/

open _root_.CategoryTheory
open scoped ContDiff _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions.ClosedComplexImmersion OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions
  ImageIntersectionCup.Constructions NormalRestriction.Constructions Normal.Product.Constructions.Class Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ}
  (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p) (W : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V q)
  (S : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V (p + q))
  (hw : Set.range S.regularComplementInclusion =
    Set.range Z.regularComplementInclusion ∩ Set.range W.regularComplementInclusion)

theorem regularThomClass_intersection (ht : Immersion.IntersectionCoordinates.Constructions.NormalTransverse Z W) :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      V.analyticSpace A (2 * (p + q))) (congrArg Set.compl hw.symm))
      (ImageIntersectionCup.Constructions.imageIntersectionCup Z.regularComplementInclusion W.regularComplementInclusion
        Z.closed.isClosed_range.isOpen_compl W.closed.isClosed_range.isOpen_compl p q
        Z.regularThomClass W.regularThomClass) = S.regularThomClass := by
  classical
  choose x y R hR hRd hRn using Immersion.IntersectionCoordinates.Constructions.exists_intersection_normalPair Z W S hw ht
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique S.regularComplementInclusion S.holomorphic
    S.differential_injective S.closed (p + q) S.regularComplement_complexImmersionCodimension R hRd
  intro z
  have hc := Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (R z).neighborhood)
    (congrArg Set.compl hw.symm) (NormalRestriction.Constructions.intersectionNeighborhood_mapsTo (R z) hw)
    (fun _ ha => ha) (2 * (p + q))
    (ImageIntersectionCup.Constructions.imageIntersectionCup Z.regularComplementInclusion W.regularComplementInclusion
      Z.closed.isClosed_range.isOpen_compl W.closed.isClosed_range.isOpen_compl p q
      Z.regularThomClass W.regularThomClass)
  apply hc.trans
  apply NormalRestriction.Constructions.imageIntersectionCup_normal_restriction
    (Z.regularFixedNormalPair (x z)) (W.regularFixedNormalPair (y z)) (R z)
    hw (hR z) (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates p q) (hRn z)
  · exact (Z.regularThomClass_restrict_normalPair (x z) (Z.regularFixedNormalPair (x z))
      (Z.regularFixedNormalPair_ambientChart_mdifferentiable (x z))).trans
      (Z.regularFixedNormalPair (x z)).rationalClassFin_eq_normalPullback.symm
  · exact (W.regularThomClass_restrict_normalPair (y z) (W.regularFixedNormalPair (y z))
      (W.regularFixedNormalPair_ambientChart_mdifferentiable (y z))).trans
      (W.regularFixedNormalPair (y z)).rationalClassFin_eq_normalPullback.symm

end AlgebraicGeometry.CycleClass.Thom.Intersection.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Intersection.Constructions.ThomAbsolute

/-! The transverse supported Thom formula gives the ordinary cup formula
after applying the actual map that forgets support. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions.ClosedComplexImmersion OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions
  ImageIntersectionCup.Constructions Constructions ExteriorCupForget.Constructions

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ}
  (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p) (W : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V q)
  (S : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V (p + q))
  (hw : Set.range S.regularComplementInclusion =
    Set.range Z.regularComplementInclusion ∩ Set.range W.regularComplementInclusion)

include hw in
theorem regularThomClass_absolute_intersection (ht : Immersion.IntersectionCoordinates.Constructions.NormalTransverse Z W) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) V.analyticSpace
      (Set.range S.regularComplementInclusion)ᶜ (2 * (p + q)) S.regularThomClass =
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) V.analyticSpace)
      (Nat.mul_add 2 p q).symm)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) V.analyticSpace (2 * p) (2 * q)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) V.analyticSpace
          (Set.range Z.regularComplementInclusion)ᶜ (2 * p) Z.regularThomClass)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) V.analyticSpace
          (Set.range W.regularComplementInclusion)ᶜ (2 * q) W.regularThomClass)) := by
  rw [← regularThomClass_intersection Z W S hw ht]
  exact (ExteriorCupForget.Constructions.relativeInclusion_supportCast V.analyticSpace (congrArg Set.compl hw.symm)
    (2 * (p + q)) _).trans
    (ImageIntersectionCup.Constructions.imageIntersectionCup_forget Z.regularComplementInclusion W.regularComplementInclusion
      Z.closed.isClosed_range.isOpen_compl W.closed.isClosed_range.isOpen_compl p q _ _)

end AlgebraicGeometry.CycleClass.Thom.Intersection.Constructions.ThomAbsolute

end

end OAI
