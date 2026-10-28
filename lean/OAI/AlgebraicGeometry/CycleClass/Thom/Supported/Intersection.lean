import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.Product

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection.Constructions.Class

noncomputable section

/-! The actual cup of two geometric cycle classes has a canonical lift
supported on the intersection of their analytic supports. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AbsoluteProductMaps.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Degree.Constructions.Class
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)

def supportedIntersectionClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of V.analyticSpace) (Set.range A.analyticInclusion ∩ Set.range B.analyticInclusion)ᶜ
    (2 * (p + q)) :=
  ImageIntersectionCup.Constructions.imageIntersectionCup A.analyticInclusion B.analyticInclusion
    A.isClosedEmbedding_analyticInclusion.isClosed_range.isOpen_compl
    B.isClosedEmbedding_analyticInclusion.isClosed_range.isOpen_compl p q
    A.rationalSupportedCycleClass B.rationalSupportedCycleClass

theorem supportedIntersectionClass_forget :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range A.analyticInclusion ∩ Set.range B.analyticInclusion)ᶜ (2 * (p + q))
      (supportedIntersectionClass A B) =
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace))
      (Nat.mul_add 2 p q).symm)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (TopCat.of V.analyticSpace) (2 * p) (2 * q)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
          (Set.range A.analyticInclusion)ᶜ (2 * p) A.rationalSupportedCycleClass)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
          (Set.range B.analyticInclusion)ᶜ (2 * q) B.rationalSupportedCycleClass)) :=
  ImageIntersectionCup.Constructions.imageIntersectionCup_forget A.analyticInclusion B.analyticInclusion _ _ p q _ _

theorem supportedIntersectionClass_geometricCup :
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (two_mul (p + q)))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range A.analyticInclusion ∩ Set.range B.analyticInclusion)ᶜ (2 * (p + q))
        (supportedIntersectionClass A B)) =
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace V.toOver) (p + p) (q + q)
        A.geometricCycleClass B.geometricCycleClass) := by
  rw [← GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric A, ← GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric B,
    Cycle.Degree.Constructions.Class.rationalCycleClass_as_cast A, Cycle.Degree.Constructions.Class.rationalCycleClass_as_cast B,
    supportedIntersectionClass_forget,
    AbsoluteProductMaps.Constructions.absoluteDegreeCast_apply (TopCat.of V.analyticSpace) (Nat.mul_add 2 p q).symm]
  have h := Cycle.Degree.Constructions.Class.projectionCup_degreeTransport (𝟙 (Betti.Scheme.schemePointSpace V.toOver))
    (𝟙 (Betti.Scheme.schemePointSpace V.toOver)) (two_mul p) (two_mul q) (Nat.mul_add 2 p q).symm
    (add_add_add_comm p p q q) (two_mul (p + q))
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range A.analyticInclusion)ᶜ (2 * p) A.rationalSupportedCycleClass)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range B.analyticInclusion)ᶜ (2 * q) B.rationalSupportedCycleClass)
  simpa only [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, ConcreteCategory.id_apply,
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomology, Betti.Scheme.schemeBetti, Betti.Scheme.schemePointSpace,
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection.Constructions.Class
