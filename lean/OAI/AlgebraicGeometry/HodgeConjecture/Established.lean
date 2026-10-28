import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionOne
import OAI.AlgebraicGeometry.HodgeConjecture.Intersections
import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionQ
import OAI.Algebra.FieldTheory.ScalarDescentTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Algebraicity
import OAI.AlgebraicGeometry.Cycles.Functoriality.DimensionPreserving
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Core
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Chow

/-! # Established -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Established.CM.SurfaceConstruction.Intrinsic

noncomputable section

/-! Proved instances of six full SurfaceConstruction prerequisites. The existing conditional
proof and its seven input meanings remain unchanged. The ThomClass transport bridge
is the proved full-proposition equivalence used by the canonical validator.
No claim about the remaining non-elementary surface existence is made here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The complete scalar-trace input at the universe used by SurfaceConstruction. -/
theorem scalarTraceDescent (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E :=
  Algebra.FieldTheory.ScalarDescentTrace.Core.scalar_trace_descent E

/-- The full proved degree-two theorem, retaining the historical ChernClass binder. -/
theorem degreeTwoAlgebraicityInput : SurfaceConstructionOne.CM.DegreeTwoAlgebraicityInput := by
  intro _ X a ha
  exact DegreeTwo.Algebraicity.CM.degree_two_algebraicity_unconditional X a ha

/-- ChernClass is proved independently; it is not inferred from the SurfaceConstruction target. -/
theorem lefschetzOneOneInput : SurfaceConstructionOne.CM.LefschetzOneOneInput :=
  DegreeTwo.Established.Constructions.e09Input

theorem degreeTwoAlgebraicity : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity :=
  SurfaceConstructionOne.CM.degreeTwoAlgebraicity_of_inputs degreeTwoAlgebraicityInput lefschetzOneOneInput

theorem properCycleClassCompatibility : SurfaceConstructionQ.CM.ProperCycleClassCompatibility :=
  Cycles.Functoriality.DimensionPreserving.Construction.cycleClass_proper_pushforward

theorem presentationDegreeCast_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {m n : ℕ}
    (h : m = n) (a : X.rationalCohomology m) :
    Intersections.CM.SurfaceConstruction.presentationDegreeCast X h a =
      cast (congrArg (fun k => (X.rationalCohomology k : Type)) h) a := by
  subst n
  rfl

/-- The full ThomClass proposition, with the exact original cast. -/
def CanonicalIntersectionCompatibility : Prop :=
  ∀ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)),
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c →
      X.geometricCycleClassMap (p + q) c =
        cast (congrArg (fun n => (X.rationalCohomology n : Type))
          (add_add_add_comm p p q q))
          (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver)
            (p + p) (q + q) (X.geometricCycleClassMap p a) (X.geometricCycleClassMap q b))

theorem full_ThomClass_equivalence :
    Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility ↔ CanonicalIntersectionCompatibility := by
  unfold Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility CanonicalIntersectionCompatibility Intersections.CM.SurfaceConstruction.evenCup
  simp only [LinearMap.compr₂_apply, presentationDegreeCast_apply]

theorem intersectionCycleClassCompatibility : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility :=
  full_ThomClass_equivalence.mpr CycleClass.Thom.Intersection.Core.cycle_class_intersection

/-- Full Chow totality, graph equalities, and projection formula from the
proved geometric operations; no historical statement proof is imported. -/
theorem chowProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula := by
  intro X Y f _ P m n _ _ p q s hdeg hdegCup
  refine ⟨IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection.chowMap X m p q,
    IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection.chowMap Y n p s,
    IntersectionTheory.ProjectionFormula.General.ChowPullback.pull P f m n p,
    IntersectionTheory.ProjectionFormula.ChowPushforwardMap.map f m n q s hdeg,
    IntersectionTheory.ProjectionFormula.ChowPushforwardMap.map f m n (p + q) (p + s) hdegCup,
    IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection.chowIntersection_eq_singleton X m p q,
    IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection.chowIntersection_eq_singleton Y n p s,
    IntersectionTheory.ProjectionFormula.General.ChowPullback.chowPullback_eq_singleton P f m n p,
    IntersectionTheory.ProjectionFormula.ChowPushforwardMap.graph f m n q s hdeg,
    IntersectionTheory.ProjectionFormula.ChowPushforwardMap.graph f m n (p + q) (p + s) hdegCup, ?_⟩
  exact IntersectionTheory.ProjectionFormula.General.Chow.Projection.chow P f m n p q s hdeg

end

end OAI.AlgebraicGeometry.HodgeConjecture.Established.CM.SurfaceConstruction.Intrinsic
