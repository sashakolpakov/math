import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProductPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.IntegralCycleDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductComponentFibers

/-! # Product Cycle Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProductCycleDescent

noncomputable section

/-! Exterior product with the source fundamental cycle preserves rational
equivalence in every codimension, for disconnected smooth projective factors. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor

theorem preserves_relations {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (P : ProperCycleLinearity.ProductPresentation X Y) (m n p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap] :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y p ≤
      (CycleClass.Thom.IntersectionGeometry.rationalEquivalences P.space p).comap (DegreeCast.ExteriorCycleLinear.secondPullbackMap P p) := by
  let : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
    ProductDimension.relativeDimension P m n
  let : Smooth P.snd.left := ProductDivisorPullback.snd_smooth P
  intro a ha
  change DegreeCast.ExteriorCycleLinear.secondPullbackMap P p a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences P.space p
  rw [DegreeCast.ExteriorCycleLinear.secondPullbackMap_apply,
    ProductPullback.secondPullback_eq_flatMap P m n p]
  apply (Component.Principal.CycleDecomposition.relations_iff P.space (m + n) p _).mpr
  intro C
  let V := (P.space.componentVariety C).presentation
  let g : V.toOver ⟶ Y.toOver := Component.Image.inclusion P.space C ≫ P.snd
  let D := Integral.ComponentFactor.component (Z := V.carrier) Y g.left
  let : SmoothOfRelativeDimension (m + n) V.structureMap :=
    Component.Image.component_relativeDimension P.space (m + n) C
  let : SmoothOfRelativeDimension n (Y.componentVariety D).structureMap :=
    Component.Image.component_relativeDimension Y n D
  let : Smooth g.left := by
    change Smooth (P.space.componentInclusion C ≫ P.snd.left)
    infer_instance
  let : GeometricallyIntegral (Integral.ComponentFactor.overMap Y g).left :=
    ProductComponentFibers.snd_geometricallyIntegral P C
  rw [ProjectionFormula.Smooth.CycleComponents.restrict_flatMap P.snd (m + n) n p C,
    ProjectionFormula.Smooth.CycleComponents.flatMap_factor g (m + n) n p]
  exact ProjectionFormula.Smooth.IntegralCycleDescent.preserves_relations (Integral.ComponentFactor.overMap Y g) (m + n) n p
    (Component.Principal.restrict_preserves_relations Y D p ha)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProductCycleDescent
