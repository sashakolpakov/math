import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberCycles
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralPrincipalRelations

/-! # Integral Cycle Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.IntegralCycleDescent

noncomputable section

/-! Smooth inverse image with geometrically integral fibers respects ThomClass's
principal-divisor relations in every codimension, on arbitrary integral
supports of the smooth projective target. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralPrincipalRelations.BundleCycles OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  [Smooth (show X.carrier ⟶ Y.carrier from f.left)]
  [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap]

include m n

theorem principal (p : ℕ) (W : IrreducibleCloseds Y.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    Cycle.flatMap f p (Principal.ClosedSectionCycle.principalCycle Y p W g) =
      Principal.ClosedSectionCycle.principalCycle X p
        (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) W)
        (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupportFunction (show X.carrier ⟶ Y.carrier from f.left) W g) := by
  change Cycle.flatMap f p (CyclePushforward.degreeComponent Y p (Divisors.LineBundles.Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g)) = _
  rw [Integral.FiberCycles.flatMap_degreeComponent f m n,
    Divisors.LineBundles.Smooth.IntegralPrincipalRelations.BundleCycles.smoothIntegralCycleExtension_principal (show X.carrier ⟶ Y.carrier from f.left) W g hg]
  rfl

theorem preserves_relations (p : ℕ) :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y p ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).comap (Cycle.flatMap f p) := by
  apply Submodule.span_le.mpr
  intro d hd
  obtain ⟨W, hW, g, hg, rfl⟩ := (Principal.ClosedSectionCycle.isPrincipalDivisor_iff Y p d).mp hd
  change Cycle.flatMap f p (Principal.ClosedSectionCycle.principalCycle Y p W g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p
  rw [principal f m n p W g hg]
  apply Submodule.subset_span
  apply Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor
  · rw [Integral.FiberCycles.codimension f m n W]
    exact hW
  · exact Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupportFunction_ne_zero
      (show X.carrier ⟶ Y.carrier from f.left) W g hg

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.IntegralCycleDescent
