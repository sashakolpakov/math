import OAI.AlgebraicGeometry.CycleClass.Thom.Open.Principal
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary

/-! # Open Principal Coefficients -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipalCoefficients.Constructions

noncomputable section

/-! On every fully retained normalization fiber, the actual open-source
principal divisor has exactly ThomClass's original principal-divisor coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.Principal.Constructions.FiberCoefficients
open OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Point.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [AlgebraicGeometry.IsNoetherian X.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
  (C : IrreducibleCloseds V.carrier)

include hg in
theorem openPrincipal_coefficient
    (hcover : ∀ y : (AmbientMap.Constructions.smoothNormalizationOver V W).left,
      (PrincipalBoundary.Constructions.fullAmbientMap V W).left y = IntersectionGeometry.supportPoint C → y ∈ Set.range a.left) :
    Point.Constructions.pointPushforward (a ≫ PrincipalBoundary.Constructions.fullAmbientMap V W).left
      (Point.Constructions.rationalPrincipalPointDivisor X.left (RationalOrderTransport.Constructions.openFunctionFieldMap a.left (PrincipalBoundary.Constructions.normalizedFunction V W g)))
      (IntersectionGeometry.supportPoint C) = IntersectionGeometry.principalDivisorCoefficient V.presentation W g C :=
  (Open.Principal.Constructions.FiberCoefficients.principalPointDivisor_open_fiber_coefficient a.left (PrincipalBoundary.Constructions.normalizedFunction V W g)
    (PrincipalBoundary.Constructions.fullAmbientMap V W).left (IntersectionGeometry.supportPoint C) hcover).trans
      (PrincipalBoundary.Constructions.normalizedPrincipal_coefficient V W g hg C)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenPrincipalCoefficients.Constructions
