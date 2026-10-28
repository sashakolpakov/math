import OAI.ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Integral Geometric Fibers -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralGeometricFibers.BundleCycles

noncomputable section

/-! The actual integral components of a smooth projective complex
scheme remain integral after arbitrary extension of the base field. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem smoothIntegral_geometricallyIntegral_over_algClosed {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [Smooth f] : GeometricallyIntegral f := by
  let : GeometricallyIrreducible f := ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents.Construction.integral_geometricallyIrreducible_over_algClosed f
  let : GeometricallyReduced f := Quotients.FiniteDescent.SchemeSmooth.Construction.SchemeSmoothReduced.geometricallyReduced_of_smooth f
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f

theorem projectiveComponent_geometricallyIntegral (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) : GeometricallyIntegral (X.componentVariety C).structureMap := by
  let : Smooth X.structureMap := X.smooth
  let : Smooth (X.componentVariety C).structureMap := by
    rw [← X.componentInclusion_over C]
    infer_instance
  exact smoothIntegral_geometricallyIntegral_over_algClosed _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralGeometricFibers.BundleCycles
