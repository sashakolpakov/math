import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Abelian Integrality -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianIntegrality

noncomputable section

/-! The original smooth integral complex abelian variety remains
integral after every geometric extension of the base. -/

open _root_.AlgebraicGeometry

theorem abelian_geometricallyIntegral (A : OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    GeometricallyIntegral A.toOver.hom := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  let : GeometricallyReduced A.toOver.hom := OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_geometricallyReduced A.toOver.hom
  let : GeometricallyIrreducible A.toOver.hom :=
    ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents.Construction.integral_geometricallyIrreducible_over_algClosed A.toOver.hom
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible A.toOver.hom

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianIntegrality
