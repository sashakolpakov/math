import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Abelian Geometric Integrality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AbelianGeometricIntegrality

/-! The original abelian-scheme hypotheses supply geometric integrality over a field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-- Every field-valued base change is connected and smooth proper, hence integral. -/
theorem geometricallyIntegral {k : Type u} [Field k] {a : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))) : GeometricallyIntegral A.scheme.hom := by
  constructor
  intro K _ g Z p q H
  have : Smooth q := MorphismProperty.of_isPullback (P := @Smooth) H inferInstance
  have : IsProper q := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have : ConnectedSpace Z :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.scheme.hom) g p q H
  exact ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral q

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AbelianGeometricIntegrality
