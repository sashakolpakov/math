import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Integral Connected -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.IntegralConnected.Construction

/-! Geometric integrality implies geometric connectedness on every actual field base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

instance (priority := low) geometricallyIntegral_geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIntegral f] : GeometricallyConnected f := by
  constructor
  intro K _ g W p q H
  have : IsIntegral W := GeometricallyIntegral.geometrically_isIntegral g p q H
  infer_instance

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.IntegralConnected.Construction
