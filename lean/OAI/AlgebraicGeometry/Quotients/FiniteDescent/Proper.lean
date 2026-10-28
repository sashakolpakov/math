import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Proper.Construction.Geometry

/-!
# Geometric properties inherited by a quotient

Geometric connectedness passes to a surjective image because this remains a
surjective continuous image after every field-valued base change.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A surjective image of a geometrically connected scheme over a base is
geometrically connected over the same base. -/
theorem geometricallyConnected_of_comp
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [Surjective q] [GeometricallyConnected (q ≫ b)] : GeometricallyConnected b := by
  constructor
  intro K _ k Y p₁ p₂ h
  have : ConnectedSpace ↥(pullback q p₁) :=
    GeometricallyConnected.geometrically_connectedSpace k (pullback.fst q p₁)
      (pullback.snd q p₁ ≫ p₂) ((IsPullback.of_hasPullback q p₁).paste_vert h)
  exact (pullback.snd q p₁).surjective.connectedSpace (pullback.snd q p₁).continuous

/-- Once separatedness and local finite type are established, properness of
the quotient follows from properness of its surjective source. -/
theorem proper_of_comp
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [Surjective q] [IsProper (q ≫ b)] [IsSeparated b] [LocallyOfFiniteType b] :
    IsProper b := by
  have : UniversallyClosed b := UniversallyClosed.of_comp_surjective q b
  exact ⟨⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Proper.Construction.Geometry
