import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReducedAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Smooth Reduced -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction

noncomputable section

/-! Reduced geometric fibers of smooth schemes in Openness. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- An affine smooth scheme over a field is reduced. -/
theorem isReduced_smooth_affine_over_field
    {K : Type u} [Field K] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X := by
  let φ := Spec.preimage (X.isoSpec.inv ≫ f)
  let : Algebra K Γ(X, ⊤) := φ.hom.toAlgebra
  have : Smooth (Spec.map φ) := by
    dsimp [φ]
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.Smooth K Γ(X, ⊤) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth) (φ := φ)).mp inferInstance
  have : _root_.IsReduced Γ(X, ⊤) := SmoothReducedAlgebra.Construction.isReduced_smooth_algebra_of_field K Γ(X, ⊤)
  exact isReduced_of_isAffine_isReduced X

/-- Every smooth scheme over a field is reduced. -/
theorem isReduced_smooth_over_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] : IsReduced X := by
  have (i : X.affineCover.I₀) : IsReduced (X.affineCover.X i) :=
    isReduced_smooth_affine_over_field (X.affineCover.f i ≫ f)
  exact IsReduced.of_openCover X X.affineCover

/-- Smooth morphisms have reduced fibers after every field extension. -/
theorem geometricallyReduced_of_smooth
    {X Y : Scheme} (f : X ⟶ Y) [Smooth f] : GeometricallyReduced f := by
  constructor
  intro K _ t Z h g hp
  have : Smooth g := MorphismProperty.of_isPullback hp inferInstance
  exact isReduced_smooth_over_field g

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction
