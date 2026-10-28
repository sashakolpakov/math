import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DomainReduced
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Reduced Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers

noncomputable section

/-! Smooth morphisms have geometrically reduced fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X S : Scheme.{u}}

theorem smoothOverField_affine_isReduced (p : X ⟶ Spec (.of K)) [IsAffine X]
    [Smooth p] : IsReduced X := by
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have hp : p.appTop.hom.Smooth :=
    (HasRingHomProperty.iff_of_isAffine (P := @Smooth) (f := p)).mp inferInstance
  algebraize [p.appTop.hom]
  have : _root_.IsReduced Γ(X, ⊤) := DomainReduced.smooth_domain_isReduced Γ(Spec (.of K), ⊤) Γ(X, ⊤)
  exact isReduced_of_isAffine_isReduced X

theorem smoothOverField_isReduced (p : X ⟶ Spec (.of K)) [Smooth p] : IsReduced X := by
  have (i : X.affineCover.I₀) : IsReduced (X.affineCover.X i) :=
    smoothOverField_affine_isReduced (X.affineCover.f i ≫ p)
  exact IsReduced.of_openCover X X.affineCover

theorem smooth_geometricallyReduced (p : X ⟶ S) [Smooth p] : GeometricallyReduced p := by
  constructor
  intro K _ b Z fst snd H
  have : Smooth snd := MorphismProperty.of_isPullback H inferInstance
  exact smoothOverField_isReduced snd

theorem smooth_reducedSource (p : X ⟶ S) [Smooth p] [IsReduced S] [IsLocallyNoetherian S] :
    IsReduced X := by
  have : GeometricallyReduced p := smooth_geometricallyReduced p
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers
