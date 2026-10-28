import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.AffineBaseChange

noncomputable section

/-! Affineness of a base-changed open subscheme is affineness of the
literal inverse-image open in the base-changed ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem baseChange_open_affine {S T : Scheme.{0}} (f : T ⟶ S) (X : Over S)
    (U : X.left.Opens) (hU : IsAffine (pullback (U.ι ≫ X.hom) f)) :
    IsAffineOpen (pullback.fst X.hom f ⁻¹ᵁ U) := by
  let q := pullback.fst X.hom f
  let W := q ⁻¹ᵁ U
  have hs := (isPullback_morphismRestrict q U).paste_vert (IsPullback.of_hasPullback X.hom f)
  let e : W.toScheme ≅ pullback (U.ι ≫ X.hom) f := hs.isoPullback
  have : IsAffine (pullback (U.ι ≫ X.hom) f) := hU
  exact isAffine_of_isAffineHom e.hom

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.AffineBaseChange
