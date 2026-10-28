import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point

/-! # Tangent Point Coefficients -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.TangentPointCoefficients

noncomputable section

/-! Actual relative tangent maps act on affine coordinate germs
by the original scheme map. No choice of tangent coordinates is assumed. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace RelativeTangent

variable {C : CommRingCat.{0}} [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
  {X Y : Scheme.{0}} (p : Y ⟶ X) (g : Spec C ⟶ Y)

theorem point_coefficients (v : Relative.TangentBaseChange.RelativeTangent.Space J hJ p g) :
    HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (Relative.TangentBaseChange.RelativeTangent.point J hJ p g v) =
      v.val.hom.comp (Y.presheaf.Γgerm (g (IsLocalRing.closedPoint C))).hom := by
  have h : Spec.map (CommRingCat.ofHom (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (Relative.TangentBaseChange.RelativeTangent.point J hJ p g v))) =
      Spec.map (Y.presheaf.Γgerm (g (IsLocalRing.closedPoint C)) ≫ CommRingCat.ofHom v.val.hom) := by
    rw [HilbertScheme.Presentations.Projective.Point.schemePointCoefficientMap_spec]
    change (Spec.map (CommRingCat.ofHom v.val.hom) ≫ Y.fromSpecStalk _) ≫ Y.toSpecΓ = _
    rw [Category.assoc, Scheme.fromSpecStalk_toSpecΓ]
    exact (Spec.map_comp (Y.presheaf.Γgerm _) (CommRingCat.ofHom v.val.hom)).symm
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

omit [IsLocalRing C] in
theorem coefficientMap_postcomp {Z : Scheme.{0}} (z : Spec C ⟶ Y) (f : Y ⟶ Z) :
    HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (z ≫ f) = (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap z).comp f.appTop.hom := by
  apply RingHom.ext
  intro b
  change (Scheme.ΓSpecIso C).hom ((z ≫ f).appTop b) = (Scheme.ΓSpecIso C).hom (z.appTop (f.appTop b))
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem map_germ {X' Y' : Scheme.{0}} (p' : Y' ⟶ X') (g' : Spec C ⟶ Y')
    (f : Y ⟶ Y') (a : X ⟶ X') (hf : f ≫ p' = p ≫ a) (hg : g ≫ f = g')
    (v : Relative.TangentBaseChange.RelativeTangent.Space J hJ p g) (b : Γ(Y', ⊤)) :
    (Relative.TangentBaseChange.RelativeTangent.map J hJ p g p' g' f a hf hg v).val.hom (Y'.presheaf.Γgerm (g' (IsLocalRing.closedPoint C)) b) =
      v.val.hom (Y.presheaf.Γgerm (g (IsLocalRing.closedPoint C)) (f.appTop b)) := by
  have h : HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (Relative.TangentBaseChange.RelativeTangent.point J hJ p' g' (Relative.TangentBaseChange.RelativeTangent.map J hJ p g p' g' f a hf hg v)) =
      (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (Relative.TangentBaseChange.RelativeTangent.point J hJ p g v)).comp f.appTop.hom := by
    rw [Relative.TangentBaseChange.RelativeTangent.point_map]
    exact coefficientMap_postcomp _ _
  rw [point_coefficients, point_coefficients] at h
  exact RingHom.congr_fun h b

end RelativeTangent

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.TangentPointCoefficients
