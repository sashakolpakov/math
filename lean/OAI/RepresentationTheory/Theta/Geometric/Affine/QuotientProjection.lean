import OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientPoints

/-! # Quotient Projection -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientProjection

noncomputable section

/-! The projection from an actual affine quotient is the spectrum of
the composite base-ring map, with the canonical affine identifications. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem affineQuotientComposite_spec {B S : Scheme.{u}} [IsAffine S]
    (p : S ⟶ B) (I : Ideal Γ(S, ⊤)) :
    (QuotientPoints.affineQuotientScheme S I).hom ≫ p ≫ B.toSpecΓ =
      Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk I).comp p.appTop.hom)) := by
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ S.isoSpec.inv) ≫
    p ≫ B.toSpecΓ = _
  rw [Category.assoc, Scheme.toSpecΓ_naturality,
    ← Category.assoc S.isoSpec.inv S.toSpecΓ, Scheme.isoSpec_inv_toSpecΓ, Category.id_comp]
  exact (Spec.map_comp p.appTop (CommRingCat.ofHom (Ideal.Quotient.mk I))).symm

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.QuotientProjection
