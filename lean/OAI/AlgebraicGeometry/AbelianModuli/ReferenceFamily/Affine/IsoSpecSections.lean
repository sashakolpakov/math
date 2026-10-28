import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Iso Spec Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IsoSpecSections

noncomputable section

/-! The canonical affine isomorphism induces the original spectrum
isomorphism on global sections, with no choice of coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineIsoSpec_inv_appTop (X : Scheme.{0}) [IsAffine X] :
    X.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
  have h : X.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom :=
    Scheme.toSpecΓ_appTop X
  apply (cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
  rw [← h, ← Scheme.Hom.comp_appTop, X.isoSpec.inv_hom_id, Scheme.Hom.id_appTop,
    h, Iso.hom_inv_id]

theorem openInclusionTopSectionIso (X : Scheme.{0}) (U : X.Opens) :
    (IsOpenImmersion.ΓIsoTop U.ι).hom ≫
      X.presheaf.map (eqToHom U.opensRange_ι.symm).op = U.topIso.hom := by
  have h : (IsOpenImmersion.ΓIsoTop U.ι).inv =
      U.ι.appLE U.ι.opensRange ⊤ (by rw [U.ι.preimage_opensRange]) := by
    simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
      eqToIso.inv, Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  apply (cancel_epi (IsOpenImmersion.ΓIsoTop U.ι).inv).mp
  rw [Iso.inv_hom_id_assoc, h, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_hom]
  exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.IsoSpecSections
