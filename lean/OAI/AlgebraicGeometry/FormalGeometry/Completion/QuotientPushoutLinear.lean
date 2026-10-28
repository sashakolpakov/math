import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPushout

/-! # Quotient Pushout Linear -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPushoutLinear.Construction

noncomputable section

/-! Actual quotient pushout comparisons as linear equivalences on module quotients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (I : Ideal R) (a : S →ₐ[R] T) (b : R ⧸ I →+* T)
  (h : IsPushout (CommRingCat.ofHom (algebraMap R S))
    (CommRingCat.ofHom (Ideal.Quotient.mk I))
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b))

/-- The actual ring pushout isomorphism respects the original base algebra. -/
def quotientPushoutAlgEquiv : (S ⧸ I.map (algebraMap R S)) ≃ₐ[R] T :=
  AlgEquiv.ofRingEquiv
    (f := (QuotientPushout.Construction.quotientPushoutIso (algebraMap R S) I h).commRingCatIsoToRingEquiv) (fun r => by
      change (QuotientPushout.Construction.quotientPushoutIso (algebraMap R S) I h).hom
        (Ideal.Quotient.mk _ (algebraMap R S r)) = algebraMap R T r
      rw [QuotientPushout.Construction.quotientPushoutIso_mk]
      exact a.commutes r)

/-- A module quotient by the extended ideal computes the actual ring pushout. -/
def quotientPushoutLinearEquiv : (S ⧸ (I • ⊤ : Submodule R S)) ≃ₗ[R] T :=
  (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I)).trans
    ((Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R S))).trans
      (quotientPushoutAlgEquiv I a b h).toLinearEquiv)

theorem quotientPushoutLinearEquiv_mk (s : S) :
    quotientPushoutLinearEquiv I a b h (Submodule.Quotient.mk s) = a s := by
  change (QuotientPushout.Construction.quotientPushoutIso (algebraMap R S) I h).hom (Ideal.Quotient.mk _ s) = a s
  exact QuotientPushout.Construction.quotientPushoutIso_mk _ _ _ _

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPushoutLinear.Construction
