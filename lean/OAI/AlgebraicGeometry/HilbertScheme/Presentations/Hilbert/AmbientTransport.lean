import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Ambient Transport -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientTransport

noncomputable section

/-! Native Hilbert families transport across actual isomorphisms of their
ambient schemes and base schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S S' : Scheme.{u}} (X : Over S) (Y : Over S') {T : Over S} {U : Over S'}
variable (e : Functor.ambient X T ≅ Functor.ambient Y U) (b : T.left ≅ U.left)
variable (he : e.hom ≫ Functor.ambientProjection Y U = Functor.ambientProjection X T ≫ b.hom)

def ambientTransportMap (I : (Functor.ambient Y U).IdealSheafData) :
    (I.comap e.hom).subscheme ⟶ I.subscheme :=
  (I.comapIso e.hom).hom ≫ pullback.snd e.hom I.subschemeι

theorem ambientTransportMap_isPullback (I : (Functor.ambient Y U).IdealSheafData) :
    IsPullback (I.comap e.hom).subschemeι (ambientTransportMap X Y e I) e.hom I.subschemeι := by
  apply isPullback_of_isClosedImmersion
  · dsimp only [ambientTransportMap]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  · simp only [Scheme.IdealSheafData.ker_subschemeι]

include he

theorem ambientTransport_projection_isPullback (I : (Functor.ambient Y U).IdealSheafData) :
    IsPullback (Functor.familyProjection X (I.comap e.hom)) (ambientTransportMap X Y e I)
      b.hom (Functor.familyProjection Y I) :=
  (ambientTransportMap_isPullback X Y e I).paste_horiz
    (IsPullback.of_vert_isIso (show CommSq (Functor.ambientProjection X T) e.hom b.hom (Functor.ambientProjection Y U) from
      ⟨he.symm⟩))

def ambientTransport (F : Functor.Family Y U) : Functor.Family X T :=
  ⟨F.val.comap e.hom,
    MorphismProperty.of_isPullback (ambientTransport_projection_isPullback X Y e b he F.val).flip F.property.1,
    MorphismProperty.of_isPullback (ambientTransport_projection_isPullback X Y e b he F.val).flip F.property.2.1,
    MorphismProperty.of_isPullback (ambientTransport_projection_isPullback X Y e b he F.val).flip F.property.2.2⟩

theorem ambientTransport_inverse_compatibility :
    e.inv ≫ Functor.ambientProjection X T = Functor.ambientProjection Y U ≫ b.inv := by
  apply (cancel_epi e.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

def ambientFamilyEquiv : Functor.Family Y U ≃ Functor.Family X T where
  toFun := ambientTransport X Y e b he
  invFun := ambientTransport Y X e.symm b.symm (ambientTransport_inverse_compatibility X Y e b he)
  left_inv F := by
    apply Subtype.ext
    change (F.val.comap e.hom).comap e.inv = F.val
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  right_inv F := by
    apply Subtype.ext
    change (F.val.comap e.inv).comap e.hom = F.val
    rw [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientTransport
