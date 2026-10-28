import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine Chart Section Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.AffineChartSectionCoordinates

noncomputable section

section

/-! Regular-function coordinates under actual affine scheme maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem specMap_section_naturality {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (r : Γ(Spec (.of R), ⊤)) :
    (Scheme.ΓSpecIso (.of S)).hom ((Spec.map (CommRingCat.ofHom f)).appTop r) =
      f ((Scheme.ΓSpecIso (.of R)).hom r) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)) r

theorem specMap_appTop_injective {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop := by
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom).injective
  apply hf
  exact (specMap_section_naturality f a).symm.trans
    ((congrArg (Scheme.ΓSpecIso (.of S)).hom hab).trans (specMap_section_naturality f b))

theorem specMap_pair_comp_of_ring_eq {A R S : Type} [CommRing A] [CommRing R] [CommRing S]
    (i : A →+* R) (f g : R →+* S) (h : f.comp i = g.comp i) :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom i) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom i) := by
  have h' : CommRingCat.ofHom i ≫ CommRingCat.ofHom f =
      CommRingCat.ofHom i ≫ CommRingCat.ofHom g := congrArg CommRingCat.ofHom h
  exact (Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom f)).symm.trans
    ((congrArg Spec.map h').trans (Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom g)))

end

/-! The actual global sections and units of an affine scheme are
identified with its chosen coordinate ring, naturally in chart maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def affineChartSectionEquiv {X : Scheme} {R : Type} [CommRing R]
    (e : X ≅ Spec (.of R)) : Γ(X, ⊤) ≃+* R := by
  have : IsIso e.inv.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.inv.op))
  exact (asIso e.inv.appTop ≪≫ Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv

theorem affineChartSectionEquiv_apply {X : Scheme} {R : Type} [CommRing R]
    (e : X ≅ Spec (.of R)) (r : Γ(X, ⊤)) :
    affineChartSectionEquiv e r = (Scheme.ΓSpecIso (.of R)).hom (e.inv.appTop r) := rfl

theorem affineChartSectionEquiv_natural
    {X Y : Scheme} {R S : Type} [CommRing R] [CommRing S]
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S))
    (b : X ⟶ Y) (f : S →+* R)
    (hb : eX.hom ≫ Spec.map (CommRingCat.ofHom f) = b ≫ eY.hom) (r : Γ(Y, ⊤)) :
    affineChartSectionEquiv eX (b.appTop r) = f (affineChartSectionEquiv eY r) := by
  have hh : eX.inv ≫ b = Spec.map (CommRingCat.ofHom f) ≫ eY.inv := by
    apply (cancel_mono eY.hom).mp
    rw [Category.assoc, ← hb, Iso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  calc
    affineChartSectionEquiv eX (b.appTop r) =
        (Scheme.ΓSpecIso (.of R)).hom ((eX.inv ≫ b).appTop r) := rfl
    _ = (Scheme.ΓSpecIso (.of R)).hom
        ((Spec.map (CommRingCat.ofHom f)).appTop (eY.inv.appTop r)) := by rw [hh]; rfl
    _ = f (affineChartSectionEquiv eY r) := specMap_section_naturality f _

theorem affineChartUnitEquiv_natural
    {X Y : Scheme} {R S : Type} [CommRing R] [CommRing S]
    (eX : X ≅ Spec (.of R)) (eY : Y ≅ Spec (.of S))
    (b : X ⟶ Y) (f : S →+* R)
    (hb : eX.hom ≫ Spec.map (CommRingCat.ofHom f) = b ≫ eY.hom) (u : Γ(Y, ⊤)ˣ) :
    Units.map (affineChartSectionEquiv eX).toMonoidHom (Units.map b.appTop.hom.toMonoidHom u) =
      Units.map f.toMonoidHom (Units.map (affineChartSectionEquiv eY).toMonoidHom u) := by
  apply Units.ext
  exact affineChartSectionEquiv_natural eX eY b f hb (u : Γ(Y, ⊤))

end

end OAI.RepresentationTheory.Theta.Geometric.AffineChartSectionCoordinates
