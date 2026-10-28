import Mathlib

/-! # Separated Affine Intersection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SeparatedAffineIntersection

noncomputable section

/-!
# IntegralComparison: affine intersections over a separated scheme

The fiber product of two affine schemes mapping to a scheme separated
over an affine base is affine. Its map into their product over the base
is a closed immersion and therefore gives a surjection on coordinate rings.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

lemma spec_preimage_surjective {A B : CommRingCat.{u}}
    (g : Spec A ⟶ Spec B) [IsClosedImmersion g] :
    Function.Surjective (Spec.preimage g) := by
  let φ := Spec.preimage g
  have hg : Spec.map φ = g := Spec.map_preimage g
  have hs : Function.Surjective (Spec.map φ).appTop := by
    rw [hg]
    exact (IsClosedImmersion.isAffine_surjective_of_isAffine g).2
  have he : φ = (Scheme.ΓSpecIso B).inv ≫
      (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso A).hom := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [show Spec.preimage g = φ from rfl, he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).2.comp
    (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).2)

variable {A B R : CommRingCat.{u}} {X : Scheme.{u}}
variable (f : Spec A ⟶ X) (g : Spec B ⟶ X) (s : X ⟶ Spec R) [IsSeparated s]

include s in
lemma left_affine : IsAffineHom f := IsAffineHom.of_comp f s

include s in
lemma intersection_affine : IsAffine (pullback f g) := by
  let := left_affine f s
  infer_instance

abbrev CoordinateRing : CommRingCat.{u} := Γ(pullback f g, ⊤)

def affineIso : Spec (CoordinateRing f g) ≅ pullback f g := by
  letI := intersection_affine f g s
  exact (Scheme.isoSpec (pullback f g)).symm

def fst : Spec (CoordinateRing f g) ⟶ Spec A :=
  (affineIso f g s).hom ≫ pullback.fst f g

def snd : Spec (CoordinateRing f g) ⟶ Spec B :=
  (affineIso f g s).hom ≫ pullback.snd f g

lemma isPullback : IsPullback (SeparatedAffineIntersection.fst f g s) (SeparatedAffineIntersection.snd f g s) f g := by
  exact (IsPullback.of_hasPullback f g).of_iso
    (affineIso f g s).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [SeparatedAffineIntersection.fst]) (by simp [SeparatedAffineIntersection.snd]) (by simp) (by simp)

variable {Q : CommRingCat.{u}} (l : Spec Q ⟶ Spec A) (r : Spec Q ⟶ Spec B)
variable (h : IsPullback l r (f ≫ s) (g ≫ s))

def embedding : Spec (CoordinateRing f g) ⟶ Spec Q :=
  (affineIso f g s).hom ≫ pullback.mapDesc f g s ≫ h.isoPullback.inv

instance embedding_closed : IsClosedImmersion (embedding f g s l r h) := by
  unfold embedding
  infer_instance

lemma embedding_fst : embedding f g s l r h ≫ l = SeparatedAffineIntersection.fst f g s := by
  simp [embedding, SeparatedAffineIntersection.fst, pullback.mapDesc, pullback.map]
  exact pullback.lift_fst _ _ _

lemma embedding_snd : embedding f g s l r h ≫ r = SeparatedAffineIntersection.snd f g s := by
  simp [embedding, SeparatedAffineIntersection.snd, pullback.mapDesc, pullback.map]
  exact pullback.lift_snd _ _ _

lemma reduction_surjective : Function.Surjective (Spec.preimage (embedding f g s l r h)) :=
  spec_preimage_surjective _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SeparatedAffineIntersection
