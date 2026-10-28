import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineFamilyTransport
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality

/-! # Affine Transport Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineTransportNaturality

noncomputable section

/-! Native family transports inherit coefficient naturality from
their ambient projective transports. The proof uses the actual
family pullback maps and the monomorphic closed embeddings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem iso_conjugate_natural {𝒞 : Type u} [Category.{v} 𝒞] {A A' B B' : 𝒞}
    (e : A ≅ B) (e' : A' ≅ B') (f : A' ⟶ A) (g : B' ⟶ B)
    (h : e'.hom ≫ g = f ≫ e.hom) (t : A ⟶ A) (t' : A' ⟶ A')
    (ht : t' ≫ f = f ≫ t) :
    (e'.inv ≫ t' ≫ e'.hom) ≫ g = g ≫ (e.inv ≫ t ≫ e.hom) := by
  have hi : e'.inv ≫ f = g ≫ e.inv := by
    apply (cancel_epi e'.hom).mp
    calc
      e'.hom ≫ (e'.inv ≫ f) = f := e'.hom_inv_id_assoc f
      _ = (f ≫ e.hom) ≫ e.inv := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
      _ = (e'.hom ≫ g) ≫ e.inv := congrArg (fun a => a ≫ e.inv) h.symm
      _ = e'.hom ≫ (g ≫ e.inv) := Category.assoc _ _ _
  calc
    _ = e'.inv ≫ t' ≫ f ≫ e.hom := by simp only [Category.assoc, h]
    _ = e'.inv ≫ (f ≫ t) ≫ e.hom := by rw [← Category.assoc t' f, ht]
    _ = (e'.inv ≫ f) ≫ t ≫ e.hom := by simp only [Category.assoc]
    _ = g ≫ (e.inv ≫ t ≫ e.hom) := by rw [hi]; simp only [Category.assoc]

variable {S : Scheme.{u}} {C A : Type u} [CommRing C] [CommRing A] (n : ℕ)
variable (f : Spec (.of C) ⟶ S) (φ : C →+* A)

def affineNativeAmbientTransport
    (E : Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)) ≅ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n))) :
    HilbertScheme.Presentations.Hilbert.Functor.ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) ⟶
      HilbertScheme.Presentations.Hilbert.Functor.ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) :=
  (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).inv ≫ E.hom.left ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom

theorem affineNativeAmbientTransport_natural
    (E : Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)) ≅ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)))
    (EA : Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)) ≅ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)))
    (h : EA.hom.left ≫ HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ = HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ ≫ E.hom.left) :
    affineNativeAmbientTransport n (Spec.map (CommRingCat.ofHom φ) ≫ f) EA ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) =
      HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) ≫ affineNativeAmbientTransport n f E :=
  iso_conjugate_natural (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f)
    (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (Spec.map (CommRingCat.ofHom φ) ≫ f)) _ _
    (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineProjectiveAmbientIso_naturality n f φ) _ _ h

theorem nativeAffineFamilyTransport_natural
    (F G : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f))
    (E : Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)) ≅ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)))
    (EA : Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)) ≅ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)))
    (hE : EA.hom.left ≫ HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ = HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap φ ≫ E.hom.left)
    (e : AffineFamilyTransport.affineNativeFamilyOver n f F ⟶ AffineFamilyTransport.affineNativeFamilyOver n f G)
    (eA : AffineFamilyTransport.affineNativeFamilyOver n (Spec.map (CommRingCat.ofHom φ) ≫ f)
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F) ⟶
      AffineFamilyTransport.affineNativeFamilyOver n (Spec.map (CommRingCat.ofHom φ) ≫ f)
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) G))
    (he : e.left ≫ G.val.subschemeι = F.val.subschemeι ≫ affineNativeAmbientTransport n f E)
    (heA : eA.left ≫ (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) G).val.subschemeι =
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F).val.subschemeι ≫
        affineNativeAmbientTransport n (Spec.map (CommRingCat.ofHom φ) ≫ f) EA) :
    eA.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) G.val =
      HilbertScheme.Presentations.Hilbert.Functor.familyMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F.val ≫ e.left := by
  let X := HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n
  let a := HilbertScheme.Presentations.Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ
  let FA := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F
  let GA := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G
  have hF : FA.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a =
      HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val ≫ F.val.subschemeι :=
    (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X a F.val).w
  have hG : GA.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a =
      HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val ≫ G.val.subschemeι :=
    (HilbertScheme.Presentations.Hilbert.Functor.family_ambient_isPullback X a G.val).w
  have hN := affineNativeAmbientTransport_natural n f φ E EA hE
  apply (cancel_mono G.val.subschemeι).mp
  calc
    _ = (eA.left ≫ GA.val.subschemeι) ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a := by
      rw [Category.assoc, ← hG, ← Category.assoc]
    _ = (FA.val.subschemeι ≫ affineNativeAmbientTransport n (Spec.map (CommRingCat.ofHom φ) ≫ f) EA) ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a := congrArg (fun b => b ≫ _) heA
    _ = (FA.val.subschemeι ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X a) ≫ affineNativeAmbientTransport n f E := by
      rw [Category.assoc, hN, ← Category.assoc]
    _ = (HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val ≫ F.val.subschemeι) ≫ affineNativeAmbientTransport n f E := by rw [hF]
    _ = (HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val ≫ e.left) ≫ G.val.subschemeι := by
      rw [Category.assoc, ← he, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineTransportNaturality
