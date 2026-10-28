import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.EmbeddingKernelIso
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies

/-! # Affine Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineFamilyTransport

noncomputable section

/-! Canonical homogeneous coordinates recover the actual native
Hilbert family as a scheme over the affine base. Compatible
projective transports therefore give actual native-family isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert
universe u
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {C : Type u} [CommRing C] (n : ℕ)
variable (f : Spec (.of C) ⟶ S)
variable (F G : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f))

def affineNativeFamilyOver : Over (Spec (.of C)) :=
  Over.mk (HilbertScheme.Presentations.Hilbert.Functor.familyProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) F.val)

def affineNativeFamilyEmbedding : affineNativeFamilyOver n f F ⟶
    Over.mk (HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) :=
  Over.homMk F.val.subschemeι rfl

def affineNativeHomogeneousEmbedding :
    Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ⟶
      Over.mk (HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) :=
  Over.homMk (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≫
    (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom) (by
      erw [Category.assoc, HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projection, HilbertScheme.Presentations.Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure]
      rfl)

def affineNativeHomogeneousFamilyIso :
    Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≅ affineNativeFamilyOver n f F := by
  have : IsClosedImmersion (affineNativeHomogeneousEmbedding n f F).left :=
    inferInstanceAs (IsClosedImmersion (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≫
      (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom))
  have : IsClosedImmersion (affineNativeFamilyEmbedding n f F).left :=
    inferInstanceAs (IsClosedImmersion F.val.subschemeι)
  exact Closed.EmbeddingKernelIso.closedEmbeddingKernelIso (affineNativeHomogeneousEmbedding n f F) (affineNativeFamilyEmbedding n f F)
    ((HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_global_kernel n f F).trans F.val.ker_subschemeι.symm)

theorem affineNativeHomogeneousFamilyIso_ambient :
    (affineNativeHomogeneousFamilyIso n f F).hom.left ≫ F.val.subschemeι =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom := by
  have : IsClosedImmersion (affineNativeHomogeneousEmbedding n f F).left :=
    inferInstanceAs (IsClosedImmersion (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≫
      (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom))
  have : IsClosedImmersion (affineNativeFamilyEmbedding n f F).left :=
    inferInstanceAs (IsClosedImmersion F.val.subschemeι)
  exact congrArg Over.Hom.left (Closed.EmbeddingKernelIso.closedEmbeddingKernelIso_embedding
    (affineNativeHomogeneousEmbedding n f F) (affineNativeFamilyEmbedding n f F)
    ((HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_global_kernel n f F).trans F.val.ker_subschemeι.symm))

def affineNativeFamilyTransport
    (e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≅
      Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f G)) :
    affineNativeFamilyOver n f F ≅ affineNativeFamilyOver n f G :=
  (affineNativeHomogeneousFamilyIso n f F).symm ≪≫ e ≪≫ affineNativeHomogeneousFamilyIso n f G

theorem affineNativeFamilyTransport_ambient
    (e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≅
      Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f G))
    (E : Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)) ≅ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)))
    (he : e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f G) =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≫ E.hom.left) :
    (affineNativeFamilyTransport n f F G e).hom.left ≫ G.val.subschemeι =
      F.val.subschemeι ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).inv ≫ E.hom.left ≫
        (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom := by
  let eF := affineNativeHomogeneousFamilyIso n f F
  let eG := affineNativeHomogeneousFamilyIso n f G
  have hF := affineNativeHomogeneousFamilyIso_ambient n f F
  have hG := affineNativeHomogeneousFamilyIso_ambient n f G
  have hi : eF.hom.left ≫ eF.inv.left = 𝟙 _ := congrArg Over.Hom.left eF.hom_inv_id
  have hp : eF.hom.left ≫ F.val.subschemeι ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).inv =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) := by
    rw [← Category.assoc, hF, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi eF.hom.left).mp
  change eF.hom.left ≫ ((eF.inv.left ≫ e.hom.left ≫ eG.hom.left) ≫ G.val.subschemeι) = _
  calc
    _ = e.hom.left ≫ eG.hom.left ≫ G.val.subschemeι := by
      simp only [← Category.assoc, hi, Category.id_comp]
    _ = HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≫
        (E.hom.left ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom) := by
      rw [hG, ← Category.assoc, he, Category.assoc]
    _ = (eF.hom.left ≫ F.val.subschemeι ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).inv) ≫
        (E.hom.left ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom) := congrArg (fun p => p ≫ _) hp.symm
    _ = _ := by simp only [Category.assoc]

theorem affineNativeFamilyTransport_existsUnique
    (E : Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)) ≅ Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n)))
    (h : ∃ e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≅
      Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f G),
      e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f G) =
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≫ E.hom.left) :
    ∃! e : affineNativeFamilyOver n f F ≅ affineNativeFamilyOver n f G,
      e.hom.left ≫ G.val.subschemeι = F.val.subschemeι ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).inv ≫
        E.hom.left ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom := by
  obtain ⟨e, he⟩ := h
  refine ⟨affineNativeFamilyTransport n f F G e, affineNativeFamilyTransport_ambient n f F G e E he,
    fun t ht => ?_⟩
  apply Iso.ext
  apply Over.OverMorphism.ext
  apply (cancel_mono G.val.subschemeι).mp
  exact ht.trans (affineNativeFamilyTransport_ambient n f F G e E he).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineFamilyTransport
