import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineFamilyTransport

/-! # Affine Family Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineFamilyComposition

noncomputable section

/-! Transferring projective-family maps to native families
preserves composition and identity. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {C : Type u} [CommRing C] (n : ℕ)
variable (f : Spec (.of C) ⟶ S)
variable (F G H : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f))

theorem affineNativeFamilyTransport_trans
    (e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) ≅
      Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f G))
    (e' : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f G) ≅
      Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f H)) :
    AffineFamilyTransport.affineNativeFamilyTransport n f F G e ≪≫ AffineFamilyTransport.affineNativeFamilyTransport n f G H e' =
      AffineFamilyTransport.affineNativeFamilyTransport n f F H (e ≪≫ e') := by
  simp only [AffineFamilyTransport.affineNativeFamilyTransport, Iso.trans_assoc, Iso.self_symm_id_assoc]

theorem affineNativeFamilyTransport_refl :
    AffineFamilyTransport.affineNativeFamilyTransport n f F F (Iso.refl _) = Iso.refl _ := by
  simp only [AffineFamilyTransport.affineNativeFamilyTransport, Iso.refl_trans, Iso.symm_self_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AffineFamilyComposition
