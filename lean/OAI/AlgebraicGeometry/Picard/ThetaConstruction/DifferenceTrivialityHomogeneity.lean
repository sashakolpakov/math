import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineTranslation
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeTriviality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousLinePowers

/-! # Difference Triviality Homogeneity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceTrivialityHomogeneity.Geometric

noncomputable section

section

/-! Actual triviality of the normalized difference bundle implies
homogeneity on every original test scheme. Conversely, universal
translation invariance supplies the trivialization over a Noetherian base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem translationInvariant_of_difference_trivial
    (e : (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A.scheme ⊗ A.scheme).left)
    {T : Over S} (a : T ⟶ A.scheme) :
    A.TranslationInvariant a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd T A.scheme).left)) := by
  let D := RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A.scheme).left :=
    Quotient.sound ⟨(Scheme.Modules.pullback (a ⊗ₘ 𝟙 A.scheme).left).mapIso e ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (a ⊗ₘ 𝟙 A.scheme).left⟩
  apply (ReferenceLineTranslation.Geometric.relativeDifference_zero_iff_originalTranslation A L a).mp
  exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T)) hc

theorem constantFamily_homogeneous_of_difference_trivial
    (e : (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A.scheme ⊗ A.scheme).left)
    (T : Over S) :
    A.IsHomogeneousPicardClass T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd T A.scheme).left)) := by
  intro U f a
  let σ : (U ⊗ A.scheme).left ⟶ (T ⊗ A.scheme).left := (f ⊗ₘ 𝟙 A.scheme).left
  have hs : σ ≫ (snd T A.scheme).left = (snd U A.scheme).left :=
    (congrArg Over.Hom.left (tensorHom_snd f (𝟙 A.scheme))).trans (Category.comp_id _)
  have hclass : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass σ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd T A.scheme).left)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left) :=
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp σ (snd T A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      (congrArg (fun z => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hs)
  change A.TranslationInvariant a
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass σ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd T A.scheme).left)))
  exact (congrArg (A.TranslationInvariant a) hclass).mpr
    (translationInvariant_of_difference_trivial A L e a)

variable [IsLocallyNoetherian S]

theorem difference_trivial_of_identity_translation
    (h : A.TranslationInvariant (𝟙 A.scheme)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd A.scheme A.scheme).left))) :
    Nonempty ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A.scheme ⊗ A.scheme).left) := by
  let : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  have hz := (ReferenceLineTranslation.Geometric.relativeDifference_zero_iff_originalTranslation A L (𝟙 A.scheme)).mpr h
  have hc := RelativeTriviality.Geometric.noetherian_relativeRigidified_class_trivial (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L) (𝟙 A.scheme) hz
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (A.scheme ⊗ A.scheme).left at hc
  rw [id_tensorHom_id] at hc
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 (A.scheme ⊗ A.scheme).left)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (A.scheme ⊗ A.scheme).left at hc
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at hc
  exact Quotient.exact hc

end

/-! Over a field, the original homogeneous line-class predicate is
equivalent to actual triviality of the normalized difference bundle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {k : Type} [Field k] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)

theorem difference_trivial_iff_homogeneous_line :
    Nonempty ((RelativeDifferenceBundle.Geometric.relativeDifferenceBundle A L).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (A.scheme ⊗ A.scheme).left) ↔
      AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  constructor
  · rintro ⟨e⟩
    exact constantFamily_homogeneous_of_difference_trivial A L e (Over.mk (𝟙 (Spec (.of k))))
  · intro hL
    apply difference_trivial_of_identity_translation A L
    have h := (hL.family A A.scheme) A.scheme (𝟙 A.scheme) (𝟙 A.scheme)
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op A.scheme)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (𝟙 A.scheme)).left
          ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 A.scheme).op
            (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op A.scheme)
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 A.scheme).op
          (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) at h
    let q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (op A.scheme) :=
      AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A A.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)
    have hid : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 (op A.scheme)) q = q := by
      exact ConcreteCategory.congr_hom
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_id (op A.scheme)) q
    have ht : A.TranslationInvariant (𝟙 A.scheme)
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map (𝟙 (op A.scheme)) q) := h
    exact (congrArg (A.TranslationInvariant (𝟙 A.scheme)) hid).mp ht

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.DifferenceTrivialityHomogeneity.Geometric
