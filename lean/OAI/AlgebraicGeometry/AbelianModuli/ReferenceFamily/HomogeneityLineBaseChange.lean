import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityUniversalTest
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousBaseTwists
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection

/-! # Homogeneity Line Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange

noncomputable section

section

/-! Original all-test homogeneity is detected by an actual isomorphism
between two normalized line bundles on the universal translation family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem normalizedProductBundle_relative {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (T : Over S) (L : HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left) :
    (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A T L)) =
      (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
  (congrArg ((HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T)) (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class A T L)).trans
    (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_relative A T (HilbertConstruction.Line.Bundles.LineBundle.classOf L))

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) {P : Over (Spec (.of k))}
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)

def universalParameterLine : HilbertConstruction.Line.Bundles.LineBundle ((P ⊗ A.scheme) ⊗ A.scheme).left :=
  Q.pullback ((fst P A.scheme) ⊗ₘ 𝟙 A.scheme).left

def universalTranslationLine : HilbertConstruction.Line.Bundles.LineBundle ((P ⊗ A.scheme) ⊗ A.scheme).left :=
  (universalParameterLine A Q).pullback (A.translation (snd P A.scheme)).left

def normalizedUniversalParameterLine : HilbertConstruction.Line.Bundles.LineBundle ((P ⊗ A.scheme) ⊗ A.scheme).left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme (P ⊗ A.scheme) (universalParameterLine A Q)

def normalizedUniversalTranslationLine : HilbertConstruction.Line.Bundles.LineBundle ((P ⊗ A.scheme) ⊗ A.scheme).left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme (P ⊗ A.scheme) (universalTranslationLine A Q)

theorem homogeneous_iff_universal_normalized_lineIso
    [CompactSpace (P ⊗ A.scheme).left] [QuasiSeparatedSpace (P ⊗ A.scheme).left] :
    A.IsHomogeneousPicardClass P (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) ↔
      Nonempty ((normalizedUniversalTranslationLine A Q).sheaf ≅ (normalizedUniversalParameterLine A Q).sheaf) := by
  rw [HomogeneityUniversalTest.parameterHomogeneous_iff_universal_translation A Q]
  have ht := normalizedProductBundle_relative A.scheme (P ⊗ A.scheme) (universalTranslationLine A Q)
  have hp := normalizedProductBundle_relative A.scheme (P ⊗ A.scheme) (universalParameterLine A Q)
  constructor
  · intro h
    exact PELModuli.IntegralModel.NormalizedPicardInjection.NormalizedPicard.iso_of_picard_eq A _ _
      (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.scheme (P ⊗ A.scheme) (universalTranslationLine A Q))
      (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.scheme (P ⊗ A.scheme) (universalParameterLine A Q))
      (ht.trans (h.trans hp.symm))
  · intro h
    exact ht.symm.trans ((congrArg ((HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (P ⊗ A.scheme)))
      (Quotient.sound h)).trans hp)

end

/-! Both actual line bundles detecting homogeneity commute with
parameter change, through their original line-bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem normalizedProductBundle_pullbackClass {S : Scheme.{0}} (A : Over S) [GrpObj A]
    {P T : Over S} (u : T ⟶ P) (L : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A).left) (N : HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left)
    (h : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (u ⊗ₘ 𝟙 A).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = HilbertConstruction.Line.Bundles.LineBundle.classOf N) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (u ⊗ₘ 𝟙 A).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A P L)) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A T N) :=
  (congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (u ⊗ₘ 𝟙 A).left) (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class A P L)).trans
    ((FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_pullback A u (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans
      ((congrArg (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass A T) h).trans (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class A T N).symm))

variable {k : Type} [Field k] {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) {P T : Over (Spec (.of k))}
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left) (u : T ⟶ P)

theorem universalParameterLine_class_naturality :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((u ⊗ₘ 𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (universalParameterLine A Q)) =
    HilbertConstruction.Line.Bundles.LineBundle.classOf (universalParameterLine A (Q.pullback (u ⊗ₘ 𝟙 A.scheme).left)) := by
  have hf : (u ⊗ₘ 𝟙 A.scheme) ≫ fst P A.scheme = fst T A.scheme ≫ u := by simp
  exact (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_naturality Q (fst P A.scheme) (u ⊗ₘ 𝟙 A.scheme)).trans
    ((congrArg (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q) hf).trans (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass_baseChange Q u (fst T A.scheme)))

theorem universalTranslationLine_class_naturality :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((u ⊗ₘ 𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (universalTranslationLine A Q)) =
    HilbertConstruction.Line.Bundles.LineBundle.classOf (universalTranslationLine A (Q.pullback (u ⊗ₘ 𝟙 A.scheme).left)) := by
  have hs : (u ⊗ₘ 𝟙 A.scheme) ≫ snd P A.scheme = snd T A.scheme := by simp
  have h := A.translationClass_naturality (u ⊗ₘ 𝟙 A.scheme) (snd P A.scheme)
    (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q (fst P A.scheme))
  exact h.trans (congrArg₂ (fun a q => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left q)
    hs (universalParameterLine_class_naturality A Q u))

theorem normalizedUniversalParameterLine_class_naturality :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((u ⊗ₘ 𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedUniversalParameterLine A Q)) =
    HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedUniversalParameterLine A (Q.pullback (u ⊗ₘ 𝟙 A.scheme).left)) :=
  normalizedProductBundle_pullbackClass A.scheme (u ⊗ₘ 𝟙 A.scheme) _ _
    (universalParameterLine_class_naturality A Q u)

theorem normalizedUniversalTranslationLine_class_naturality :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((u ⊗ₘ 𝟙 A.scheme) ⊗ₘ 𝟙 A.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedUniversalTranslationLine A Q)) =
    HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedUniversalTranslationLine A (Q.pullback (u ⊗ₘ 𝟙 A.scheme).left)) :=
  normalizedProductBundle_pullbackClass A.scheme (u ⊗ₘ 𝟙 A.scheme) _ _
    (universalTranslationLine_class_naturality A Q u)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange
