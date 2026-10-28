import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousBaseTwists
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.BundleNormalization

/-! # Generic Universal Homogeneity -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericUniversalHomogeneity.Geometric.GenericHomogeneity

noncomputable section

/-! Original all-test homogeneity is detected by an actual isomorphism
between two normalized line bundles on the universal translation family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.BundleNormalization.Construction

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {P : Over S}
    (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)

def universalParameterLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((P ⊗ A.scheme) ⊗ A.scheme).left :=
  Q.pullback ((fst P A.scheme) ⊗ₘ 𝟙 A.scheme).left

def universalTranslationLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((P ⊗ A.scheme) ⊗ A.scheme).left :=
  (universalParameterLine A Q).pullback (A.translation (snd P A.scheme)).left

def normalizedUniversalParameterLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((P ⊗ A.scheme) ⊗ A.scheme).left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme (P ⊗ A.scheme) (universalParameterLine A Q)

def normalizedUniversalTranslationLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((P ⊗ A.scheme) ⊗ A.scheme).left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle A.scheme (P ⊗ A.scheme) (universalTranslationLine A Q)

theorem homogeneous_iff_universal_normalized_lineIso
    (hA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme) :
    A.IsHomogeneousPicardClass P (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q) ↔
      Nonempty ((normalizedUniversalTranslationLine A Q).sheaf ≅ (normalizedUniversalParameterLine A Q).sheaf) := by
  rw [AbelianModuli.ReferenceFamily.HomogeneityUniversalTest.parameterHomogeneous_iff_universal_translation A Q]
  have ht := AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange.normalizedProductBundle_relative A.scheme (P ⊗ A.scheme) (universalTranslationLine A Q)
  have hp := AbelianModuli.ReferenceFamily.HomogeneityLineBaseChange.normalizedProductBundle_relative A.scheme (P ⊗ A.scheme) (universalParameterLine A Q)
  constructor
  · intro h
    exact AbelianScheme.IsogenyQuotient.Universal.BundleNormalization.Construction.universal_bundleIso_of_relativePicard_eq A.scheme (P ⊗ A.scheme) hA
      (normalizedUniversalTranslationLine A Q) (normalizedUniversalParameterLine A Q)
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero A (P ⊗ A.scheme)).left
      (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection A (P ⊗ A.scheme))
      ((FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.scheme (P ⊗ A.scheme) (universalTranslationLine A Q)) ≪≫
        (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis A.scheme (P ⊗ A.scheme) (universalParameterLine A Q)).symm)
      (ht.trans (h.trans hp.symm))
  · intro h
    exact ht.symm.trans ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (P ⊗ A.scheme)))
      (Quotient.sound h)).trans hp)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericUniversalHomogeneity.Geometric.GenericHomogeneity
