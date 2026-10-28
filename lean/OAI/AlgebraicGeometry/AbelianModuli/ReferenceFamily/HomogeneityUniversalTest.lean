import OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent

/-! # Homogeneity Universal Test -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityUniversalTest

noncomputable section

/-! The original all-test homogeneity condition is equivalent to
one actual translation identity on the universal parameter product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent

variable {S : Scheme} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {P : Over S}
    (Q : HilbertConstruction.Line.Bundles.LineBundle (P ⊗ A.scheme).left)

theorem parameterHomogeneous_iff_universal_translation :
    A.IsHomogeneousPicardClass P (HilbertConstruction.Line.Bundles.LineBundle.classOf Q) ↔
      (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (P ⊗ A.scheme))
        (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (snd P A.scheme)).left
          (RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass Q (fst P A.scheme))) =
        RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass Q (fst P A.scheme) := by
  constructor
  · intro h
    exact h (P ⊗ A.scheme) (fst P A.scheme) (snd P A.scheme)
  · intro h U f a
    have hu := congrArg ((HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map (lift f a).op) h
    rw [RepresentationTheory.Theta.Geometric.HomogeneousParameterDescent.parameterTranslationPicard_naturality, RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterPicardClass_naturality,
      lift_fst, lift_snd] at hu
    exact hu

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneityUniversalTest
