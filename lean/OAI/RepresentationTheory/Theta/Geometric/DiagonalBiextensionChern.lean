import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChernPullbackLaws

/-! # Diagonal Biextension Chern -/

namespace OAI.RepresentationTheory.Theta.Geometric.DiagonalBiextensionChern

noncomputable section

/-! Pulling the actual biextension tensor identity along the diagonal
recovers the doubling-minus-two formula with its original normalization. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def abelianDiagonal (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : A.toOver ⟶ A.toOver ⊗ A.toOver :=
  lift (𝟙 A.toOver) (𝟙 A.toOver)

theorem abelianDiagonal_mul (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    abelianDiagonal A ≫ MonObj.mul (X := A.toOver) = (𝟙 A.toOver) ^ 2 := by
  rw [pow_two, Hom.mul_def]
  rfl

theorem diagonalBiextension_chern (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.toOver ⊗ A.toOver).left)
    (e : ((B.tensor (L.pullback (fst A.toOver A.toOver).left)).tensor
      (L.pullback (snd A.toOver A.toOver).left)).sheaf ≅
        (L.pullback (MonObj.mul (X := A.toOver)).left).sheaf) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation (B.pullback (abelianDiagonal A).left) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity.nativeChernPullback ((𝟙 A.toOver) ^ 2) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L) -
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L - AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L := by
  let X := A.variety.presentation
  let Z := AlgebraicGeometry.Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation X X
  let c := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass X L
  have hb := AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity.lineBundleChernClass_biextension A L B e
  have hd := congrArg (AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity.nativeChernPullback (X := Z) (Y := X) (abelianDiagonal A)) hb
  rw [map_sub, map_sub,
    Intrinsic.ChernPullbackLaws.nativeChernPullback_comp (X := X) (Y := Z) (Z := X) (abelianDiagonal A) (MonObj.mul (X := A.toOver)),
    Intrinsic.ChernPullbackLaws.nativeChernPullback_comp (X := X) (Y := Z) (Z := X) (abelianDiagonal A) (fst A.toOver A.toOver),
    Intrinsic.ChernPullbackLaws.nativeChernPullback_comp (X := X) (Y := Z) (Z := X) (abelianDiagonal A) (snd A.toOver A.toOver), abelianDiagonal_mul] at hd
  have hf : abelianDiagonal A ≫ fst A.toOver A.toOver = 𝟙 A.toOver := lift_fst _ _
  have hs : abelianDiagonal A ≫ snd A.toOver A.toOver = 𝟙 A.toOver := lift_snd _ _
  rw [hf, hs, Intrinsic.ChernPullbackLaws.nativeChernPullback_id] at hd
  exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernEmbeddingIndependence.lineBundleChernClass_pullback (X := Z) (Y := X) (abelianDiagonal A) B).trans hd

end

end OAI.RepresentationTheory.Theta.Geometric.DiagonalBiextensionChern
