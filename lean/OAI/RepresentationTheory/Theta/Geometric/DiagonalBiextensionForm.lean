import OAI.RepresentationTheory.Theta.Geometric.DiagonalBiextensionChern
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicChernPairing

/-! # Diagonal Biextension Form -/

namespace OAI.RepresentationTheory.Theta.Geometric.DiagonalBiextensionForm

noncomputable section

/-! The actual diagonal biextension has twice the original native
Chern form of its polarization witness. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem diagonalBiextension_chernForm (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.toOver ⊗ A.toOver).left)
    (e : ((B.tensor (L.pullback (fst A.toOver A.toOver).left)).tensor
      (L.pullback (snd A.toOver A.toOver).left)).sheaf ≅
        (L.pullback (MonObj.mul (X := A.toOver)).left).sheaf)
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A (B.pullback (DiagonalBiextensionChern.abelianDiagonal A).left) v w = 2 * AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L v w := by
  let c := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L
  let b := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation (B.pullback (DiagonalBiextensionChern.abelianDiagonal A).left)
  let d := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation (L.pullback ((𝟙 A.toOver) ^ 2).left)
  have hd : d = AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity.nativeChernPullback ((𝟙 A.toOver) ^ 2) c :=
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernEmbeddingIndependence.lineBundleChernClass_pullback ((𝟙 A.toOver) ^ 2) L
  have hb : b = d - c - c := (DiagonalBiextensionChern.diagonalBiextension_chern A L B e).trans (by rw [hd])
  have hs : b + c + c = d := by rw [hb]; abel
  have h := congrArg (fun t => AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.alternatingClassPairing (AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeMultiplication A) t
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A w)) hs
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernClassOperations.alternatingClassPairing_add, AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernClassOperations.alternatingClassPairing_add] at h
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A (B.pullback (DiagonalBiextensionChern.abelianDiagonal A).left) v w + AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L v w +
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L v w = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A (L.pullback ((𝟙 A.toOver) ^ 2).left) v w at h
  rw [AlgebraicChernPairing.nativeChernForm_multiplication] at h
  norm_num at h
  linarith

end

end OAI.RepresentationTheory.Theta.Geometric.DiagonalBiextensionForm
