import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyPairingAntisymmetry
import OAI.RepresentationTheory.Theta.Geometric.QuotientDifferenceFibers

/-! # Line Period Pairing -/

namespace OAI.RepresentationTheory.Theta.Geometric.LinePeriodPairing

noncomputable section

/-! The actual product line class pairs native rational periods.
Pullback is natural in both factors, and the genuine difference formula
recovers the original Chern form without a change of normalization. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

def linePeriodPairing (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.toOver ⊗ B.toOver).left) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A →ₗ[ℚ] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B →ₗ[ℚ] ℚ :=
  (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing A B q).compl₁₂
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B).toLinearMap

theorem linePeriodPairing_pullback (A B A' B' : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ A'.toOver) (g : B.toOver ⟶ B'.toOver) [IsMonHom f] [IsMonHom g]
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A'.toOver ⊗ B'.toOver).left)
    (x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) :
    linePeriodPairing A B (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ g).left q) x y =
      linePeriodPairing A' B' q (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g y) := by
  change AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing A B _ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B y) =
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing A' B' q (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A' (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f x))
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B' (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift g y))
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality f x, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods.nativeHomologyPeriods_naturality g y]
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality.nativeProductClassPairing_pullback A B A' B' f g q
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A x) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B y)

theorem linePeriodPairing_biextension (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A.toOver ⊗ A.toOver).left)
    (e : ((B.tensor (L.pullback (fst A.toOver A.toOver).left)).tensor
      (L.pullback (snd A.toOver A.toOver).left)).sheaf ≅
        (L.pullback (MonObj.mul (X := A.toOver)).left).sheaf) :
    linePeriodPairing A A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B) = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm A L := by
  change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionPeriodPairing.nativeBiextensionHomologyPairing A B).compl₁₂
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap = _
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionPeriodPairing.nativeBiextensionHomologyPairing_eq A L B e]
  exact (congrArg (fun c => c.compl₁₂
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyPairingAntisymmetry.alternatingClassPairing_eq_original A (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L))).symm

theorem linePeriodPairing_adjoint (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.toOver ⊗ B.toOver).left)
    (d : A.toOver ⟶ A.toOver) (f : B.toOver ⟶ B.toOver) [IsMonHom d] [IsMonHom f]
    (he : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 B.toOver).left q =
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.toOver ⊗ₘ f).left q)
    (x : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) (y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) :
    linePeriodPairing A B q (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift d x) y =
      linePeriodPairing A B q x (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f y) := by
  have hl := linePeriodPairing_pullback A B A B d (𝟙 B.toOver) q x y
  have hr := linePeriodPairing_pullback A B A B (𝟙 A.toOver) f q x y
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift_id] at hl hr
  exact hl.symm.trans ((congrArg (fun c => linePeriodPairing A B c x y) he).trans hr)

end

end OAI.RepresentationTheory.Theta.Geometric.LinePeriodPairing
