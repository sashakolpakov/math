import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductCohomology

/-! # Biextension Period Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionPeriodPairing

noncomputable section

/-! The actual Poincare biextension determines the native Chern period
form. This proves independence from the line-bundle witness whenever
the two genuine tensor identities induce the same biextension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

def nativeBiextensionHomologyPairing (B : HilbertConstruction.Line.Bundles.LineBundle (A.toOver ⊗ A.toOver).left) :
    HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.toOver) →ₗ[ℚ] HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.toOver) →ₗ[ℚ] ℚ :=
  CrossClassEvaluation.crossClassPairing (Betti.Scheme.schemePointSpace A.toOver) (Betti.Scheme.schemePointSpace A.toOver)
    (Intrinsic.ProductCohomology.nativeProductCohomologyPullback A A
      (Intrinsic.ChernClasses.lineBundleChernClass (Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation A.variety.presentation) B))

theorem nativeBiextensionHomologyPairing_eq
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (B : HilbertConstruction.Line.Bundles.LineBundle (A.toOver ⊗ A.toOver).left)
    (e : ((B.tensor (L.pullback (fst A.toOver A.toOver).left)).tensor
      (L.pullback (snd A.toOver A.toOver).left)).sheaf ≅ (L.pullback (MonObj.mul (X := A.toOver)).left).sheaf) :
    nativeBiextensionHomologyPairing A B =
      HomologyCrossPairing.homologyClassPairing (Betti.Scheme.schemePointSpace A.toOver) (Intrinsic.ChernPairing.nativeMultiplication A)
        (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L) := by
  let c := Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L
  have h := congrArg (Intrinsic.ProductCohomology.nativeProductCohomologyPullback A A)
    (BiextensionChernIdentity.lineBundleChernClass_biextension A L B e)
  rw [map_sub, map_sub, Intrinsic.ProductCohomology.nativeProductCohomologyPullback_mul A c,
    Intrinsic.ProductCohomology.nativeProductCohomologyPullback_fst A A c, Intrinsic.ProductCohomology.nativeProductCohomologyPullback_snd A A c] at h
  exact (congrArg (CrossClassEvaluation.crossClassPairing (Betti.Scheme.schemePointSpace A.toOver) (Betti.Scheme.schemePointSpace A.toOver)) h).trans
    (CrossClassEvaluation.crossClassPairing_multiplication_difference (Betti.Scheme.schemePointSpace A.toOver) (Intrinsic.ChernPairing.nativeMultiplication A) c)

theorem nativeChernForm_eq_of_biextension
    (L M : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (B : HilbertConstruction.Line.Bundles.LineBundle (A.toOver ⊗ A.toOver).left)
    (eL : ((B.tensor (L.pullback (fst A.toOver A.toOver).left)).tensor
      (L.pullback (snd A.toOver A.toOver).left)).sheaf ≅ (L.pullback (MonObj.mul (X := A.toOver)).left).sheaf)
    (eM : ((B.tensor (M.pullback (fst A.toOver A.toOver).left)).tensor
      (M.pullback (snd A.toOver A.toOver).left)).sheaf ≅ (M.pullback (MonObj.mul (X := A.toOver)).left).sheaf) :
    Intrinsic.ChernPairing.nativeChernForm A L = Intrinsic.ChernPairing.nativeChernForm A M := by
  have h := (nativeBiextensionHomologyPairing_eq A L B eL).symm.trans
    (nativeBiextensionHomologyPairing_eq A M B eM)
  exact congrArg (fun b => ((1 / 2 : ℚ) • (b - b.flip)).compl₁₂
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap) h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionPeriodPairing
