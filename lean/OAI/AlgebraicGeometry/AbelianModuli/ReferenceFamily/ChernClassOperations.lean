import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernTensorAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernEmbeddingIndependence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing

/-! # Chern Class Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernClassOperations

noncomputable section

/-! Additivity and functoriality of the genuine Chern class on line-bundle
isomorphism classes, and additivity of its native period pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lineBundleClassChernClass_tensor (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (a b : HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.carrier) :
    Intrinsic.ChernClasses.lineBundleClassChernClass X (HilbertConstruction.Line.Bundles.LineBundle.tensorClass a b) =
      Intrinsic.ChernClasses.lineBundleClassChernClass X a + Intrinsic.ChernClasses.lineBundleClassChernClass X b := by
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M => exact ChernTensorAdditivity.lineBundleChernClass_tensor X L M

theorem lineBundleClassChernClass_pullback {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : Y.toOver ⟶ X.toOver) (a : HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.carrier) :
    Intrinsic.ChernClasses.lineBundleClassChernClass Y (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left a) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 2 (Intrinsic.ChernClasses.lineBundleClassChernClass X a) := by
  induction a using Quotient.inductionOn with
  | h L => exact ChernEmbeddingIndependence.lineBundleChernClass_pullback f L

theorem lineBundleChernClass_trivial (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    Intrinsic.ChernClasses.lineBundleChernClass X (HilbertConstruction.Line.Bundles.LineBundle.trivial X.carrier) = 0 := by
  let L := HilbertConstruction.Line.Bundles.LineBundle.trivial X.carrier
  have h := ChernTensorAdditivity.lineBundleChernClass_tensor X L L
  have hi := Intrinsic.ChernClasses.lineBundleChernClass_iso X (L.tensor L) L (HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso L.sheaf)
  rw [hi] at h
  exact (add_left_cancel (a := Intrinsic.ChernClasses.lineBundleChernClass X L) ((add_zero _).trans h)).symm

theorem homologyClassPairing_add (X : TopCat.{0}) (m : TopCat.of (X × X) ⟶ X)
    (c d : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    HomologyCrossPairing.homologyClassPairing X m (c + d) = HomologyCrossPairing.homologyClassPairing X m c + HomologyCrossPairing.homologyClassPairing X m d := by
  ext x y
  change AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X 2 (c + d) _ =
    AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X 2 c _ + AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X 2 d _
  rw [map_add, LinearMap.add_apply]

theorem alternatingClassPairing_add (X : TopCat.{0}) (m : TopCat.of (X × X) ⟶ X)
    (c d : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X 2) :
    HomologyCrossPairing.alternatingClassPairing X m (c + d) = HomologyCrossPairing.alternatingClassPairing X m c + HomologyCrossPairing.alternatingClassPairing X m d := by
  unfold HomologyCrossPairing.alternatingClassPairing
  rw [homologyClassPairing_add]
  ext x y
  change (1 / 2 : ℚ) * ((HomologyCrossPairing.homologyClassPairing X m c x y + HomologyCrossPairing.homologyClassPairing X m d x y) -
    (HomologyCrossPairing.homologyClassPairing X m c y x + HomologyCrossPairing.homologyClassPairing X m d y x)) = _
  change _ = (1 / 2 : ℚ) * (HomologyCrossPairing.homologyClassPairing X m c x y - HomologyCrossPairing.homologyClassPairing X m c y x) +
    (1 / 2 : ℚ) * (HomologyCrossPairing.homologyClassPairing X m d x y - HomologyCrossPairing.homologyClassPairing X m d y x)
  ring

theorem nativeChernForm_tensor (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L M : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) :
    Intrinsic.ChernPairing.nativeChernForm A (L.tensor M) = Intrinsic.ChernPairing.nativeChernForm A L + Intrinsic.ChernPairing.nativeChernForm A M := by
  have h := (congrArg (HomologyCrossPairing.alternatingClassPairing (Betti.Scheme.schemePointSpace A.toOver) (Intrinsic.ChernPairing.nativeMultiplication A))
    (ChernTensorAdditivity.lineBundleChernClass_tensor A.variety.presentation L M)).trans
      (alternatingClassPairing_add (Betti.Scheme.schemePointSpace A.toOver) (Intrinsic.ChernPairing.nativeMultiplication A)
        (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation L) (Intrinsic.ChernClasses.lineBundleChernClass A.variety.presentation M))
  exact congrArg (fun b => b.compl₁₂ (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap
    (Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A).toLinearMap) h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernClassOperations
