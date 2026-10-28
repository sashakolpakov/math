import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogIntegralSheaf

/-! # Integral Sheaf Chern Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralSheafChernClass

noncomputable section

/-! The first Chern class of the original algebraic line bundle has
a constructed integral sheaf class. Its rationalization is exactly
the native singular first Chern class under the proved comparison,
with no multiplication or change of normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier)

def nativeIntegralSheafChernClass :
    CategoryTheory.Sheaf.H (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))) 2 :=
  DivisorClass.Chern.LogIntegralSheaf.logarithmicIntegralSheafClass
    (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (ChernClasses.nativeLineBundle X L).logCover
    (ChernClasses.nativeLineBundle X L).bundleLogCech (ChernClasses.nativeLineBundle X L).bundleLogCech_cocycle
    (by
      apply top_unique
      intro x _
      obtain ⟨i, hi⟩ := (ChernClasses.nativeLineBundle X L).logCover_covers x
      exact Opens.mem_iSup.mpr ⟨i, hi⟩)

theorem nativeIntegralSheafChernClass_rationalize
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)]
    [StronglyLocallyContractibleSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)]
    [LocallyPathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)] :
    CategoryTheory.Sheaf.H.map (DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalConstantSheaf
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))) 2 (nativeIntegralSheafChernClass X L) =
      DivisorClass.Chern.Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 1
        (ChernClasses.lineBundleChernClass X L) :=
  DivisorClass.Chern.LogIntegralSheaf.logarithmicIntegralSheafClass_rationalize
    (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) (ChernClasses.nativeLineBundle X L).logCover
    (ChernClasses.nativeLineBundle X L).bundleLogCech (ChernClasses.nativeLineBundle X L).bundleLogCech_cocycle
    (ChernClasses.nativeLineBundle X L).logCover_covers

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralSheafChernClass
