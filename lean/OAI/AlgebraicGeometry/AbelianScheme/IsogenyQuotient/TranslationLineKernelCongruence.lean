import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation

/-! # Translation Line Kernel Congruence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TranslationLineKernelCongruence.Construction

noncomputable section

/-! Infinitesimal translation depends only on the original line-bundle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation

attribute [local instance] Quotients.FiniteDescent.LineBundleDual.Construction.LineBundlePicard.instCommGroupIsoClass

theorem dualTranslationLineKernel_congr (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G]
    (L L' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle G.left) (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L')
    (t : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints G 1) :
    AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualTranslationLineKernel G L t = AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualTranslationLineKernel G L' t := by
  apply Subtype.ext
  calc
    _ = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left) /
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left) :=
      AbelianModuli.ReferenceFamily.DualLine.PullbackDifference.dualLinePullbackDifferenceKernel_class G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left
        (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G t) L
    _ = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L'.pullback (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left) /
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L'.pullback (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left) :=
      congrArg (fun z => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left z /
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left z) hL
    _ = _ := (AbelianModuli.ReferenceFamily.DualLine.PullbackDifference.dualLinePullbackDifferenceKernel_class G (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation G t).left
      (snd (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) G).left (AbelianModuli.ReferenceFamily.Intrinsic.InfinitesimalTranslation.dualInfinitesimalTranslation_equal_reduction G t) L').symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TranslationLineKernelCongruence.Construction
