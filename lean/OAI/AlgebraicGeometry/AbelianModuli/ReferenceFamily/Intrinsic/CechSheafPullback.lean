import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.TopResolutionPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LiteralCechPullbackClasses

/-! # Cech Sheaf Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechSheafPullback

noncomputable section

/-! The original Čech-to-native-sheaf comparison commutes with the
exact-adjunction pullback, without any acyclicity hypothesis on the cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {I : Type} (U : I → Opens Y)
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤) (n : ℕ)

theorem nativeCechToSheaf_pullback
    (x : ((CategoryTheory.cechComplexFunctor U).obj F.obj).homology (n + 1)) :
    Abelian.CoefficientPullback.abelianCoefficientCohomologyPullback f a (n + 1) (DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf U F hU n x) =
      DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf (fun i => (Opens.map f).obj (U i)) G hV n
        (HomologicalComplex.homologyMap (Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a.hom) (n + 1) x) := by
  let V := fun i => (Opens.map f).obj (U i)
  let p := HomologicalComplex.homologyMap (Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a.hom) (n + 1)
  have hF := ConcreteCategory.congr_hom (CechResolutionFactorization.nativeCechToTopResolution_toSheaf U F hU n) x
  have hG := ConcreteCategory.congr_hom (CechResolutionFactorization.nativeCechToTopResolution_toSheaf V G hV n) (p x)
  have hC := ConcreteCategory.congr_hom (Cech.TopResolutionPullback.nativeCechToTopResolution_pullback f U a hU hV n) x
  have hR := SectionComparisonPullback.nativeTopResolutionCohomologyMap_pullback f a n (CechResolutionFactorization.nativeCechToTopResolution U F hU n x)
  exact (congrArg (Abelian.CoefficientPullback.abelianCoefficientCohomologyPullback f a (n + 1)) hF.symm).trans
    (hR.trans ((congrArg (SectionComparisonPullback.nativeTopResolutionCohomologyMap G n) hC.symm).trans hG))

theorem nativeCechSheafClass_pullback (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0) :
    Abelian.CoefficientPullback.abelianCoefficientCohomologyPullback f a (n + 1) (DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U F hU n k hk) =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (fun i => (Opens.map f).obj (U i)) G hV n
        (LiteralCechPullback.literalCechPullback f U F.obj G.obj a.hom (n + 1) k)
        (LiteralCechPullback.literalCechPullback_closed f U F.obj G.obj a.hom (n + 1) k hk) := by
  have h := nativeCechToSheaf_pullback f U a hU hV n (DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F.obj n k hk)
  exact h.trans (congrArg (DivisorClass.Chern.Abelian.CechComparison.abelianCechToSheaf (fun i => (Opens.map f).obj (U i)) G hV n)
    (LiteralCechPullbackClasses.literalCechPullback_nativeClass f U F G a.hom n k hk))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechSheafPullback
