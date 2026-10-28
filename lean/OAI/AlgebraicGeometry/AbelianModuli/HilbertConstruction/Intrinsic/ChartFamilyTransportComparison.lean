import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.FamilyPullbackFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoTransportConjugation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackComposition

/-! # Chart Family Transport Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ChartFamilyTransportComparison

noncomputable section

/-! Native Hilbert-family pullback comparisons commute with the original
transport through an intersection of charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem nativeChartFamilyTransportComparison
    {S : Scheme.{u}} (X : Over S) {W A B Z T : Over S}
    {l : W ⟶ A} {r : W ⟶ B} {p : A ⟶ Z} {q : B ⟶ Z}
    (H : IsPullback l r p q) (F : HilbertScheme.Presentations.Hilbert.Functor.Family X A) (G : HilbertScheme.Presentations.Hilbert.Functor.Family X B)
    (e : FamilyTestPoints.nativeFamilyOver X W (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X l F) ≅
      FamilyTestPoints.nativeFamilyOver X W (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X r G))
    (a : T ⟶ A) (b : T ⟶ B) (h : a ≫ p = b ≫ q)
    (c : T ⟶ W) (hL : c ≫ l = a) (hR : c ≫ r = b)
    (FA FB : HilbertScheme.Presentations.Hilbert.Functor.Family X T)
    (hA : FA = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F)
    (hB : FB = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X b G)
    (hAL : FA = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X c (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X l F))
    (hBR : FB = HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X c (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X r G)) :
    (FamilyPullbackComposition.nativeFamilyEqIso X hA ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X a F) ≪≫
        StableHilbert.FamilyTransport.chartFamilyPullbackTransport H (FamilyTestPoints.nativeFamilyOver X A F) (FamilyTestPoints.nativeFamilyOver X B G)
          ((FamilyPullbackIso.nativeFamilyPullbackIso X l F).symm ≪≫ e ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X r G)
          a b h ≪≫
        (FamilyPullbackComposition.nativeFamilyEqIso X hB ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X b G).symm =
      FamilyPullbackComposition.nativeFamilyEqIso X hAL ≪≫
        FamilyPullbackPoints.nativeFamilyIsoPullback X c (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X l F)
          (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X r G) e ≪≫
        (FamilyPullbackComposition.nativeFamilyEqIso X hBR).symm := by
  let K := Over.pullback c.left
  let qL := FamilyPullbackIso.nativeFamilyPullbackIso X l F
  let qR := FamilyPullbackIso.nativeFamilyPullbackIso X r G
  let nL := FamilyPullbackIso.nativeFamilyPullbackIso X c (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X l F)
  let nR := FamilyPullbackIso.nativeFamilyPullbackIso X c (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X r G)
  let ea := FamilyPullbackComposition.nativeFamilyEqIso X hAL
  let eb := FamilyPullbackComposition.nativeFamilyEqIso X hBR
  let zL := (Over.pullbackComp c.left l.left).symm.app (FamilyTestPoints.nativeFamilyOver X A F) ≪≫
    eqToIso (congrArg
      (fun f : T.left ⟶ A.left => (Over.pullback f).obj (FamilyTestPoints.nativeFamilyOver X A F))
      (congrArg Over.Hom.left hL))
  let zR := (Over.pullbackComp c.left r.left).symm.app (FamilyTestPoints.nativeFamilyOver X B G) ≪≫
    eqToIso (congrArg
      (fun f : T.left ⟶ B.left => (Over.pullback f).obj (FamilyTestPoints.nativeFamilyOver X B G))
      (congrArg Over.Hom.left hR))
  exact IsoTransportConjugation.isoTransportConjugation K qL qR e nL nR ea eb zL zR
    (FamilyPullbackComposition.nativeFamilyEqIso X hA ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X a F)
    (FamilyPullbackComposition.nativeFamilyEqIso X hB ≪≫ FamilyPullbackIso.nativeFamilyPullbackIso X b G)
    (StableHilbert.FamilyTransport.chartFamilyPullbackTransport H (FamilyTestPoints.nativeFamilyOver X A F) (FamilyTestPoints.nativeFamilyOver X B G)
      (qL.symm ≪≫ e ≪≫ qR) a b h)
    (FamilyPullbackComposition.nativeFamilyPullbackIso_factor X l c a hL F FA hA hAL)
    (FamilyPullbackComposition.nativeFamilyPullbackIso_factor X r c b hR G FB hB hBR)
    (Chart.FamilyPullbackFactorization.chartFamilyPullbackTransport_factor H (FamilyTestPoints.nativeFamilyOver X A F)
      (FamilyTestPoints.nativeFamilyOver X B G) (qL.symm ≪≫ e ≪≫ qR) a b h c hL hR)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ChartFamilyTransportComparison
