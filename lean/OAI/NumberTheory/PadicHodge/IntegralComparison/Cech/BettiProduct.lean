import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.GlobalCechProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SmoothBettiProduct

/-! # Betti Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BettiProduct

noncomputable section

/-! Product compatibility from the native algebraic Čech total to
Betti cohomology, through actual smooth forms and integration. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {ι : Type} (U : ι → V.toOver.left.Opens)
  (hU : ⨆ i, U i = ⊤)

local instance integral : IsIntegral V.toOver.left := V.property
local instance smooth : Smooth V.toOver.hom := V.presentation.smooth
local instance proper : IsProper V.toOver.hom := V.presentation.projective.isProper

def smoothComparison (n : ℕ) :
    (AlgebraicSmoothCechProduct.smoothTotal V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U)).homology n ≃ₗ[ℂ]
        V.complexCohomology n :=
  (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.globalCohomologyIso V.toOver U hU n).symm.toLinearEquiv.trans
    (V.deRhamBettiIso n).toLinearEquiv

theorem smoothComparison_cup (p q : ℕ)
    (a : (AlgebraicSmoothCechProduct.smoothTotal V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U)).homology p)
    (b : (AlgebraicSmoothCechProduct.smoothTotal V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U)).homology q) :
    smoothComparison V U hU (p + q)
        (AlgebraicSmoothCohomologyProduct.Cech.cohomologyCup V.toOver
          (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U) p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) p q
        (smoothComparison V U hU p a) (smoothComparison V U hU q b) :=
  (congrArg (V.deRhamBettiIso (p + q)).hom
    (IntegralComparison.Smooth.GlobalCechProduct.Comparison.globalCohomologyIso_inv_cup V.toOver U hU p q a b)).trans
      (Global.SmoothBettiProduct.comparison_cup V p q _ _)

def algebraicComparison (n : ℕ) :
    (RationalDeRham.TotalCup.Cech.total ℂ V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U)).homology n →ₗ[ℂ]
        V.complexCohomology n :=
  (smoothComparison V U hU n).toLinearMap.comp
    (HomologicalComplex.homologyMap (AlgebraicSmoothCechProduct.totalMap V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U)) n).hom

theorem algebraicComparison_cup (p q : ℕ)
    (a : (RationalDeRham.TotalCup.Cech.total ℂ V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U)).homology p)
    (b : (RationalDeRham.TotalCup.Cech.total ℂ V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U)).homology q) :
    algebraicComparison V U hU (p + q)
        (RationalDeRham.CohomologyCup.Cech.cohomologyCup ℂ V.toOver
          (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U) p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) p q
        (algebraicComparison V U hU p a) (algebraicComparison V U hU q b) :=
  (congrArg (smoothComparison V U hU (p + q))
    (AlgebraicSmoothCohomologyProduct.Cech.totalMap_cohomologyCup V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver U) p q a b)).trans
        (smoothComparison_cup V U hU p q _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BettiProduct
