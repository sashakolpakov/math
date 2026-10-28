import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticPointTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius

/-! # Special Detection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SpecialDetection.CM

noncomputable section

/-! IntegralModel generation and CMPoints density give faithful detection by the
actual prime-field ordinary Albanese differences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

def ordinaryPointIso :=
  ArithmeticPointTransport.CM.pointsIso q (M.components a).A R.specialBase R.geometricBase
    (Frobenius.CM.geometricBase_factor R)

theorem ordinaryImage_transport (x : Detection.CM.ordinaryPoints R a) :
    ordinaryPointIso R a (Detection.CM.ordinaryAlbanesePoint R a x) = SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x :=
  ArithmeticPointTransport.CM.component_point q (M.components a).A R.specialBase R.geometricBase
    (Frobenius.CM.geometricBase_factor R) x.1 ((M.components a).a x.1) x.2.val

variable (hS : ∀ i, Smooth ((M.components a).S i).hom)
  (hA : ∀ i, AlbaneseProduct.CM.GoodGroupGeometry ((M.components a).A i).X)
  (hgenerate : ∀ i, ∃ n : ℕ, 0 < n ∧
    ∀ t : PELModuli.IntegralModel.Base.GeometricPoint M.arithmetic.base,
      Function.Surjective ((M.components a).sumOfDifferences i n t))
  (ho : IsOpen (R.ordinaryLocus a))
  (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})

include hS hA hgenerate ho hd in
theorem integral_detection (f : AbelianScheme.TateComparison.End.IntegralEnd (Frobenius.CM.specialAlbanese R a).X)
    (h : ∀ x y : Detection.CM.ordinaryPoints R a, x.1 = y.1 →
      PointSpecializationFormula.CM.Points.evaluateAt (Frobenius.CM.specialAlbanese R a) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) f
        (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x - SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a y) = 0) : f = 0 :=
  ArithmeticPointTransport.CM.detection_transfer q (M.components a).A R.specialBase R.geometricBase
    (Frobenius.CM.geometricBase_factor R) (fun x : Detection.CM.ordinaryPoints R a => x.1)
    (Detection.CM.ordinaryAlbanesePoint R a) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a) (ordinaryImage_transport R a)
    (fun g hg => Detection.CM.detection_from_IntegralModel_CMPoints R a hS hA hgenerate ho hd g hg) f h

include hS hA hgenerate ho hd in
theorem algebraic_detection (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (Frobenius.CM.specialAlbanese R a).X)
    (h : ∀ x y : Detection.CM.ordinaryPoints R a, x.1 = y.1 →
      PointEvaluation.CM.action (Frobenius.CM.specialAlbanese R a) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q) f
        (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x - SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a y) = 0) : f = 0 := by
  apply (EndomorphismComparison.CM.integralEquiv (Frobenius.CM.specialAlbanese R a).X).symm.injective
  rw [map_zero]
  exact integral_detection R a hS hA hgenerate ho hd
    ((EndomorphismComparison.CM.integralEquiv (Frobenius.CM.specialAlbanese R a).X).symm f) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.SpecialDetection.CM
