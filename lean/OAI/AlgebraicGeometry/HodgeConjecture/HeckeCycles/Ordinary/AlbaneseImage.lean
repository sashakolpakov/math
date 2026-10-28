import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TotalAlbaneseMap
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius

/-! # Albanese Image -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.AlbaneseImage.CM

noncomputable section

/-! The actual total Albanese image of a full-source ordinary point is
the component Albanese image used in the detection theorem. The identity
follows from the original component inclusion and natural base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.PointFrobenius.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

def sourcePoint (x : Intrinsic.Detection.CM.ordinaryPoints R a) : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ R.specialFiber a :=
  ReductionPoints.CM.primeFieldPoint R a (x.2.val ≫ Locus.CM.componentFiberInclusion R a x.1)

theorem image_eq (x : Intrinsic.Detection.CM.ordinaryPoints R a) :
    Additive.ofMul (sourcePoint R a x ≫ (Over.pullback R.specialBase).map
      (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a))) = SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x := by
  apply Additive.toMul.injective
  have hp : sourcePoint R a x = Intrinsic.PointFrobenius.CM.pointsEquiv R ((M.components a).S x.1) x.2.val ≫
      (Over.pullback R.specialBase).map (Locus.CM.componentInclusion (M.components a) (M.decomposition a) x.1) :=
    (Intrinsic.PointFrobenius.CM.pointsEquiv_eq_primeFieldPoint R a (x.2.val ≫ Locus.CM.componentFiberInclusion R a x.1)).symm.trans
      (Intrinsic.PointFrobenius.CM.pointsEquiv_map R (Locus.CM.componentInclusion (M.components a) (M.decomposition a) x.1) x.2.val)
  have hc := congrArg (Over.pullback R.specialBase).map
    (TotalAlbaneseMap.CM.component (M.components a) (M.decomposition a) x.1)
  change sourcePoint R a x ≫ _ = _
  exact (congrArg (· ≫ (Over.pullback R.specialBase).map
      (TotalAlbaneseMap.CM.map (M.components a) (M.decomposition a))) hp).trans
    ((Category.assoc _ _ _).trans
      (congrArg (Intrinsic.PointFrobenius.CM.pointsEquiv R ((M.components a).S x.1) x.2.val ≫ ·)
        (((Over.pullback R.specialBase).map_comp _ _).symm.trans hc)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.AlbaneseImage.CM
