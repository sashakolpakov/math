import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionPullback

/-! # Integral Pullback Criterion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPullbackCriterion.IntrinsicPadicIntegralPullbackCriterion

noncomputable section

/-! Geometric naturality of the actual completed comparison follows
from naturality of its original finite small-quotient coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p

variable (u : X ⟶ X) (v : Y ⟶ Y)

include hprojective in
theorem naturality
  (hfinite : ∀ (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1),
    CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback.pullback p Y v n
      ((D).map (SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel.iso p X Y f hp I n).hom
        (Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology 1)
          (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X n x))) =
    (D).map (SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel.iso p X Y f hp I n).hom
      (Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology 1)
        (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X n (DeRham.Int.pullback u 1 x))))
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral p v
      (IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective x) =
    IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective (DeRham.Int.pullback u 1 x) := by
  apply CrystallineRestrictionExt.IntrinsicPadicCrystallineRestrictionExt.ext p Y hprojective
  intro n
  exact (LinearMap.congr_fun (CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback.natural p Y v n)
    (IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective x)).symm.trans
      ((congrArg (CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback.pullback p Y v n)
        (SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel.restriction p X Y f hp I hprojective n x)).trans
          ((hfinite n x).trans (SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel.restriction p X Y f hp I hprojective n
            (DeRham.Int.pullback u 1 x)).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPullbackCriterion.IntrinsicPadicIntegralPullbackCriterion
