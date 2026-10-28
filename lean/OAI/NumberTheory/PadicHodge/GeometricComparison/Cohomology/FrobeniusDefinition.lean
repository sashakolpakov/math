import OAI.NumberTheory.PadicHodge.GeometricComparison.CanonicalSmallFrobenius
import OAI.AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators
import OAI.NumberTheory.PadicHodge.GeometricComparison.DVR

/-! # Frobenius Definition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.FrobeniusDefinition.CrystallineAdapter

noncomputable section

/-! Cohomology's native Frobenius specializes to GeometricComparison's actual q-power small-site operator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem canonicalSmallFrobenius_eq_Cohomology {p : ℕ} [Fact p.Prime]
    (B : AlgebraicGeometry.Crystalline.Cohomology.Foundations.MixedCharacteristicDVR.{u} p)
    (X : Over (Spec (CommRingCat.of B.R))) [IsProper X.hom] (n : ℕ) :
    CanonicalSmallFrobenius.CrystallineAdapter.canonicalSmallFrobenius p B.k (B.specialFiber X) n =
      AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallineFrobenius B X n := rfl

theorem e62Frobenius_eq_native (q : ℕ) [Fact q.Prime]
    (X : Over (Spec (CommRingCat.of ℤ_[q]))) [IsProper X.hom]
    (x : AlgebraicGeometry.Crystalline.Cohomology.Foundations.rationalCrystalline (DVR.PadicBase.dvr q) X 1) :
    AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallineFrobenius (DVR.PadicBase.dvr q) X 1 x =
      SmallCrystallineOperators.CrystallineAdapter.smallFrobenius q ((DVR.PadicBase.dvr q).specialFiber X) x :=
  (DFunLike.congr_fun (canonicalSmallFrobenius_eq_Cohomology (DVR.PadicBase.dvr q) X 1).symm x).trans
    (CanonicalSmallFrobenius.CrystallineAdapter.canonicalSmallFrobenius_eq_native q ((DVR.PadicBase.dvr q).specialFiber X) x)

theorem smallFrobenius_bijective_congr (q : ℕ) [Fact q.Prime]
    {X Y : Over (Spec (CommRingCat.of (ZMod q)))} [IsSeparated X.hom] [IsSeparated Y.hom]
    (h : X = Y) : Function.Bijective (SmallCrystallineOperators.CrystallineAdapter.smallFrobenius q X) ↔ Function.Bijective (SmallCrystallineOperators.CrystallineAdapter.smallFrobenius q Y) := by
  subst Y
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.FrobeniusDefinition.CrystallineAdapter
