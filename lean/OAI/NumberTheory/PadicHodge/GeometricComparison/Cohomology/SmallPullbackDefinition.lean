import OAI.NumberTheory.PadicHodge.GeometricComparison.CanonicalSmallPullback
import OAI.AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators

/-! # Small Pullback Definition -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.SmallPullbackDefinition.CrystallineAdapter

noncomputable section

/-! The repaired Cohomology ordinary pullback has the specified canonical small-site normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem canonicalSmallPullback_eq_Cohomology {p : ℕ} [Fact p.Prime]
    (B : AlgebraicGeometry.Crystalline.Cohomology.Foundations.MixedCharacteristicDVR.{u} p)
    {X Y : Over (Spec (CommRingCat.of B.R))} [IsProper X.hom] [IsProper Y.hom]
    (f : X ⟶ Y) (n : ℕ) :
    CanonicalSmallPullback.CrystallineAdapter.canonicalSmallPullback p B.k (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.specialFiberMap B f) n =
      AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallinePullback B f n := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.SmallPullbackDefinition.CrystallineAdapter
