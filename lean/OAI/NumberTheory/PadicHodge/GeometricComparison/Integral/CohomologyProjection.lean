import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.DerivedMapSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.FunctorialInteger
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeRhamOneCech

/-! # Cohomology Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.CohomologyProjection.IntegralHOneProjectionNaturality

noncomputable section

/-! The original degree-one de Rham projection to its first three terms is
natural for actual geometric pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)

def integerMap := FirstThree.FunctorialInteger.FirstThreeFunctorialInteger.firstThreeMap (DeRham.Int.inverseImage f) (DeRham.Int.sheafPullback f)

theorem naturality (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology R Y 1) :
    Intrinsic.ResolvedPullback.IntrinsicResolvedPullback.derivedMap f (integerMap f) 1 (DeRhamOneCech.IntegralDeRhamHOneCech.projection R Y x) =
      DeRhamOneCech.IntegralDeRhamHOneCech.projection R X (DeRham.Int.pullback f 1 x) := by
  have h := Intrinsic.DerivedMapSquare.IntrinsicResolvedPullback.derivedMap_square f
    (HomologicalComplex.extendMap (FirstThree.ThreeComplex.FirstThreeComplex.projection (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y))
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (FirstThree.ThreeComplex.FirstThreeComplex.projection (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))
      ComplexShape.embeddingUpNat)
    (FirstThree.FunctorialInteger.FirstThreeFunctorialInteger.map (DeRham.Int.inverseImage f) (DeRham.Int.sheafPullback f))
    (integerMap f)
    (FirstThree.FunctorialInteger.FirstThreeFunctorialInteger.projection_square (DeRham.Int.inverseImage f) (DeRham.Int.sheafPullback f)) 1 x
  change _ = DeRhamOneCech.IntegralDeRhamHOneCech.projection R X
    (Intrinsic.ResolvedPullback.IntrinsicResolvedPullback.derivedMap f (DeRham.Int.sheafPullbackInt f) 1 x) at h
  exact h.trans (congrArg (DeRhamOneCech.IntegralDeRhamHOneCech.projection R X)
    (Intrinsic.ResolvedDeRham.IntrinsicResolvedPullback.derivedMap_deRham f 1 x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.CohomologyProjection.IntegralHOneProjectionNaturality
