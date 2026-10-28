import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FiniteReduction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPullbackCriterion

/-! # Integral Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralNaturality.IntrinsicPadicIntegralGeometricNaturality

noncomputable section

/-! The actual completed integral crystalline comparison commutes
with every compatible geometric endomorphism. -/

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

variable (u : X ⟶ X) (v : Y ⟶ Y) (hsquare : f ≫ u.left = v.left ≫ f)

include hsquare in
theorem naturality (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral p v
      (IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective x) =
    IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective (DeRham.Int.pullback u 1 x) :=
  IntegralPullbackCriterion.IntrinsicPadicIntegralPullbackCriterion.naturality p X Y f hp I hprojective u v
    (fun n y => FiniteReduction.IntrinsicPadicGeometricFiniteReduction.naturality p u v f f hp hp hsquare n I I y) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralNaturality.IntrinsicPadicIntegralGeometricNaturality
