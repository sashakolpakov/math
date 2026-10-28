import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineEquiv
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates

/-! # Integral Crystalline Rational -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineRational.IntrinsicPadicIntegralCrystallineRational

noncomputable section

/-! Rationalization of the constructed integral comparison lands in
the original GeometricComparison big crystalline vector space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

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

def integralEquiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 ≃ₗ[ℤ_[p]]
    CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates.integral p Y :=
  IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective

def equiv : ℚ_[p] ⊗[ℤ_[p]] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 ≃ₗ[ℚ_[p]] Crystalline.CoefficientAdapter.RationalH1 p Y :=
  ((integralEquiv p X Y f hp I hprojective).baseChange ℤ_[p] ℚ_[p] _ _).trans
    (CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates.rationalEquiv p Y)

theorem equiv_apply (x : ℚ_[p] ⊗[ℤ_[p]] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    equiv p X Y f hp I hprojective x = CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates.rationalEquiv p Y
      (((integralEquiv p X Y f hp I hprojective).baseChange ℤ_[p] ℚ_[p] _ _) x) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineRational.IntrinsicPadicIntegralCrystallineRational
