import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineLimit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechCoordinates

/-! # Integral Crystalline Equiv -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv

noncomputable section

/-! The completed crystalline comparison descends to a p-adic linear
equivalence whose source is original native integral de Rham H-one. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

variable
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def equiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 ≃ₗ[ℤ_[p]]
    (Coefficient.IntrinsicPadicCoefficientDescent.restrict p).obj (ModuleCat.of R
      (IntegralComparison.BigCrystallineCohomology.Cohomology (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 1)) :=
  (IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X).trans ((Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((C).homology 1)).trans
    (((Coefficient.IntrinsicPadicCoefficientDescent.restrict p).mapIso
      (IntegralCrystallineLimit.IntrinsicPadicIntegralCrystallineLimit.iso p X Y f hp I hprojective)).toLinearEquiv))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv
