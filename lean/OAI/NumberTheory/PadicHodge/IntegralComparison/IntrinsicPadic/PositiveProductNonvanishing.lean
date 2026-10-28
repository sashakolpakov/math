import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReductionCupCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.UniformTopProduct

/-! # Positive Product Nonvanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PositiveProductNonvanishing.Intrinsic

noncomputable section

/-! A nonzero rational ordinary top product forces the original balanced
rational crystalline exterior cup to be nonzero. Uniform integral lifting
at every finite level supplies the comparison, with no choice of product
or cohomology groups substituted for the original ones. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hprojective : Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

abbrev ordinary (i : ℕ) := UniformTopProduct.Intrinsic.ordinary p X i

abbrev ordinaryCup (i j : ℕ) (x : ordinary p X i) (y : ordinary p X j) :=
  UniformTopProduct.Intrinsic.ordinaryCup p X i j x y

include hp in
theorem exteriorPowerCup_ne_zero (d : ℕ) (v : Fin (d+1) → ordinary p X 1)
    (hv : (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] GradedPositiveProduct.product (ordinaryCup p X) d v ≠ 0) :
    GradedExteriorCup.exteriorPowerCup
      (Balanced.RationalCupUnit.data p (ZMod p) Y hprojective) (d+1) ≠ 0 :=
  UniformTopProduct.Intrinsic.exteriorPowerCup_ne_zero p X Y f hp hprojective
    (ReductionCupCoordinates.Intrinsic.cup p X Y f hp)
    (ProductProperties.IntrinsicComparison.reductionComparison_eq_zero p X Y f hp)
    d v hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.PositiveProductNonvanishing.Intrinsic
