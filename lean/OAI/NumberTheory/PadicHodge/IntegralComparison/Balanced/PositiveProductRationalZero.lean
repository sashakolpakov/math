import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RationalTorsionUniform

/-! # Positive Product Rational Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveProductRationalZero.Torsion

noncomputable section

/-! If the original rational exterior cup is zero, finite generation
bounds the p-power torsion of all corresponding integral products uniformly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local irreducible] GradedExteriorCup.exteriorPowerCup

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (d : ℕ)

local notation "W" => WittVector p k
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupUnit.data p k X hprojective
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X

private theorem data_cup (i j : ℕ)
    (x : Witt.Crystalline.rationalCohomology p k X i)
    (y : Witt.Crystalline.rationalCohomology p k X j) :
    (D).cup i j x y = RationalCrystallineCup.cup p k X hprojective i j x y := by
  dsimp only [RationalCupUnit.data, ScalarGradedCupData.data]
  rfl

private theorem rational_product
    (v : Fin (d+1) → Witt.Crystalline.rationalCohomology p k X 1) :
    @GradedPositiveProduct.product (fun n => Witt.Crystalline.rationalCohomology p k X n)
      (fun i j x y => (D).cup i j x y) d v =
      PositiveCup.rational p k X hprojective d v := by
  unfold PositiveCup.rational
  apply congrArg (fun μ : ∀ i j, Witt.Crystalline.rationalCohomology p k X i →
      Witt.Crystalline.rationalCohomology p k X j →
      Witt.Crystalline.rationalCohomology p k X (i+j) =>
    GradedPositiveProduct.product μ d v)
  funext i j x y
  exact data_cup p k X hprojective i j x y

theorem rational_zero
    (hz : GradedExteriorCup.exteriorPowerCup D (d+1) = 0)
    (v : Fin (d+1) → Witt.Crystalline.rationalCohomology p k X 1) :
    PositiveCup.rational p k X hprojective d v = 0 := by
  rw [← rational_product p k X hprojective d v]
  by_contra hv
  exact (GradedPositiveProduct.exteriorPowerCup_ne_zero D d v hv) hz

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveProductRationalZero.Torsion
