import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveProductRationalZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.RationalTorsionUniform

/-! # Positive Product Torsion -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveProductTorsion

noncomputable section

/-! If the original rational exterior cup is zero, finite generation
bounds the p-power torsion of all corresponding integral products uniformly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

attribute [local irreducible] GradedExteriorCup.exteriorPowerCup
attribute [local irreducible] Abelian.Ext Abelian.Ext.homEquiv

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (d : ℕ)

local notation "W" => WittVector p k
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupUnit.data p k X hprojective
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X

include p k X hprojective d in
private abbrev tensor_zero
    (hz : GradedExteriorCup.exteriorPowerCup D (d+1) = 0)
    (v : Fin (d+1) → H 1) :=
  (PositiveCup.rational_tmul p k X hprojective d v).symm.trans
    (PositiveProductRationalZero.Torsion.rational_zero p k X hprojective d hz
      (fun i => (1 : FractionRing W) ⊗ₜ[W] v i))

include hprojective in
theorem uniform
    (hz : GradedExteriorCup.exteriorPowerCup D (d+1) = 0) :
    ∃ b : ℕ, ∀ v : Fin (d+1) → H 1,
      p^b • PositiveCup.integral p k X hprojective d v = 0 := by
  let : Module.Finite W (H (d+1)) :=
    SmoothProper.CrystallineFiniteness.integral p k X hprojective (d+1)
  apply Witt.RationalTorsionUniform.exists_power p k
    (fun v : Fin (d+1) → H 1 => PositiveCup.integral p k X hprojective d v)
  exact tensor_zero p k X hprojective d hz

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveProductTorsion
