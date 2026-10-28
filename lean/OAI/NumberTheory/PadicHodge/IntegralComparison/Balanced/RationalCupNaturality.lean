import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CrystallineCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension

/-! # Rational Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupNaturality

noncomputable section

/-! Actual geometric pullback preserves the native rational crystalline
cup, by scalar extension of the proved integral identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y)

local notation "W" => WittVector p k
local notation "K" => FractionRing (WittVector p k)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CrystallineCupNaturality (integralPullback pullback integralPullback_apply pullback_tmul)

variable (hX : Projectivity.Construction.ProjectiveOver k X.hom) (hY : Projectivity.Construction.ProjectiveOver k Y.hom)

private theorem integralCup_apply
    (Z : Over (Spec (CommRingCat.of k))) [IsProper Z.hom] [Smooth Z.hom]
    (hZ : Projectivity.Construction.ProjectiveOver k Z.hom) (i j : ℕ)
    (x : Witt.Crystalline.integralCohomology p k Z i) (y : Witt.Crystalline.integralCohomology p k Z j) :
    RationalCrystallineCup.integralCup p k Z hZ i j x y =
      CrystallineCup.Integral.cup p k Z hZ i j x y := rfl

theorem integral_cup_natural (i j : ℕ) (x : Witt.Crystalline.integralCohomology p k Y i) (y : Witt.Crystalline.integralCohomology p k Y j) :
    Rational.CrystallineCupNaturality.integralPullback p k X Y g (i + j) (RationalCrystallineCup.integralCup p k Y hY i j x y) =
      RationalCrystallineCup.integralCup p k X hX i j
        (Rational.CrystallineCupNaturality.integralPullback p k X Y g i x) (Rational.CrystallineCupNaturality.integralPullback p k X Y g j y) := by
  rw [integralCup_apply, integralCup_apply, Rational.CrystallineCupNaturality.integralPullback_apply,
    Rational.CrystallineCupNaturality.integralPullback_apply, Rational.CrystallineCupNaturality.integralPullback_apply]
  exact CupNaturality.Integral.cup_natural p k X Y g hX hY i j x y

include p k X Y g hX hY in
abbrev cup_natural (i j : ℕ) (x : K ⊗[W] Witt.Crystalline.integralCohomology p k Y i)
    (y : K ⊗[W] Witt.Crystalline.integralCohomology p k Y j) :=
  BilinearScalarExtension.map_natural K
    (RationalCrystallineCup.integralCup p k Y hY i j)
    (RationalCrystallineCup.integralCup p k X hX i j)
    (Rational.CrystallineCupNaturality.integralPullback p k X Y g i) (Rational.CrystallineCupNaturality.integralPullback p k X Y g j)
    (Rational.CrystallineCupNaturality.integralPullback p k X Y g (i + j))
    (integral_cup_natural p k X Y g hX hY i j) x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupNaturality
