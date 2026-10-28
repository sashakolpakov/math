import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedPositiveProduct

/-! # Positive Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveCup

noncomputable section

/-! Positive-degree cup products on the original crystalline groups
commute with finite restriction and genuine rational scalar extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

def integral (d : ℕ) (x : Fin (d+1) → Witt.Crystalline.integralCohomology p k X 1) :=
  GradedPositiveProduct.product
    (fun i j a b => CrystallineCup.Integral.cup p k X hprojective i j a b) d x

def rational (d : ℕ) (x : Fin (d+1) → Witt.Crystalline.rationalCohomology p k X 1) :=
  GradedPositiveProduct.product
    (fun i j a b => RationalCrystallineCup.cup p k X hprojective i j a b) d x

theorem restriction (n d : ℕ) (x : Fin (d+1) → Witt.Crystalline.integralCohomology p k X 1) :
    CrystallineCup.Integral.restriction p k X n (d+1) (integral p k X hprojective d x) =
      GradedPositiveProduct.product
        (fun i j a b => SmoothProperWittCup.cup p k X n i j a b) d
        (fun j => CrystallineCup.Integral.restriction p k X n 1 (x j)) :=
  GradedPositiveProduct.natural _ _
    (fun i => CrystallineCup.Integral.restriction p k X n i)
    (CrystallineCup.Integral.restriction_cup p k X hprojective n) d x

include p k X hprojective in
private abbrev scalar_cup (i j : ℕ) (x : Witt.Crystalline.integralCohomology p k X i)
    (y : Witt.Crystalline.integralCohomology p k X j) := by
  have h := RationalCrystallineCup.cup_tmul p k X hprojective i j
    (1 : FractionRing (WittVector p k)) 1 x y
  rw [one_mul] at h
  exact h.symm

include p k X hprojective in
abbrev rational_tmul (d : ℕ) (x : Fin (d+1) → Witt.Crystalline.integralCohomology p k X 1) :=
  (GradedPositiveProduct.natural
    (fun i j a b => CrystallineCup.Integral.cup p k X hprojective i j a b)
    (fun i j a b => BilinearScalarExtension.map (FractionRing (WittVector p k))
      (RationalCrystallineCup.integralCup p k X hprojective i j) a b)
    (fun _ x => (1 : FractionRing (WittVector p k)) ⊗ₜ[WittVector p k] x)
    (scalar_cup p k X hprojective) d x).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.PositiveCup
