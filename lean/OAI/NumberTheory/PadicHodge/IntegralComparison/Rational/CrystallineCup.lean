import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CrystallineCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Crystalline Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CrystallineCup

noncomputable section

/-! Rational cup on the original fraction-field crystalline cohomology,
obtained by scalar extension of the native integral Ext product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "W" => WittVector p k
local notation "K" => FractionRing (WittVector p k)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

/-- Restrict the already constructed integral product to the actual Witt action. -/
def integralCup (i j : ℕ) : Witt.Crystalline.integralCohomology p k X i →ₗ[W]
    Witt.Crystalline.integralCohomology p k X j →ₗ[W] Witt.Crystalline.integralCohomology p k X (i + j) :=
  BilinearRestriction.map R W (ULift.ringEquiv : R ≃+* W).symm.toRingHom
    (Witt.Crystalline.integralCohomology p k X i) (Witt.Crystalline.integralCohomology p k X j) (Witt.Crystalline.integralCohomology p k X (i + j))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (Integral.CrystallineCup.cup p k X hprojective i j)

theorem integralCup_apply (i j : ℕ) (x : Witt.Crystalline.integralCohomology p k X i)
    (y : Witt.Crystalline.integralCohomology p k X j) : integralCup p k X hprojective i j x y =
      Integral.CrystallineCup.cup p k X hprojective i j x y :=
  BilinearRestriction.map_apply R W (ULift.ringEquiv : R ≃+* W).symm.toRingHom
    (Witt.Crystalline.integralCohomology p k X i) (Witt.Crystalline.integralCohomology p k X j) (Witt.Crystalline.integralCohomology p k X (i + j))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (Integral.CrystallineCup.cup p k X hprojective i j) x y

/-- Bilinear cup on the exact original rational crystalline groups. -/
def cup (i j : ℕ) : Witt.Crystalline.rationalCohomology p k X i →ₗ[K]
    Witt.Crystalline.rationalCohomology p k X j →ₗ[K] Witt.Crystalline.rationalCohomology p k X (i + j) :=
  TensorProduct.curry (((TensorProduct.lift (integralCup p k X hprojective i j)).baseChange K).comp
    (TensorProduct.AlgebraTensorModule.distribBaseChange W K
      (Witt.Crystalline.integralCohomology p k X i) (Witt.Crystalline.integralCohomology p k X j)).symm.toLinearMap)

theorem cup_tmul (i j : ℕ) (a b : K) (x : Witt.Crystalline.integralCohomology p k X i) (y : Witt.Crystalline.integralCohomology p k X j) :
    cup p k X hprojective i j (a ⊗ₜ[W] x) (b ⊗ₜ[W] y) =
      (a * b) ⊗ₜ[W] Integral.CrystallineCup.cup p k X hprojective i j x y := by
  change (TensorProduct.lift (integralCup p k X hprojective i j)).baseChange K
    ((TensorProduct.AlgebraTensorModule.distribBaseChange W K
      (Witt.Crystalline.integralCohomology p k X i) (Witt.Crystalline.integralCohomology p k X j)).symm
        ((a ⊗ₜ[W] x) ⊗ₜ[K] (b ⊗ₜ[W] y))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    TensorProduct.lift.tmul]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CrystallineCup
