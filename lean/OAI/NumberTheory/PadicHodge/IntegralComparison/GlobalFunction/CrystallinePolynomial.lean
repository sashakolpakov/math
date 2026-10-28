import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineEquivalence
import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallineFrobenius
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-! # Crystalline Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallinePolynomial

noncomputable section

/-! The original degree-zero crystalline Frobenius polynomial is the polynomial of the actual global-function Witt Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

attribute [local instance] PeriodInvariants.WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom] [Nonempty X.left]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (a : ℕ) (hcard : Fintype.card k = p ^ a)

local notation "W" => WittVector p k
local notation "K" => FractionRing (WittVector p k)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.GlobalFunctionAlgebra.algebra k X

theorem rational (z : TensorProduct W K (WittVector p A)) :
    Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0
      (CrystallineEquivalence.rationalEquiv p k X hprojective z) =
        CrystallineEquivalence.rationalEquiv p k X hprojective
          ((WittFrobenius.witt p k X).toLinearMap.baseChange K z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c w =>
    change c ⊗ₜ[W] Global.CrystallineFrobenius.integralFrobenius p k X a hcard 0
        (SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective w) =
      c ⊗ₜ[W] SmoothProper.GlobalFunctionConstants.integralMap p k X hprojective
        (WittFrobenius.witt p k X w)
    exact congrArg (fun x => c ⊗ₜ[W] x) (CrystallineFrobenius.integral p k X hprojective a hcard w)
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conjugate :
    (CrystallineEquivalence.rationalEquiv p k X hprojective).symm.conj
      (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0) =
        (WittFrobenius.witt p k X).toLinearMap.baseChange K := by
  let e := CrystallineEquivalence.rationalEquiv p k X hprojective
  apply LinearMap.ext
  intro z
  apply e.injective
  change e (e.symm (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0 (e z))) =
    e ((WittFrobenius.witt p k X).toLinearMap.baseChange K z)
  exact (e.apply_symm_apply _).trans (rational p k X hprojective a hcard z)

theorem charpoly :
    letI := SmoothProper.CrystallineFiniteness.rational p k X hprojective 0
    letI := SmoothProper.GlobalFunctionWitt.finite p k X hprojective
    (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0).charpoly =
      ((WittFrobenius.witt p k X).toLinearMap.baseChange K).charpoly := by
  let := SmoothProper.CrystallineFiniteness.rational p k X hprojective 0
  let := SmoothProper.GlobalFunctionWitt.finite p k X hprojective
  let : Module.Free K (TensorProduct W K (WittVector p A)) := Module.Free.of_divisionRing K _
  exact ((CrystallineEquivalence.rationalEquiv p k X hprojective).symm.charpoly_conj
    (Global.CrystallineFrobenius.rationalFrobenius p k X a hcard 0)).symm.trans
      (congrArg (fun F : Module.End K (TensorProduct W K (WittVector p A)) => F.charpoly)
        (conjugate p k X hprojective a hcard))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.CrystallinePolynomial
