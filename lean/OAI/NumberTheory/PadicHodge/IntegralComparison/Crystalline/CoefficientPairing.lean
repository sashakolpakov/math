import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution
import Mathlib.Algebra.Algebra.Bilinear

/-! # Coefficient Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientPairing

noncomputable section

/-! Bilinear products through the exact coefficient functor used by
native crystalline sheafification. The formula is the actual universe
lift, with the original coefficient-ring action restricted along `down`. -/

open _root_.CategoryTheory

universe u

variable (B : Type u) [CommRing B]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution.coefficientFunctor (B := B)

variable (M N P : ModuleCat.{u} B)

def lift (μ : M →ₗ[B] N →ₗ[B] P) :
    (T).obj M →ₗ[R] (T).obj N →ₗ[R] (T).obj P where
  toFun x :=
    { toFun := fun y => ULift.up (μ x.down y.down)
      map_add' := by
        intro y z
        exact congrArg ULift.up ((μ x.down).map_add y.down z.down)
      map_smul' := by
        intro r y
        exact congrArg ULift.up ((μ x.down).map_smul r.down y.down) }
  map_add' := by
    intro x z
    apply LinearMap.ext
    intro y
    exact congrArg ULift.up (LinearMap.congr_fun (μ.map_add x.down z.down) y.down)
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    exact congrArg ULift.up (LinearMap.congr_fun (μ.map_smul r.down x.down) y.down)

theorem lift_apply (μ : M →ₗ[B] N →ₗ[B] P)
    (x : (T).obj M) (y : (T).obj N) :
    lift B M N P μ x y = ULift.up (μ x.down y.down) := rfl

variable {M' N' P' : ModuleCat.{u} B}
  (a : M ⟶ M') (b : N ⟶ N') (c : P ⟶ P')
  (μ : M →ₗ[B] N →ₗ[B] P) (ν : M' →ₗ[B] N' →ₗ[B] P')
  (h : ∀ x y, c (μ x y) = ν (a x) (b y))

include h in
theorem map_lift (x : (T).obj M) (y : (T).obj N) :
    (T).map c (lift B M N P μ x y) =
      lift B M' N' P' ν ((T).map a x) ((T).map b y) :=
  congrArg ULift.up (h x.down y.down)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientPairing
