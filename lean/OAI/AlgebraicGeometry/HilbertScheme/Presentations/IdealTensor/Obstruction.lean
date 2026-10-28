import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Noetherian.Basic

/-! # Obstruction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Obstruction

noncomputable section

/-! The ideal-tensor kernel which tests flatness is a finite module
over a noetherian coefficient algebra. Flat modules have zero kernel. -/

open TensorProduct

universe u v w
variable (B : Type u) [CommRing B] (S : Type v) [CommRing S] [Algebra B S]
variable (M : Type w) [AddCommGroup M] [Module B M] [Module S M] [IsScalarTower B S M]

def idealTensorMultiplication (I : Ideal B) : M ⊗[B] I →ₗ[S] M :=
  (AlgebraTensorModule.rid B S M).toLinearMap.comp
    (AlgebraTensorModule.map (LinearMap.id : M →ₗ[S] M) I.subtype)

theorem idealTensorMultiplication_tmul (I : Ideal B) (m : M) (r : I) :
    idealTensorMultiplication B S M I (m ⊗ₜ[B] r) = r.val • m := rfl

theorem idealTensorMultiplication_injective (I : Ideal B) [Module.Flat B M] :
    Function.Injective (idealTensorMultiplication B S M I) := by
  exact (AlgebraTensorModule.rid B S M).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := M) I.subtype Subtype.val_injective)

theorem idealTensorModule_finite (I : Ideal B) (hI : I.FG) [Module.Finite S M] :
    Module.Finite S (M ⊗[B] I) := by
  let : Module.Finite B I := Module.Finite.of_fg hI
  exact Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange B S S M I)

theorem idealTensorObstruction_finite [IsNoetherianRing S] [Module.Finite S M]
    (I : Ideal B) (hI : I.FG) : Module.Finite S (idealTensorMultiplication B S M I).ker := by
  let := idealTensorModule_finite B S M I hI
  infer_instance

theorem idealTensorObstruction_eq_bot (I : Ideal B) [Module.Flat B M] :
    (idealTensorMultiplication B S M I).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (idealTensorMultiplication_injective B S M I)

theorem flat_iff_idealTensorObstructions_zero :
    Module.Flat B M ↔ ∀ I : Ideal B, (idealTensorMultiplication B S M I).ker = ⊥ := by
  constructor
  · intro h I
    let := h
    exact idealTensorObstruction_eq_bot B S M I
  · intro h
    apply ((Module.Flat.tfae_equational_criterion B M).out 1 2).mpr
    intro I
    apply (I.subtype.lTensor_inj_iff_rTensor_inj M).mp
    intro x y hxy
    apply (LinearMap.ker_eq_bot.mp (h I))
    exact congrArg (AlgebraTensorModule.rid B S M) hxy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Obstruction
