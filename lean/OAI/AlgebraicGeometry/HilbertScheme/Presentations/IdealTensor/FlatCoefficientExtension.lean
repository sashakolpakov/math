import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Obstruction

/-! # Flat Coefficient Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.FlatCoefficientExtension

noncomputable section

/-! Ideal-tensor injectivity survives flat extension of the algebra
acting on the module, including localization of that algebra. -/

open TensorProduct

universe u v w t
variable (B : Type u) [CommRing B] (S : Type v) [CommRing S] [Algebra B S]
variable (T : Type w) [CommRing T] [Algebra S T] [Algebra B T] [IsScalarTower B S T]
variable (M : Type t) [AddCommGroup M] [Module B M] [Module S M] [IsScalarTower B S M]

theorem idealTensorMultiplication_flatExtension_formula (I : Ideal B)
    (x : (T ⊗[S] M) ⊗[B] I) :
    Obstruction.idealTensorMultiplication B T (T ⊗[S] M) I x =
      (Obstruction.idealTensorMultiplication B S M I).lTensor T
        (AlgebraTensorModule.assoc B S T T M I x) := by
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x r =>
    induction x with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul t m =>
      change r.val • (t ⊗ₜ[S] m) = t ⊗ₜ[S] (r.val • m)
      rw [← algebraMap_smul S r.val (t ⊗ₜ[S] m), ← TensorProduct.tmul_smul,
        algebraMap_smul]

theorem idealTensorMultiplication_injective_of_flat_extension [Module.Flat S T]
    (I : Ideal B) (h : Function.Injective (Obstruction.idealTensorMultiplication B S M I)) :
    Function.Injective (Obstruction.idealTensorMultiplication B T (T ⊗[S] M) I) := by
  intro x y hxy
  apply (AlgebraTensorModule.assoc B S T T M I).injective
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := T)
    (Obstruction.idealTensorMultiplication B S M I) h
  simpa only [← idealTensorMultiplication_flatExtension_formula] using hxy

theorem flat_of_flat_coefficient_extension [Module.Flat S T] [Module.Flat B M] :
    Module.Flat B (T ⊗[S] M) := by
  apply (Obstruction.flat_iff_idealTensorObstructions_zero B T (T ⊗[S] M)).mpr
  intro I
  apply bot_unique
  intro x hx
  have hinj := idealTensorMultiplication_injective_of_flat_extension B S T M I
    (Obstruction.idealTensorMultiplication_injective B S M I)
  have hx0 : Obstruction.idealTensorMultiplication B T (T ⊗[S] M) I x = 0 := hx
  exact (Submodule.mem_bot T).mpr (hinj (hx0.trans (map_zero _).symm))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.FlatCoefficientExtension
