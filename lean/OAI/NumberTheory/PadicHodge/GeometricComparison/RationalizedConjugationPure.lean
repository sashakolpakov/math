import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Rationalized Conjugation Pure -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RationalizedConjugationPure.RationalizedConjugation

noncomputable section

/-! Conjugating an integral operator commutes with its actual tensor
rationalization and a specified rational comparison. -/

open scoped TensorProduct

universe uR uS uM uN uD
variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  {M : Type uM} [AddCommGroup M] [Module R M]
  {N : Type uN} [AddCommGroup N] [Module R N]
  {D : Type uD} [AddCommGroup D] [Module S D]
  (e : M ≃ₗ[R] N) (c : S ⊗[R] N ≃ₗ[S] D) (t : N →ₗ[R] N) (T : D →ₗ[S] D)
  (h : ∀ x : S ⊗[R] N, c (t.baseChange S x) = T (c x))

def transport : M →ₗ[R] M := e.symm.toLinearMap.comp (t.comp e.toLinearMap)

include h in
theorem pure (a : S) (x : M) :
    ((e.baseChange R S M N).trans c) (a ⊗ₜ[R] transport e t x) =
      T (((e.baseChange R S M N).trans c) (a ⊗ₜ[R] x)) := by
  change c (a ⊗ₜ[R] e (e.symm (t (e x)))) = T (c (a ⊗ₜ[R] e x))
  rw [e.apply_symm_apply]
  exact h (a ⊗ₜ[R] e x)

include h in
theorem naturality (x : S ⊗[R] M) :
    ((e.baseChange R S M N).trans c) ((transport e t).baseChange S x) =
      T (((e.baseChange R S M N).trans c) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => exact pure S e c t T h a x

include h in
theorem linearMap :
    ((e.baseChange R S M N).trans c).toLinearMap.comp ((transport e t).baseChange S) =
      T.comp ((e.baseChange R S M N).trans c).toLinearMap :=
  LinearMap.ext (naturality S e c t T h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.RationalizedConjugationPure.RationalizedConjugation
