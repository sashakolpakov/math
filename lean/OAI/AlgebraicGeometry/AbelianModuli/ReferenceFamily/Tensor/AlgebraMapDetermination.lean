import Mathlib.RingTheory.TensorProduct.Maps

/-! # Algebra Map Determination -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.AlgebraMapDetermination

noncomputable section

/-! Maps from a scalar extension over its full coefficient base are
determined by the original affine functions. No additional scalar action
on the target is required. -/

open scoped TensorProduct

variable (R D A T : Type) [CommRing R] [CommRing D] [CommRing A] [CommRing T]
    [Algebra R D] [Algebra R A] [Algebra D T]

theorem tensorAlgebraMap_ext_original (f g : (D ⊗[R] A) →ₐ[D] T)
    (h : ∀ a, f ((1 : D) ⊗ₜ[R] a) = g ((1 : D) ⊗ₜ[R] a)) : f = g := by
  apply AlgHom.ext
  intro p
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul c a =>
    have hf : f (c ⊗ₜ[R] (1 : A)) = algebraMap D T c := f.commutes c
    have hg : g (c ⊗ₜ[R] (1 : A)) = algebraMap D T c := g.commutes c
    have hm : c ⊗ₜ[R] a = (c ⊗ₜ[R] (1 : A)) * ((1 : D) ⊗ₜ[R] a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hm, map_mul, map_mul, hf, hg, h]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.AlgebraMapDetermination
