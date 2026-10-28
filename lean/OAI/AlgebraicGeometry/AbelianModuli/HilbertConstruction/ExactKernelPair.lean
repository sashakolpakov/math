import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Exact Kernel Pair -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExactKernelPair

noncomputable section

/-! An exact pair induces a short exact sequence between its consecutive kernels. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v

def exactKernelPair {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (kernel.ι S.f) (kernel.lift S.g S.f S.zero) (by
    apply (cancel_mono (kernel.ι S.g)).mp
    simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp])

theorem exactKernelPair_shortExact {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex C) (hS : S.Exact) : (exactKernelPair S).ShortExact := by
  unfold exactKernelPair
  let q := kernel.lift S.g S.f S.zero
  have : Epi q := hS.epi_kernelLift
  refine { exact := ?_, mono_f := by infer_instance, epi_g := ?_ }
  · apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι' _ _ ?_
    intro W k hk
    change k ≫ q = 0 at hk
    refine ⟨kernel.lift S.f k ?_, ?_⟩
    · calc
        k ≫ S.f = (k ≫ q) ≫ kernel.ι S.g := by
          dsimp only [q]
          rw [Category.assoc, kernel.lift_ι]
        _ = 0 := by rw [hk, zero_comp]
    · exact kernel.lift_ι _ _ _
  · change Epi q
    infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExactKernelPair
