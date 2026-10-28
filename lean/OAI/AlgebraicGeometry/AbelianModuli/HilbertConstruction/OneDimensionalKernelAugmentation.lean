import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Prod

/-! # One Dimensional Kernel Augmentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OneDimensionalKernelAugmentation

noncomputable section

/-! A linear map over a field whose kernel has dimension at most one becomes injective after adjoining one scalar coordinate. -/

universe u v w

theorem oneDimensionalKernel_exists_injective_augmentation
    {K : Type u} [Field K] {V : Type v} {W : Type w}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    (h : Module.finrank K f.ker ≤ 1) :
    ∃ l : V →ₗ[K] K, Function.Injective (f.prod l) := by
  have hd : Module.finrank K f.ker ≤ Module.finrank K K := by simpa using h
  obtain ⟨g, hg⟩ := (finrank_le_iff_exists_linearMap).mp hd
  obtain ⟨l, hl⟩ := g.exists_extend
  refine ⟨l, LinearMap.ker_eq_bot.mp ?_⟩
  apply eq_bot_iff.mpr
  intro x hx
  have hx0 : (f.prod l) x = 0 := hx
  have hf : f x = 0 := congrArg Prod.fst hx0
  have hlf : l x = 0 := congrArg Prod.snd hx0
  let z : f.ker := ⟨x, hf⟩
  have hz : g z = 0 := (LinearMap.congr_fun hl z).symm.trans hlf
  have he : z = 0 := hg (hz.trans g.map_zero.symm)
  exact congrArg Subtype.val he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OneDimensionalKernelAugmentation
