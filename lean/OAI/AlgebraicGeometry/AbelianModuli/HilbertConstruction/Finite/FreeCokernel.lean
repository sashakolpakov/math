import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.Kernel
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Free Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeCokernel.FiniteFreeCokernel

noncomputable section

/-! Completing a map with finite cokernel by finitely many free generators.
This is the elementary step in replacing a bounded flat complex by a
finite complex. -/

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem exists_completion (f : M →ₗ[R] N) [Module.Finite R (N ⧸ f.range)] :
    ∃ (n : ℕ) (v : (Fin n → R) →ₗ[R] N), Function.Surjective (f.coprod v) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := N ⧸ f.range)
  choose t ht using fun i => f.range.mkQ_surjective (s i)
  let v : (Fin n → R) →ₗ[R] N := Fintype.linearCombination R t
  refine ⟨n, v, fun y => ?_⟩
  have hy : f.range.mkQ y ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  have he : f.range.mkQ (v c) = f.range.mkQ y := by
    change f.range.mkQ (∑ i, c i • t i) = _
    simpa only [map_sum, map_smul, ht] using hc
  have hr : y - v c ∈ f.range := by
    rw [← f.range.ker_mkQ]
    change f.range.mkQ (y - v c) = 0
    rw [map_sub, he, sub_self]
  obtain ⟨x, hx⟩ := hr
  refine ⟨(x, c), ?_⟩
  change f x + v c = y
  rw [hx, sub_add_cancel]

structure Completion (f : M →ₗ[R] N) where
  n : ℕ
  generators : (Fin n → R) →ₗ[R] N
  surjective : Function.Surjective (f.coprod generators)

def completion (f : M →ₗ[R] N) [Module.Finite R (N ⧸ f.range)] : Completion f :=
  let n := (exists_completion f).choose
  let h := (exists_completion f).choose_spec
  ⟨n, h.choose, h.choose_spec⟩

theorem Completion.flat_kernel [Module.Flat R M] [Module.Flat R N]
    {f : M →ₗ[R] N} (D : Completion f) : Module.Flat R (f.coprod D.generators).ker := by
  have : Module.Flat R (M × (Fin D.n → R)) := HilbertConstruction.Flat.Kernel.FlatKernel.prod
  apply HilbertConstruction.Flat.Kernel.FlatKernel.flat _ D.surjective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeCokernel.FiniteFreeCokernel
