import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Span.Basic

/-! # Bilinear Diagonal -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BilinearDiagonal.BilinearDiagonalSpan

/-! Alternation of a skew bilinear map can be checked on a spanning set, including in characteristic two. -/

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

theorem diagonal_zero (B : M →ₗ[R] M →ₗ[R] N) (s : Set M)
    (hs : Submodule.span R s = ⊤) (hskew : ∀ x y, B x y + B y x = 0)
    (hgen : ∀ x ∈ s, B x x = 0) (x : M) : B x x = 0 := by
  have hx : x ∈ Submodule.span R s := hs.symm ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp only [map_zero]
  | add x y _ _ hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    exact hskew y x
  | smul a x _ hx =>
    simp only [map_smul, LinearMap.smul_apply, hx, smul_zero]

end OAI.NumberTheory.PadicHodge.GeometricComparison.BilinearDiagonal.BilinearDiagonalSpan
