import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Inner Inverse -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.InnerInverse

noncomputable section

/-! Every linear map of vector spaces has an inner inverse. For a
rational matrix, this supplies a rational projection onto its kernel. -/
open scoped Classical
universe u v w
variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

theorem linearMap_exists_innerInverse (f : V →ₗ[K] W) :
    ∃ g : W →ₗ[K] V, (f.comp g).comp f = f := by
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨G, hG⟩ := g.exists_extend
  refine ⟨G, ?_⟩
  ext x
  let y : f.range := ⟨f x, LinearMap.mem_range_self f x⟩
  have hy : G (f x) = g y := congrArg (fun h : f.range →ₗ[K] V => h y) hG
  change f (G (f x)) = f x
  rw [hy]
  exact congrArg Subtype.val (congrArg (fun h : f.range →ₗ[K] f.range => h y) hg)

theorem matrix_exists_innerInverse {ι κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ K) : ∃ B : Matrix κ ι K, A * B * A = A := by
  obtain ⟨g, hg⟩ := linearMap_exists_innerInverse (Matrix.toLin' A)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact hg

theorem matrix_innerInverse_kernel_projection {ι κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ K) (B : Matrix κ ι K) (h : A * B * A = A) :
    A * (1 - B * A) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, sub_self]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.InnerInverse
