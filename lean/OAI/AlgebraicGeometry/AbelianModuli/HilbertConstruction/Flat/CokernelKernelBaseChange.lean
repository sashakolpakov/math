import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.SurjectivityBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CokernelSplittingEquation

/-! # Cokernel Kernel Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.CokernelKernelBaseChange

noncomputable section

/-! A finite matrix with flat cokernel has a split kernel projector.
The projector proves that its kernel commutes with every coefficient
map, including nonflat maps and maps between nonreduced rings. -/
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.CokernelSplittingEquation
universe u v w
variable {R : Type u} [CommRing R]

theorem kernel_eq_range_of_splitting_equation
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (h : f.comp (g.comp f) = f) :
    f.ker = (LinearMap.id - g.comp f).range := by
  ext x
  constructor
  · intro hx
    refine ⟨x, ?_⟩
    change x - g (f x) = x
    rw [LinearMap.mem_ker.mp hx, map_zero, sub_zero]
  · rintro ⟨y, rfl⟩
    change f (y - g (f y)) = 0
    rw [map_sub]
    have hh : f (g (f y)) = f y := LinearMap.congr_fun h y
    rw [hh, sub_self]

theorem matrix_kernel_projector_range
    {μ : Type v} {ν : Type w} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
    (A : Matrix ν μ R) (X : Matrix μ ν R) (h : A * X * A = A) :
    (Matrix.toLin' A).ker = (Matrix.toLin' (1 - X * A)).range := by
  have hh : (Matrix.toLin' A).comp ((Matrix.toLin' X).comp (Matrix.toLin' A)) = Matrix.toLin' A := by
    simpa only [Matrix.toLin'_mul, LinearMap.comp_assoc] using congrArg Matrix.toLin' h
  simpa only [map_sub, Matrix.toLin'_one, Matrix.toLin'_mul] using
    kernel_eq_range_of_splitting_equation (Matrix.toLin' A) (Matrix.toLin' X) hh

variable {S μ ν : Type u} [CommRing S]
variable [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

theorem matrix_kernel_baseChange_of_flat_cokernel
    (φ : R →+* S) (A : Matrix ν μ R)
    (hflat : Module.Flat R ((ν → R) ⧸ (Matrix.toLin' A).range)) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ (Matrix.toLin' A).ker = (Matrix.toLin' (A.map φ)).ker := by
  obtain ⟨X, hX⟩ := (HilbertScheme.Presentations.CokernelSplittingEquation.matrix_cokernel_flat_iff_splitting_equation A).mp hflat
  have hXS : A.map φ * X.map φ * A.map φ = A.map φ := by
    simpa only [Matrix.map_mul] using congrArg (fun B => B.map φ) hX
  rw [matrix_kernel_projector_range A X hX, HilbertConstruction.Matrix.SurjectivityBaseChange.coordinateSubmoduleExtension_matrixRange,
    matrix_kernel_projector_range (A.map φ) (X.map φ) hXS]
  have he : (1 - X * A).map φ = 1 - X.map φ * A.map φ := by
    ext i j
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply]
  rw [he]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.CokernelKernelBaseChange
