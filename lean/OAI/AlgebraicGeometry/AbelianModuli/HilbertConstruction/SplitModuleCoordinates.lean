import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitModuleKernel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Split Module Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite free ambient modules give explicit coordinate matrices for kernels of maps between direct summands. -/

universe u

variable {R : Type u} [CommRing R]
variable {M F G : Type u} [AddCommGroup M] [Module R M]
variable [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]

def SplitModuleKernel.SplitModuleEmbedding.changeAmbient (P : SplitModuleKernel.SplitModuleEmbedding R M F) (e : F ≃ₗ[R] G) :
    SplitModuleKernel.SplitModuleEmbedding R M G where
  inclusion := e.toLinearMap.comp P.inclusion
  projection := P.projection.comp e.symm.toLinearMap
  split := by
    ext x
    exact (congrArg P.projection (e.symm_apply_apply (P.inclusion x))).trans
      (P.projection_inclusion x)

variable {N : Type u} [AddCommGroup N] [Module R N]
variable {μ ν : Type u} [Fintype μ] [DecidableEq μ]

def SplitModuleCoordinates.splitModuleCoordinateEquation (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R))
    (Q : SplitModuleKernel.SplitModuleEmbedding R N (ν → R)) (f : M →ₗ[R] N) :
    (μ → R) →ₗ[R] (ν ⊕ μ → R) :=
  (LinearEquiv.sumArrowLequivProdArrow ν μ R R).symm.toLinearMap.comp
    (SplitModuleKernel.splitModuleKernelEquation P Q f)

def SplitModuleCoordinates.splitModuleKernelMatrix (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R))
    (Q : SplitModuleKernel.SplitModuleEmbedding R N (ν → R)) (f : M →ₗ[R] N) : Matrix (ν ⊕ μ) μ R :=
  LinearMap.toMatrix' (SplitModuleCoordinates.splitModuleCoordinateEquation P Q f)

theorem SplitModuleCoordinates.splitModuleCoordinateEquation_ker (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R))
    (Q : SplitModuleKernel.SplitModuleEmbedding R N (ν → R)) (f : M →ₗ[R] N) :
    (Matrix.toLin' (SplitModuleCoordinates.splitModuleKernelMatrix P Q f)).ker = (SplitModuleKernel.splitModuleKernelEquation P Q f).ker := by
  rw [SplitModuleCoordinates.splitModuleKernelMatrix, Matrix.toLin'_toMatrix']
  ext x
  change (LinearEquiv.sumArrowLequivProdArrow ν μ R R).symm
    (SplitModuleKernel.splitModuleKernelEquation P Q f x) = 0 ↔ SplitModuleKernel.splitModuleKernelEquation P Q f x = 0
  exact (LinearEquiv.sumArrowLequivProdArrow ν μ R R).symm.map_eq_zero_iff

def SplitModuleCoordinates.splitModuleKernelMatrixEquiv (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R))
    (Q : SplitModuleKernel.SplitModuleEmbedding R N (ν → R)) (f : M →ₗ[R] N) :
    f.ker ≃ₗ[R] (Matrix.toLin' (SplitModuleCoordinates.splitModuleKernelMatrix P Q f)).ker :=
  (SplitModuleKernel.splitModuleKernelEquiv P Q f).trans
    (LinearEquiv.ofEq _ _ (SplitModuleCoordinates.splitModuleCoordinateEquation_ker P Q f).symm)

theorem SplitModuleCoordinates.splitModuleKernelMatrix_inl (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R))
    (Q : SplitModuleKernel.SplitModuleEmbedding R N (ν → R)) (f : M →ₗ[R] N) (i : ν) (j : μ) :
    SplitModuleCoordinates.splitModuleKernelMatrix P Q f (.inl i) j = Q.inclusion (f (P.projection (Pi.single j 1))) i := rfl

theorem SplitModuleCoordinates.splitModuleKernelMatrix_inr (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R))
    (Q : SplitModuleKernel.SplitModuleEmbedding R N (ν → R)) (f : M →ₗ[R] N) (i j : μ) :
    SplitModuleCoordinates.splitModuleKernelMatrix P Q f (.inr i) j =
      (Pi.single j (1 : R) : μ → R) i - P.inclusion (P.projection (Pi.single j 1)) i := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
