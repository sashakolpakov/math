import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitModuleCoordinates

/-! # Module Coordinate Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The finite matrix equations for a kernel commute with extension of the coefficient ring. -/

open TensorProduct

universe u

variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
variable (A : Type u) [CommRing A] [Algebra R A]

def SplitModuleKernel.SplitModuleEmbedding.coordinateBaseChange (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R)) :
    SplitModuleKernel.SplitModuleEmbedding A (A ⊗[R] M) (μ → A) :=
  (P.baseChange A).changeAmbient (TensorProduct.piScalarRight R A A μ)

omit [Fintype ν] [DecidableEq ν] in
theorem SplitModuleKernel.SplitModuleEmbedding.coordinateBaseChange_projection_single
    (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R)) (j : μ) :
    (P.coordinateBaseChange A).projection (Pi.single j 1) = 1 ⊗ₜ[R] P.projection (Pi.single j 1) := by
  change P.projection.baseChange A
    ((TensorProduct.piScalarRight R A A μ).symm (Pi.single j 1)) = _
  rw [TensorProduct.piScalarRight_symm_single, LinearMap.baseChange_tmul]

omit [Fintype ν] [DecidableEq ν] in
theorem SplitModuleKernel.SplitModuleEmbedding.coordinateBaseChange_inclusion_tmul
    (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R)) (x : M) (i : μ) :
    (P.coordinateBaseChange A).inclusion (1 ⊗ₜ[R] x) i = algebraMap R A (P.inclusion x i) := by
  change TensorProduct.piScalarRight R A A μ (P.inclusion.baseChange A (1 ⊗ₜ[R] x)) i = _
  simp only [LinearMap.baseChange_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, Algebra.smul_def, mul_one]

theorem ModuleCoordinateBaseChange.splitModuleKernelMatrix_baseChange (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R))
    (Q : SplitModuleKernel.SplitModuleEmbedding R N (ν → R)) (f : M →ₗ[R] N) :
    SplitModuleCoordinates.splitModuleKernelMatrix (P.coordinateBaseChange A) (Q.coordinateBaseChange A) (f.baseChange A) =
      (SplitModuleCoordinates.splitModuleKernelMatrix P Q f).map (algebraMap R A) := by
  ext i j
  cases i with
  | inl i =>
    simp only [SplitModuleCoordinates.splitModuleKernelMatrix_inl, Matrix.map_apply,
      SplitModuleKernel.SplitModuleEmbedding.coordinateBaseChange_projection_single,
      LinearMap.baseChange_tmul, SplitModuleKernel.SplitModuleEmbedding.coordinateBaseChange_inclusion_tmul]
  | inr i =>
    simp only [SplitModuleCoordinates.splitModuleKernelMatrix_inr, Matrix.map_apply,
      SplitModuleKernel.SplitModuleEmbedding.coordinateBaseChange_projection_single,
      SplitModuleKernel.SplitModuleEmbedding.coordinateBaseChange_inclusion_tmul, map_sub]
    congr 1
    by_cases h : i = j <;> simp only [Pi.single_apply, h, ite_true, ite_false, map_one, map_zero]

def ModuleCoordinateBaseChange.splitModuleKernelMatrixBaseChangeEquiv (P : SplitModuleKernel.SplitModuleEmbedding R M (μ → R))
    (Q : SplitModuleKernel.SplitModuleEmbedding R N (ν → R)) (f : M →ₗ[R] N) :
    (f.baseChange A).ker ≃ₗ[A]
      (Matrix.toLin' ((SplitModuleCoordinates.splitModuleKernelMatrix P Q f).map (algebraMap R A))).ker :=
  (SplitModuleCoordinates.splitModuleKernelMatrixEquiv (P.coordinateBaseChange A) (Q.coordinateBaseChange A)
    (f.baseChange A)).trans
    (LinearEquiv.ofEq _ _ (congrArg (fun B : Matrix (ν ⊕ μ) μ A => (Matrix.toLin' B).ker)
      (ModuleCoordinateBaseChange.splitModuleKernelMatrix_baseChange A P Q f)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
