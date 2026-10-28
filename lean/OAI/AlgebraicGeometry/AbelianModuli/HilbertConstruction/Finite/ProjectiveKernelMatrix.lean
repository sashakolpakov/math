import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ModuleCoordinateBaseChange

/-! # Projective Kernel Matrix -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelMatrix

noncomputable section

/-! Every map between finite projective modules has one finite matrix that computes its kernel after every scalar extension. -/

open TensorProduct

universe u

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

def finiteProjectiveCoordinateSize : ℕ := (SplitModuleKernel.finite_projective_exists_split (R := R) (M := M)).choose

def finiteProjectiveCoordinateEmbedding :
    SplitModuleKernel.SplitModuleEmbedding R M (ULift.{u} (Fin (finiteProjectiveCoordinateSize R M)) → R) :=
  (Classical.choice (SplitModuleKernel.finite_projective_exists_split (R := R) (M := M)).choose_spec).changeAmbient
    (LinearEquiv.funCongrLeft R R Equiv.ulift)

variable {R M}
variable {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

def finiteProjectiveKernelMatrix (f : M →ₗ[R] N) :
    Matrix (ULift.{u} (Fin (finiteProjectiveCoordinateSize R N)) ⊕
      ULift.{u} (Fin (finiteProjectiveCoordinateSize R M)))
      (ULift.{u} (Fin (finiteProjectiveCoordinateSize R M))) R :=
  SplitModuleCoordinates.splitModuleKernelMatrix (finiteProjectiveCoordinateEmbedding R M)
    (finiteProjectiveCoordinateEmbedding R N) f

def finiteProjectiveKernelMatrixBaseChangeEquiv (f : M →ₗ[R] N)
    (A : Type u) [CommRing A] [Algebra R A] :
    (f.baseChange A).ker ≃ₗ[A]
      (Matrix.toLin' ((finiteProjectiveKernelMatrix f).map (algebraMap R A))).ker :=
  ModuleCoordinateBaseChange.splitModuleKernelMatrixBaseChangeEquiv A (finiteProjectiveCoordinateEmbedding R M)
    (finiteProjectiveCoordinateEmbedding R N) f

theorem finite_projective_kernel_has_uniform_matrix (f : M →ₗ[R] N) :
    ∃ (m n : ℕ) (B : Matrix (ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)) (ULift.{u} (Fin m)) R),
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty ((f.baseChange A).ker ≃ₗ[A] (Matrix.toLin' (B.map (algebraMap R A))).ker) :=
  ⟨finiteProjectiveCoordinateSize R M, finiteProjectiveCoordinateSize R N,
    finiteProjectiveKernelMatrix f, fun A _ _ => ⟨finiteProjectiveKernelMatrixBaseChangeEquiv f A⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelMatrix
