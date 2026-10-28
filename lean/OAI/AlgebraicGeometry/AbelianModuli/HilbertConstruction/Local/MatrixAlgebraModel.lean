import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RankOneAlgebraRetraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelBaseChangeDimension

/-! # Matrix Algebra Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MatrixAlgebraModel

noncomputable section

/-! A local algebra with a split unit and a finite matrix model is its coefficient ring when the model's residue-field kernel has dimension at most one. No naturality of the chosen model is required. -/

universe u

theorem localMatrixModel_algebraMap_bijective
    {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ]
    (B : Matrix ν μ R) (e : A ≃ₗ[R] (Matrix.toLin' B).ker)
    (σ : A →ₗ[R] R) (hσ : σ 1 = 1)
    (h : Module.finrank (IsLocalRing.ResidueField R)
      (Matrix.toLin' (B.map (algebraMap R (IsLocalRing.ResidueField R)))).ker ≤ 1) :
    Function.Bijective (algebraMap R A) := by
  obtain ⟨φ, hφ⟩ := HilbertConstruction.Matrix.KernelBaseChangeDimension.localMatrixKernel_exists_scalar_embedding B h
  exact RankOneAlgebraRetraction.algebraMap_bijective_of_linearEmbedding σ (φ.comp e.toLinearMap) hσ
    (hφ.comp e.injective)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.MatrixAlgebraModel
