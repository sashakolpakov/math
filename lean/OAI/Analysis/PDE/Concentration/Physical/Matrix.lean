import OAI.Analysis.PDE.Concentration.Physical.Current

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped Matrix

/-- The source matrix, reindexed and rotated into the physical frame. -/
def physicalMatrix {d : ℕ} (M : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)) :
    Matrix (Fin (d + 2)) (Fin (d + 2)) (Quaternion ℝ) :=
  (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ * M.submatrix (nullIndexEquiv d) (nullIndexEquiv d) *
    OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d)

theorem physicalMatrix_eq {d : ℕ} (M : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)) :
    physicalMatrix M = matrixConjugationCLM (nullRotation d) (nullMatrixReindex d M) := rfl

theorem physicalMatrix_mul {d : ℕ} (M N : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)) :
    physicalMatrix M * physicalMatrix N = physicalMatrix (M * N) := by
  have hR := realLift_orthogonal (nullRotation_orthogonal d)
  unfold physicalMatrix
  calc
    _ = (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ * M.submatrix (nullIndexEquiv d) (nullIndexEquiv d) *
        (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d) * (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ) *
        N.submatrix (nullIndexEquiv d) (nullIndexEquiv d) * OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d) := by
      simp only [Matrix.mul_assoc]
    _ = (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ *
        (M.submatrix (nullIndexEquiv d) (nullIndexEquiv d) *
          N.submatrix (nullIndexEquiv d) (nullIndexEquiv d)) * OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d) := by
      rw [hR, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.submatrix_mul_equiv]

@[simp] theorem physicalMatrix_zero (d : ℕ) :
    physicalMatrix (0 : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)) = 0 := by
  simp [physicalMatrix]

theorem physicalMatrix_mul_zero {d : ℕ} {M N : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)}
    (hMN : M * N = 0) : physicalMatrix M * physicalMatrix N = 0 := by
  rw [physicalMatrix_mul, hMN, physicalMatrix_zero]

theorem physicalPacketCurrent_eq_physicalMatrix {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) :
    physicalPacketCurrent h a κ cR cI v x =
      physicalMatrix (OAI.Analysis.Calculus.Current.sourceRegularizedCurrent h a κ cR cI v
        (physicalToNullCurrentPoint d x).1 (physicalToNullCurrentPoint d x).2) := rfl

end OAI.Analysis.PDE.Concentration
