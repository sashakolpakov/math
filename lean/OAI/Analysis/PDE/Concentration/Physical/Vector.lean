import OAI.Analysis.PDE.Concentration.Physical.RankOne

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped Matrix

@[simp] theorem physicalVector_zero (d : ℕ) :
    physicalVector (0 : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) = 0 := by
  simp [physicalVector]

theorem physicalVector_injective (d : ℕ) :
    Function.Injective (physicalVector : (OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) → _) := by
  intro v w h
  have hh := congrArg (fun y => OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d) *ᵥ y) h
  simp only [physicalVector, Matrix.mulVec_mulVec,
    realLift_orthogonal (nullRotation_orthogonal d), Matrix.one_mulVec] at hh
  funext i
  have hi := congrFun hh ((nullIndexEquiv d).symm i)
  simpa using hi

theorem physicalMatrix_mulVec {d : ℕ} (M : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ))
    (v : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) :
    physicalMatrix M *ᵥ physicalVector v = physicalVector (M *ᵥ v) := by
  unfold physicalMatrix physicalVector
  have hc (u : Fin (d + 2) → Quaternion ℝ) :
      OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d) *ᵥ ((OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, realLift_orthogonal (nullRotation_orthogonal d), Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec]
  rw [hc, Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

theorem physicalVector_dot {d : ℕ} (v w : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) :
    star (physicalVector v) ⬝ᵥ physicalVector w = star v ⬝ᵥ w := by
  unfold physicalVector
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, realLift_orthogonal (nullRotation_orthogonal d), Matrix.one_mulVec]
  exact (nullIndexEquiv d).sum_comp (fun i => star (v i) * w i)

end OAI.Analysis.PDE.Concentration
