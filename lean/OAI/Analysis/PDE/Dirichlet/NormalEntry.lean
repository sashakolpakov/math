import OAI.Analysis.PDE.Dirichlet.AdaptedBasis
import OAI.LinearAlgebra.Moore.Schur

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Positivity on the coordinate tangent hyperplane is exactly positivity
of the trailing quaternionic block. No positivity of the normal entry is used. -/
theorem trailingBlock_posDef {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Q) (hA : A.IsHermitian)
    (hT : ∀ z : Fin (n + 1) → Q, z ≠ 0 → z 0 = 0 → 0 < (quaternionForm A z).re) :
    (OAI.LinearAlgebra.Moore.complexify (A.submatrix Fin.succ Fin.succ)).PosDef := by
  apply (OAI.LinearAlgebra.Moore.complexify_posDef_iff (hA.submatrix Fin.succ)).mpr
  intro z hz
  let w : Fin (n + 1) → Q := Fin.cases 0 z
  have hw : w ≠ 0 := by
    intro he
    apply hz
    funext i
    exact congrFun he i.succ
  have hp := hT w hw rfl
  simpa only [quaternionForm, Fin.sum_univ_succ, w, Fin.cases_zero, Fin.cases_succ,
    star_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, Matrix.submatrix_apply] using hp

/-- The normal cofactor is strictly positive from tangential positivity,
even for an indefinite full matrix. -/
theorem normal_cofactor_pos_of_tangent {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Q) (hA : A.IsHermitian)
    (hT : ∀ z : Fin (n + 1) → Q, z ≠ 0 → z 0 = 0 → 0 < (quaternionForm A z).re) :
    0 < (OAI.LinearAlgebra.Moore.mooreCofactor (n + 1) A 0 0).re := by
  have hD := trailingBlock_posDef A hA hT
  conv_rhs => rw [OAI.LinearAlgebra.Moore.hermitianBlock_reconstruct A hA]
  rw [OAI.LinearAlgebra.Moore.mooreCofactor_hermitianBlock_normal _ _ _ hD]
  exact OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef _ hD

/-- The determinant equation determines the normal entry using only the
tangential block and the mixed entries. -/
theorem normal_entry_of_tangent {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Q) (hA : A.IsHermitian)
    (hT : ∀ z : Fin (n + 1) → Q, z ≠ 0 → z 0 = 0 → 0 < (quaternionForm A z).re) :
    ∃ C : Matrix (Fin n) (Fin n) Q,
      A.submatrix Fin.succ Fin.succ * C = 1 ∧
      C * A.submatrix Fin.succ Fin.succ = 1 ∧
      (A 0 0).re = OAI.LinearAlgebra.Moore.mooreDet (n + 1) A / OAI.LinearAlgebra.Moore.mooreDet n (A.submatrix Fin.succ Fin.succ) +
        (quaternionForm C (fun i ↦ A i.succ 0)).re := by
  have hD := trailingBlock_posDef A hA hT
  obtain ⟨C, hDC, hCD⟩ := OAI.LinearAlgebra.Moore.exists_quaternion_inverse_of_complexify_posDef _ hD
  refine ⟨C, hDC, hCD, ?_⟩
  have h := OAI.LinearAlgebra.Moore.hermitianBlock_normal_entry (A 0 0).re (fun i ↦ A i.succ 0) _ C hD hDC hCD
  rwa [← OAI.LinearAlgebra.Moore.hermitianBlock_reconstruct A hA] at h

end OAI.Analysis.PDE.Dirichlet
