import OAI.LinearAlgebra.Moore.Adjugate

/-! Nonvanishing of the normal cofactor when the tangential restriction is
positive definite, without requiring a prior principal-minor formula. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.PDE.Dirichlet
open scoped MatrixOrder ComplexOrder

theorem coordinateProjector_eq_single (n : ℕ) (k : Fin n) :
    coordinateProjector n k = Matrix.single k k (1 : Quaternion ℝ) := by
  apply Matrix.ext
  intro i j
  simp [coordinateProjector, Matrix.single, eq_comm]

theorem coordinateProjector_isHermitian (n : ℕ) (k : Fin n) :
    (coordinateProjector n k).IsHermitian := by
  apply Matrix.ext
  intro i j
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [Matrix.conjTranspose_apply, coordinateProjector, hi, hj]

theorem quaternionForm_coordinateProjector (n : ℕ) (k : Fin n) (z : Fin n → Quaternion ℝ) :
    (OAI.Analysis.PDE.Dirichlet.quaternionForm (coordinateProjector n k) z).re = Quaternion.normSq (z k) := by
  simp [OAI.Analysis.PDE.Dirichlet.quaternionForm, coordinateProjector, ite_and, Quaternion.star_mul_self]

theorem mooreCofactor_diag (n : ℕ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (k : Fin n) :
    (mooreCofactor n A k k).re =
      mooreDet n (A + coordinateProjector n k) - mooreDet n A := by
  have hd := (hasDerivAt_mooreDet_affine A (coordinateProjector n k) 0).unique
    (hasDerivAt_mooreDet_coordinate n A k 0)
  simp only [zero_smul, add_zero] at hd
  calc
    (mooreCofactor n A k k).re = realTrace (mooreCofactor n A * coordinateProjector n k) := by
      rw [coordinateProjector_eq_single, realTrace_mul_single, mul_one]
    _ = mooreDifferential n A (coordinateProjector n k) :=
      mooreCofactor_pairing n A _ (coordinateProjector_isHermitian n k)
    _ = _ := hd

/-- Adding the normal rank-one projector makes the full matrix positive
definite if its tangential restriction is already positive definite. -/
theorem complexify_add_coordinate_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (k : Fin n)
    (hA : (complexify A).PosSemidef)
    (hT : ∀ z ≠ 0, z k = 0 → 0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm A z).re) :
    (complexify (A + coordinateProjector n k)).PosDef := by
  have hAH := isHermitian_of_complexify hA.isHermitian
  apply (complexify_posDef_iff (hAH.add (coordinateProjector_isHermitian n k))).mpr
  intro z hz
  rw [OAI.Analysis.PDE.Dirichlet.quaternionForm_add, Quaternion.re_add, quaternionForm_coordinateProjector]
  by_cases hk : z k = 0
  · simpa [hk] using hT z hz hk
  · exact add_pos_of_nonneg_of_pos ((complexify_posSemidef_iff hAH).mp hA z)
      (lt_of_le_of_ne (show 0 ≤ Quaternion.normSq (z k) from Quaternion.normSq_nonneg)
        (Ne.symm (Quaternion.normSq_ne_zero.mpr hk)))

/-- The normal component of the cofactor is strictly positive at a singular
semidefinite matrix with positive tangential restriction. -/
theorem mooreCofactor_diag_pos_of_tangential_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (k : Fin n)
    (hA : (complexify A).PosSemidef) (hdet : mooreDet n A = 0)
    (hT : ∀ z ≠ 0, z k = 0 → 0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm A z).re) :
    0 < (mooreCofactor n A k k).re := by
  rw [mooreCofactor_diag, hdet, sub_zero]
  exact mooreDet_pos_of_complexify_posDef _ (complexify_add_coordinate_posDef A k hA hT)

end OAI.LinearAlgebra.Moore
