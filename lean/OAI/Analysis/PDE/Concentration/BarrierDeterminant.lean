import OAI.Analysis.PDE.Dirichlet.Barriers
import OAI.LinearAlgebra.Moore.OuterPencil

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Matrix OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Dirichlet
open scoped MatrixOrder ComplexOrder

theorem mooreDifferential_identity_matrix {n : ℕ}
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hD : D.IsHermitian) :
    OAI.LinearAlgebra.Moore.mooreDifferential n 1 D = ∑ i, (D i i).re := by
  simpa only [OAI.LinearAlgebra.Moore.mooreDet_identity, Matrix.one_mul, one_mul] using
    OAI.LinearAlgebra.Moore.mooreDifferential_inverse n 1 D 1 (by simp) hD (by simp) (by simp)

theorem mooreDet_scalar_identity_add_outer (n : ℕ)
    (v : Fin (n + 2) → Quaternion ℝ) (t lam : ℝ) :
    OAI.LinearAlgebra.Moore.mooreDet (n + 2) (t • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ)) + lam • OAI.Analysis.Calculus.Quaternion.outer v) =
      t ^ (n + 2) + lam * t ^ (n + 1) * ∑ i, (OAI.Analysis.Calculus.Quaternion.outer v i i).re := by
  rw [OAI.LinearAlgebra.Moore.mooreDet_outer_pencil, OAI.LinearAlgebra.Moore.mooreDet_identity, mul_one,
    mooreDifferential_identity_matrix _ (OAI.Analysis.Calculus.Quaternion.outer_isHermitian v)]

/-- Quantitative determinant gain from a rank-one background. It retains one
factor of the background size and uses only `n+1` powers of the barrier. -/
theorem rank_one_barrier_determinant_lower (n : ℕ)
    (A R : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (hA : ∃ v, A = OAI.Analysis.Calculus.Quaternion.outer v) {α b lam t : ℝ}
    (hα : 0 < α) (hb : 0 < b) (hlam : 0 ≤ lam)
    (hR : (OAI.LinearAlgebra.Moore.complexify (R - α • 1)).PosSemidef)
    (htrace : t ≤ ∑ i, (A i i).re) :
    lam * (b * α) ^ (n + 1) * t ≤ OAI.LinearAlgebra.Moore.mooreDet (n + 2) (lam • A + b • R) := by
  obtain ⟨v, rfl⟩ := hA
  have hbase : (OAI.LinearAlgebra.Moore.complexify (lam • OAI.Analysis.Calculus.Quaternion.outer v + (b * α) • 1)).PosDef := by
    apply OAI.LinearAlgebra.Moore.complexify_add_pos_identity _ _ (mul_pos hb hα)
    rw [OAI.LinearAlgebra.Moore.complexify_real_smul]
    exact (OAI.LinearAlgebra.Moore.complexify_outer_posSemidef v).smul hlam
  have hd : (OAI.LinearAlgebra.Moore.complexify ((lam • OAI.Analysis.Calculus.Quaternion.outer v + b • R) -
      (lam • OAI.Analysis.Calculus.Quaternion.outer v + (b * α) • 1))).PosSemidef := by
    have he : (lam • OAI.Analysis.Calculus.Quaternion.outer v + b • R) - (lam • OAI.Analysis.Calculus.Quaternion.outer v + (b * α) • 1) = b • (R - α • 1) := by
      module
    rw [he, OAI.LinearAlgebra.Moore.complexify_real_smul]
    exact hR.smul hb.le
  have hm := OAI.LinearAlgebra.Moore.mooreDet_le_of_posSemidef_difference _ _ hbase hd
  rw [add_comm (lam • OAI.Analysis.Calculus.Quaternion.outer v), mooreDet_scalar_identity_add_outer] at hm
  have hp : 0 ≤ lam * (b * α) ^ (n + 1) := by positivity
  have ht := mul_le_mul_of_nonneg_left htrace hp
  have hz : 0 ≤ (b * α) ^ (n + 2) := by positivity
  exact ht.trans ((le_add_of_nonneg_left hz).trans hm)

end OAI.Analysis.PDE.Concentration
