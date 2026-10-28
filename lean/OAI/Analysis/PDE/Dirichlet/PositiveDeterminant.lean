import OAI.Analysis.PDE.Dirichlet.Continuity
import OAI.LinearAlgebra.Moore.Square
import OAI.Analysis.PDE.Dirichlet.MatrixBounds

open Set Filter
open scoped Matrix ComplexOrder Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem mooreDet_sq_eq_complexify_det_of_posSemidef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) :
    OAI.LinearAlgebra.Moore.mooreDet n A ^ 2 = (OAI.LinearAlgebra.Moore.complexify A).det.re := by
  have hline : Continuous (fun t : ℝ ↦ A + t • (1 : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hleft : Continuous (fun t : ℝ ↦ OAI.LinearAlgebra.Moore.mooreDet n (A + t • 1) ^ 2) :=
    ((OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp hline).pow 2
  have hright : Continuous (fun t : ℝ ↦ (OAI.LinearAlgebra.Moore.complexify (A + t • 1)).det.re) := by
    apply Complex.continuous_re.comp
    apply Continuous.matrix_det
    simp only [OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
    fun_prop
  have hclosed := isClosed_eq hleft hright
  have hsub : Ioi (0 : ℝ) ⊆ {t | OAI.LinearAlgebra.Moore.mooreDet n (A + t • 1) ^ 2 = (OAI.LinearAlgebra.Moore.complexify (A + t • 1)).det.re} := by
    intro t ht
    exact OAI.LinearAlgebra.Moore.mooreDet_sq_eq_complexify_det_of_posDef _ (OAI.LinearAlgebra.Moore.complexify_add_pos_identity A hA ht)
  have hzero : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by simp
  have heq : OAI.LinearAlgebra.Moore.mooreDet n (A + (0 : ℝ) • 1) ^ 2 = (OAI.LinearAlgebra.Moore.complexify (A + (0 : ℝ) • 1)).det.re :=
    closure_minimal hsub hclosed hzero
  simpa only [zero_smul, add_zero] using heq

theorem complex_posDef_of_posSemidef_det_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (hdet : 0 < A.det.re) : A.PosDef := by
  have hd : A.det.re = ∏ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    rfl
  rw [hd] at hdet
  apply hA.isHermitian.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hi : hA.isHermitian.eigenvalues i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hdet.ne') i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) hi.symm

/-- A positive Moore determinant excludes every singular positive-semidefinite
boundary limit. This is used for data-uniform ellipticity. -/
theorem complexify_posDef_of_posSemidef_mooreDet_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) OAI.Analysis.Calculus.Quaternion.Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef)
    (hdet : 0 < OAI.LinearAlgebra.Moore.mooreDet n A) : (OAI.LinearAlgebra.Moore.complexify A).PosDef := by
  apply complex_posDef_of_posSemidef_det_pos _ hA
  rw [← mooreDet_sq_eq_complexify_det_of_posSemidef A hA]
  positivity

end OAI.Analysis.PDE.Dirichlet
