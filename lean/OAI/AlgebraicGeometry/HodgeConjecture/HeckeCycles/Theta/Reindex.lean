import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ReindexHeisenberg
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Reindex.CM

noncomputable section

/-! Relabeling the actual rational lattice and finite Schwartz function
preserves PoissonAutomorphy's theta series and its Jacobi variable exactly. -/

open scoped Classical

variable {I J : Type} [Fintype I] [Fintype J] (e : I ≃ J)

theorem matrix_form (M : Matrix J J ℂ) (x y : J → ℝ) :
    ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (M.submatrix e e) (x ∘ e) (y ∘ e) = ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm M x y := by
  simp only [ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Matrix.submatrix_apply, Function.comp_apply]
  calc
    _ = ∑ i : I, ∑ j : J, (x (e i) : ℂ) * ((y j : ℂ) * M (e i) j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact e.sum_comp (fun j => (x (e i) : ℂ) * ((y j : ℂ) * M (e i) j))
    _ = _ := e.sum_comp (fun i => ∑ j : J, (x i : ℂ) * ((y j : ℂ) * M i j))

theorem term (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J) (W : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hM : Z.matrix.submatrix e e = W.matrix) (z : J → ℂ) (x : I → ℚ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ) Z z (fun j => x (e.symm j)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ W (z ∘ e) x := by
  have hf : ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.matrix (fun j => (x (e.symm j) : ℝ)) (fun j => (x (e.symm j) : ℝ)) =
      ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm W.matrix (fun i => (x i : ℝ)) (fun i => (x i : ℝ)) := by
    simpa only [hM, Function.comp_def, Equiv.symm_apply_apply] using
      (matrix_form e Z.matrix (fun j => (x (e.symm j) : ℝ)) (fun j => (x (e.symm j) : ℝ))).symm
  have hl : (∑ j : J, (x (e.symm j) : ℂ) * z j) = ∑ i : I, (x i : ℂ) * z (e i) := by
    simpa only [Equiv.symm_apply_apply] using
      (e.sum_comp (fun j => (x (e.symm j) : ℂ) * z j)).symm
  have ht : (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (fun j => x (e.symm j))) =
      φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) := by
    rw [Finite.ReindexHeisenberg.CM.Pairing.testEquiv_apply]
    apply congrArg φ.val
    funext i
    exact congrArg (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (congrArg x (e.symm_apply_apply i))
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm
  rw [ht, hf, hl]
  rfl

theorem theta (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J) (W : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hM : Z.matrix.submatrix e e = W.matrix) (z : J → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ) Z z =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ W (z ∘ e) := by
  let q : (I → ℚ) ≃ (J → ℚ) :=
    (LinearEquiv.funCongrLeft ℚ ℚ e.symm).toEquiv
  calc
    _ = ∑' x : I → ℚ,
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm (Finite.ReindexHeisenberg.CM.Pairing.testEquiv e φ) Z z (q x) := (q.tsum_eq _).symm
    _ = _ := tsum_congr (term e φ Z W hM z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Reindex.CM
