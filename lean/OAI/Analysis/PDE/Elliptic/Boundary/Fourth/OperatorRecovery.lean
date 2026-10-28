import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Tangential
import OAI.Analysis.PDE.Elliptic.Boundary.Third.LocalRecovery
import OAI.Analysis.PDE.Schauder.Dirichlet.EuclideanCoefficientHolder

noncomputable section
open Set
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Schauder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance fourthOperator1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthOperator1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthOperator2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthOperator2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthOperatorEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance fourthOperatorEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

/-- Fourth-order normal recovery directly from the actual real elliptic
operator. Passing to its coordinate matrix costs no Hölder norm. -/
theorem exists_uniform_fourth_holder_of_operator
    {α μ N : ℝ} (hα : 0 ≤ α) (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (S : Set E) (u : E → ℝ), ContDiff ℝ 4 u → ∀ k : Fin m,
      ∀ (a : E → E →L[ℝ] E) (A : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
        (R : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
        (B : Fin m × Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = a x) → ‖A‖ ≤ N →
      (∀ x : S, (a x).toLinearMap.IsSymmetric) →
      (∀ i, i ≠ k → ∀ j, j ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value (B (i,j)) x =
        fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative
          (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1))) x) →
      ∀ M Q, 0 ≤ M → 0 ≤ Q →
      (∀ i, i ≠ k → ∀ j, j ≠ k → ‖B (i,j)‖ ≤ M) → (∀ i, ‖R i‖ ≤ Q) →
      (∀ x : S, μ ≤ inner ℝ (a x (EuclideanSpace.single k 1)) (EuclideanSpace.single k 1)) →
      (∀ i (x : S), ellipticTrace a
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1))
          (EuclideanSpace.single k 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (R i) x) →
      HasFourthHolderBound S α u (C*(M+Q)) := by
  obtain ⟨C,hC,hrecover⟩ := exists_uniform_fourth_holder_of_double_tangential
    (I := Fin m) hα hμ hN
  refine ⟨C,hC,?_⟩
  intro S u hu k a A R B hA hAn hsym hB M Q hM hQ hBn hRn hpos heq
  let AM := OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrixCLM A
  have hAM : ‖AM‖ ≤ N := by
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrixCLM A).trans
    exact (mul_le_mul_of_nonneg_right OAI.Analysis.PDE.Schauder.norm_euclideanCoefficientMatrixCLM_le
      (norm_nonneg A)).trans (by simpa only [one_mul] using hAn)
  let AC (p : Fin m × Fin m) := OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Schauder.matrixEntryCLM p.1 p.2) AM
  have hAC (p : Fin m × Fin m) : ‖AC p‖ ≤ N :=
    (matrix_entry_holder_norm_le hα AM p.1 p.2).trans hAM
  have hACval (p : Fin m × Fin m) (x : S) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (AC p) x =
      OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (a x) p.1 p.2 := by
    change OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) p.1 p.2 = _
    rw [hA]
  apply hrecover S u hu k (fun y => OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (a y)) AC R B
    hACval hAC hB M Q hM hQ hBn hRn hpos
  intro i x
  have hq : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)) (EuclideanSpace.single k 1)) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative
      (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 3) (by norm_num) _) (m := 2) (by norm_num) _
  exact (OAI.Analysis.PDE.Schauder.ellipticTrace_eq_nondivergenceOperator a _ hq x (hsym x)).symm.trans (heq i x)

end OAI.Analysis.PDE.Elliptic
