import OAI.Analysis.PDE.Schauder.Dirichlet.EuclideanCoefficient
import OAI.Analysis.PDE.Elliptic.DirichletChartHolderFields

open InnerProductSpace Set
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance euclideanHolderMatrixGroup : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance euclideanHolderMatrixSpace : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))
local instance euclideanHolderMatrixMapGroup :
    NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] (Fin m → Fin m → ℝ)))

theorem norm_euclideanCoefficientMatrix_le (A : E →L[ℝ] E) :
    ‖euclideanCoefficientMatrix A‖ ≤ ‖A‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg A)).mpr
  intro i j
  change ‖inner ℝ (A (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)‖ ≤ ‖A‖
  calc
    _ ≤ ‖A (EuclideanSpace.single i 1)‖ * ‖(EuclideanSpace.single j 1 : E)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖A‖ := by simpa using A.le_opNorm (EuclideanSpace.single i 1)

def euclideanCoefficientMatrixCLM : (E →L[ℝ] E) →L[ℝ] Matrix (Fin m) (Fin m) ℝ :=
  euclideanCoefficientMatrix.mkContinuous 1 (fun A => by simpa using norm_euclideanCoefficientMatrix_le A)

theorem norm_euclideanCoefficientMatrixCLM_le : ‖(euclideanCoefficientMatrixCLM (m := m))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖euclideanCoefficientMatrix A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using norm_euclideanCoefficientMatrix_le A

theorem norm_euclideanCoefficientHolder_le {α : ℝ} (B : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] E) α) :
    ‖OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM euclideanCoefficientMatrixCLM B‖ ≤ ‖B‖ := by
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le euclideanCoefficientMatrixCLM B).trans
    ((mul_le_mul_of_nonneg_right norm_euclideanCoefficientMatrixCLM_le (norm_nonneg B)).trans_eq (one_mul _))

/-- Actual matrix and vector fields usable by the flat-boundary theorem,
with a common bound chosen before the physical coefficient field. -/
theorem exists_chart_matrix_holder_fields
    (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 2 P)
    {S : Set E} (hne : S.Nonempty) (hS : IsCompact S) (hSc : Convex ℝ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ A : E → E →L[ℝ] E, Continuous A → ∀ N : ℝ, 0 ≤ N →
      (∀ x ∈ S, ‖A (G x)‖ ≤ N) →
      (∀ x ∈ S, ∀ y ∈ S, ‖A (G x)-A (G y)‖ ≤ N * ‖G x-G y‖^α) →
      ∃ (B : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α) (b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α),
        ‖B‖ ≤ C*N ∧ ‖b‖ ≤ C*N ∧
        (∀ x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = euclideanCoefficientMatrix
          (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x)))) ∧
        (∀ x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value b x = OAI.Analysis.PDE.Elliptic.inverseChartDrift A G P x) := by
  obtain ⟨C, hC, hfields⟩ := OAI.Analysis.PDE.Elliptic.exists_chart_holder_fields G P hG hP hne hS hSc hdiam hα hα1
  refine ⟨C, hC, ?_⟩
  intro A hA N hN hAn hAh
  obtain ⟨B, b, hBn, hbn, hB, hb⟩ := hfields A hA N hN hAn hAh
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM euclideanCoefficientMatrixCLM B, b,
    (norm_euclideanCoefficientHolder_le B).trans hBn, hbn, ?_, hb⟩
  intro x hx
  change euclideanCoefficientMatrix (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x) = _
  rw [hB x hx]

end OAI.Analysis.PDE.Schauder
