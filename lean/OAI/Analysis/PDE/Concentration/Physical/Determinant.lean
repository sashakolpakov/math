import OAI.Analysis.PDE.Concentration.Physical.Barrier

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Matrix OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

def spatialDefiningMatrix (d : ℕ) (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Quaternion ℝ) :=
  (OAI.Analysis.Calculus.Current.physicalFiberHessian (1 / 10) a τ q).submatrix (finSuccEquiv d) (finSuccEquiv d)

def spatialBackgroundMatrix (d : ℕ) (τ : ℂ) (q : Option (Fin d) → ℂ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Quaternion ℝ) :=
  (OAI.Analysis.Calculus.Current.physicalBackgroundHessian τ q).submatrix (finSuccEquiv d) (finSuccEquiv d)

theorem spatial_defining_shift (d : ℕ) (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ) (c : ℝ)
    (hc : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Calculus.Current.physicalFiberHessian (1 / 10) a τ q - c • 1)).PosSemidef) :
    (OAI.LinearAlgebra.Moore.complexify (spatialDefiningMatrix d a τ q - c • 1)).PosSemidef := by
  have hh := hc.submatrix (fun i : Fin (d + 1) × Fin 2 => (finSuccEquiv d i.1, i.2))
  convert hh using 1
  ext i j
  simp only [spatialDefiningMatrix, OAI.LinearAlgebra.Moore.complexify, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Equiv.apply_eq_iff_eq]

theorem spatial_background_outer (d : ℕ) (τ : ℂ) (q : Option (Fin d) → ℂ)
    (hY : OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0) :
    ∃ v : Fin (d + 1) → Quaternion ℝ, spatialBackgroundMatrix d τ q = OAI.Analysis.Calculus.Quaternion.outer v := by
  refine ⟨fun i => (2 : ℝ) • OAI.Analysis.Calculus.Current.complexK (star (OAI.Analysis.Calculus.Current.physicalPhaseRow (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) (finSuccEquiv d i))), ?_⟩
  rw [spatialBackgroundMatrix, physical_background_outer τ q hY]
  rfl

theorem spatial_background_trace_lower (d : ℕ) (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ)
    (hY : OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0)
    (hr : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0) :
    1 ≤ ∑ i, (spatialBackgroundMatrix d τ q i i).re := by
  have he := (finSuccEquiv d).sum_comp (fun i => (OAI.Analysis.Calculus.Current.physicalBackgroundHessian τ q i i).re)
  simpa only [spatialBackgroundMatrix, Matrix.submatrix_apply, he] using
    (OAI.Analysis.Calculus.Current.physicalBackgroundHessian_trace_bounds a τ q hY hr).1

/-- The source's quantitative rank-one determinant lower bound, now for the
actual physically normalized defining and background Hessians. -/
theorem physical_input_barrier_determinant (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (τ : ℂ) (q : Option (Fin (n + 1)) → ℂ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a → OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      ∀ (b lam : ℝ), 0 < b → 0 ≤ lam →
      lam * (b * (c / a ^ 2)) ^ (n + 1) ≤
        OAI.LinearAlgebra.Moore.mooreDet (n + 2) (lam • spatialBackgroundMatrix (n + 1) τ q +
          b • spatialDefiningMatrix (n + 1) a τ q) := by
  obtain ⟨c, hc, hbound⟩ := physical_defining_matrix_lower (n + 1)
  refine ⟨c, hc, ?_⟩
  intro a τ q ha ht ht' hr b lam hb hlam
  have hy := (OAI.Analysis.Calculus.Current.fiber_collar_height_bounds a (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) ha
    (by simpa only [OAI.Analysis.Calculus.Current.imaginaryTime_physicalEmbedding] using ht) (hr.trans (by norm_num))).1
  have hY : OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hy).ne'
  simpa only [mul_one] using rank_one_barrier_determinant_lower n
    (spatialBackgroundMatrix (n + 1) τ q) (spatialDefiningMatrix (n + 1) a τ q)
    (spatial_background_outer _ τ q hY) (by positivity : 0 < c / a ^ 2) hb hlam
    (spatial_defining_shift _ a τ q _ (hbound a τ q ha ht ht' hr))
    (spatial_background_trace_lower _ a τ q hY hr)

end OAI.Analysis.PDE.Concentration
