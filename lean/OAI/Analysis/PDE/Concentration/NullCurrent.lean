import OAI.Analysis.PDE.Concentration.NullCoordinates
import OAI.Analysis.PDE.Concentration.CurrentTransform

noncomputable section
open scoped ContDiff
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion

def nullMatrixReindex (d : ℕ) : (OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) →L[ℝ]
    (Fin (d + 2) → Fin (d + 2) → Quaternion ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (ContinuousLinearMap.proj (nullIndexEquiv d j) : (OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) →L[ℝ] Quaternion ℝ).comp
      (ContinuousLinearMap.proj (nullIndexEquiv d i) :
        (OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) →L[ℝ] (OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ))

@[simp] theorem nullMatrixReindex_apply (d : ℕ) (M : OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ)
    (i j : Fin (d + 2)) : nullMatrixReindex d M i j = M (nullIndexEquiv d i) (nullIndexEquiv d j) := rfl

def nullIndexedCurrent {d : ℕ} (A : OAI.Analysis.Calculus.Current.CurrentSpace d → OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3 → Fin (d + 2) → Fin (d + 2) → Quaternion ℝ :=
  nullMatrixReindex d ∘ A ∘ nullCoordinateProjection d

theorem contDiffAt_nullIndexedCurrent {d : ℕ} {N : ℕ∞ω}
    {A : OAI.Analysis.Calculus.Current.CurrentSpace d → OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3}
    (hA : ContDiffAt ℝ N A (nullCoordinateProjection d x)) :
    ContDiffAt ℝ N (nullIndexedCurrent A) x :=
  (nullMatrixReindex d).contDiff.contDiffAt.comp x
    (hA.comp x (nullCoordinateProjection d).contDiff.contDiffAt)

theorem fderiv_nullIndexedCurrent_coordinate {d : ℕ}
    {A : OAI.Analysis.Calculus.Current.CurrentSpace d → OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3}
    (hA : DifferentiableAt ℝ A (nullCoordinateProjection d x)) (i : Fin (d + 2)) (α : Fin 3) :
    fderiv ℝ (nullIndexedCurrent A) x (OAI.Analysis.PDE.Dirichlet.coordinateVector (i, α)) =
      nullMatrixReindex d (fderiv ℝ A (nullCoordinateProjection d x)
        (OAI.Analysis.Calculus.Current.currentDirection (nullIndexEquiv d i, α))) := by
  have hd := (nullMatrixReindex d).hasFDerivAt.comp x
    (hA.hasFDerivAt.comp x (nullCoordinateProjection d).hasFDerivAt)
  have he : fderiv ℝ (nullIndexedCurrent A) x =
      (nullMatrixReindex d).comp ((fderiv ℝ A (nullCoordinateProjection d x)).comp
        (nullCoordinateProjection d)) := hd.fderiv
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, nullCoordinateProjection_coordinateVector]

theorem strongDivergence_nullMatrixReindex (d : ℕ) (e : Fin 3 → Quaternion ℝ)
    (D : OAI.Analysis.Calculus.Current.Index d × Fin 3 → OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) (b : Fin (d + 2)) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p : Fin (d + 2) × Fin 3 =>
      nullMatrixReindex d (D (nullIndexEquiv d p.1, p.2))) b =
        OAI.Analysis.Calculus.Quaternion.strongDivergence e D (nullIndexEquiv d b) := by
  unfold OAI.Analysis.Calculus.Quaternion.strongDivergence
  simp only [nullMatrixReindex_apply]
  exact (nullIndexEquiv d).sum_comp (fun i =>
    ∑ α, star (e α) * D (i, α) i (nullIndexEquiv d b))

theorem nullIndexedCurrent_strongDivergence_zero {d : ℕ} (e : Fin 3 → Quaternion ℝ)
    {A : OAI.Analysis.Calculus.Current.CurrentSpace d → OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3}
    (hA : DifferentiableAt ℝ A (nullCoordinateProjection d x))
    (hdiv : ∀ b, OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p =>
      fderiv ℝ A (nullCoordinateProjection d x) (OAI.Analysis.Calculus.Current.currentDirection p)) b = 0)
    (b : Fin (d + 2)) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ (nullIndexedCurrent A) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 := by
  have he (p : Fin (d + 2) × Fin 3) := fderiv_nullIndexedCurrent_coordinate hA p.1 p.2
  simp only [Prod.mk.eta] at he
  simp_rw [he]
  exact (strongDivergence_nullMatrixReindex d e
    (fun p => fderiv ℝ A (nullCoordinateProjection d x) (OAI.Analysis.Calculus.Current.currentDirection p)) b).trans
    (hdiv _)

end OAI.Analysis.PDE.Concentration
