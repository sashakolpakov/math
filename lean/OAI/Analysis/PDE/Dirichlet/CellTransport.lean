import OAI.Analysis.PDE.Dirichlet.Moore.Flux
import OAI.Analysis.PDE.Weak.Elliptic.Classical.Divergence
import Mathlib.Analysis.CStarAlgebra.Matrix

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Variational OAI.Analysis.PDE.Weak OAI.Analysis.Calculus.Quaternion

variable {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- The raw coordinates used by the variational solver and the orthonormal
coordinates used by the Moore Hessian describe the same real vector space. -/
def cellEuclideanReindex (e : Fin (m + 1) ≃ I) :
    OAI.Analysis.PDE.Variational.CellCoordinates m ≃L[ℝ] EuclideanSpace ℝ I :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) ↦ ℝ)).symm.trans
    (coordinateReindex e).toContinuousLinearEquiv

@[simp] theorem cellEuclideanReindex_single (e : Fin (m + 1) ≃ I) (i : Fin (m + 1)) :
    cellEuclideanReindex e (Pi.single i 1) = EuclideanSpace.single (e i) 1 := by
  change coordinateReindex e (EuclideanSpace.single i 1) = _
  exact coordinateReindex_single e i 1

omit [DecidableEq I] in
@[simp] theorem coordinateReindex_apply_image (e : Fin (m + 1) ≃ I)
    (v : OAI.Analysis.PDE.Variational.CellVectors m) (i : Fin (m + 1)) : coordinateReindex e v (e i) = v i := by
  change v (e.symm (e i)) = v i
  rw [e.symm_apply_apply]

omit [DecidableEq I] in
@[simp] theorem coordinateReindex_symm_apply_coordinate (e : Fin (m + 1) ≃ I)
    (v : EuclideanSpace ℝ I) (i : Fin (m + 1)) : coordinateReindex e.symm v i = v (e i) := rfl

theorem cellGradient_comp_reindex (e : Fin (m + 1) ≃ I)
    {u : EuclideanSpace ℝ I → ℝ} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hu : DifferentiableAt ℝ u (cellEuclideanReindex e x)) (i : Fin (m + 1)) :
    OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellEuclideanReindex e) x i =
      fderiv ℝ u (cellEuclideanReindex e x) (EuclideanSpace.single (e i) 1) := by
  change fderiv ℝ (u ∘ cellEuclideanReindex e) x (Pi.single i 1) = _
  rw [fderiv_comp x hu (cellEuclideanReindex e).differentiableAt,
    (cellEuclideanReindex e).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    cellEuclideanReindex_single]

/-- Matrix coefficients on the raw coordinate cell, acting on Euclidean
gradient vectors as required by the variational theory. -/
def cellMatrixCoefficient (e : Fin (m + 1) ≃ I)
    (A : EuclideanSpace ℝ I → Matrix I I ℝ) (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
  Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℝ)
    (fun i j ↦ A (cellEuclideanReindex e x) (e i) (e j))

theorem cellMatrixCoefficient_gradient (e : Fin (m + 1) ≃ I)
    (A : EuclideanSpace ℝ I → Matrix I I ℝ)
    {u : EuclideanSpace ℝ I → ℝ} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hu : DifferentiableAt ℝ u (cellEuclideanReindex e x)) :
    cellMatrixCoefficient e A x (OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellEuclideanReindex e) x) =
      coordinateReindex e.symm (indexedFlux A u (cellEuclideanReindex e x)) := by
  apply PiLp.ext
  intro i
  change (∑ j, A (cellEuclideanReindex e x) (e i) (e j) *
      OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellEuclideanReindex e) x j) =
    ∑ j, A (cellEuclideanReindex e x) (e i) j *
      fderiv ℝ u (cellEuclideanReindex e x) (EuclideanSpace.single j 1)
  simp_rw [cellGradient_comp_reindex e hu]
  exact e.sum_comp (fun j ↦ A (cellEuclideanReindex e x) (e i) j *
    fderiv ℝ u (cellEuclideanReindex e x) (EuclideanSpace.single j 1))

theorem classicalDivergence_reindex (e : Fin (m + 1) ≃ I)
    {H : EuclideanSpace ℝ I → EuclideanSpace ℝ I} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hH : DifferentiableAt ℝ H (cellEuclideanReindex e x)) :
    OAI.Analysis.PDE.Weak.classicalDivergence (fun y ↦ coordinateReindex e.symm (H (cellEuclideanReindex e y))) x =
      indexedDivergence H (cellEuclideanReindex e x) := by
  have hi (i : Fin (m + 1)) :
      fderiv ℝ (fun y ↦ coordinateReindex e.symm (H (cellEuclideanReindex e y)) i)
        x (Pi.single i 1) =
      fderiv ℝ (fun y ↦ H y (e i)) (cellEuclideanReindex e x)
        (EuclideanSpace.single (e i) 1) := by
    change fderiv ℝ ((fun y ↦ H y (e i)) ∘ cellEuclideanReindex e) x (Pi.single i 1) = _
    have hh : DifferentiableAt ℝ (fun y ↦ H y (e i)) (cellEuclideanReindex e x) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (e i)).differentiableAt.comp _ hH
    rw [fderiv_comp x hh (cellEuclideanReindex e).differentiableAt,
      (cellEuclideanReindex e).fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      cellEuclideanReindex_single]
  unfold OAI.Analysis.PDE.Weak.classicalDivergence indexedDivergence
  simp_rw [hi]
  exact e.sum_comp (fun i ↦ fderiv ℝ (fun y ↦ H y i) (cellEuclideanReindex e x)
    (EuclideanSpace.single i 1))

end OAI.Analysis.PDE.Dirichlet
