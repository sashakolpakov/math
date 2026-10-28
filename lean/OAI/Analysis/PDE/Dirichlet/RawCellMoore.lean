import OAI.Analysis.PDE.Dirichlet.Linear.CoefficientBounds

open Set Filter InnerProductSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Variational OAI.Analysis.PDE.Weak OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Green

def rawCellEuclidean (m : ℕ) : OAI.Analysis.PDE.Variational.CellCoordinates m ≃L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
  cellEuclideanReindex (Equiv.refl (Fin (m + 1)))

@[simp] theorem rawCellEuclidean_apply {m : ℕ} (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    rawCellEuclidean m x = WithLp.toLp 2 x := rfl

theorem cellGradient_comp_raw {m : ℕ} {u : OAI.Analysis.PDE.Variational.CellVectors m → ℝ} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hu : DifferentiableAt ℝ u (rawCellEuclidean m x)) :
    OAI.Analysis.PDE.Variational.cellGradient (u ∘ rawCellEuclidean m) x = gradient u (rawCellEuclidean m x) := by
  apply PiLp.ext
  intro i
  have hi : OAI.Analysis.PDE.Variational.cellGradient (u ∘ rawCellEuclidean m) x i =
      fderiv ℝ u (rawCellEuclidean m x) (EuclideanSpace.single i 1) :=
    cellGradient_comp_reindex (Equiv.refl (Fin (m + 1))) hu i
  rw [hi]
  change fderiv ℝ u (rawCellEuclidean m x) (EuclideanSpace.single i 1) = _
  simpa only [EuclideanSpace.inner_single_right, mul_one, one_mul,
    starRingEnd_apply, star_trivial] using
    (inner_gradient_left (f := u) (x := rawCellEuclidean m x)
      (y := EuclideanSpace.single i 1)).symm

theorem classicalDivergence_comp_raw {m : ℕ}
    {H : OAI.Analysis.PDE.Variational.CellVectors m → OAI.Analysis.PDE.Variational.CellVectors m} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hH : DifferentiableAt ℝ H (rawCellEuclidean m x)) :
    OAI.Analysis.PDE.Weak.classicalDivergence (H ∘ rawCellEuclidean m) x = indexedDivergence H (rawCellEuclidean m x) := by
  have hh := classicalDivergence_reindex (Equiv.refl (Fin (m + 1))) hH
  have he : (fun y ↦ coordinateReindex (Equiv.refl (Fin (m + 1))).symm
      (H (cellEuclideanReindex (Equiv.refl (Fin (m + 1))) y))) = H ∘ rawCellEuclidean m := rfl
  rw [he] at hh
  exact hh

section Coefficients
variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def cellPhysicalEquiv (L : OAI.Analysis.PDE.Variational.CellVectors m ≃L[ℝ] F) : OAI.Analysis.PDE.Variational.CellCoordinates m ≃L[ℝ] F :=
  (rawCellEuclidean m).trans L

def rawCellCoefficient (L : OAI.Analysis.PDE.Variational.CellVectors m ≃L[ℝ] F) (A : F → F →L[ℝ] F)
    (x : OAI.Analysis.PDE.Variational.CellCoordinates m) : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m :=
  linearPullbackCoefficient L A (rawCellEuclidean m x)

theorem contDiff_rawCellCoefficient (L : OAI.Analysis.PDE.Variational.CellVectors m ≃L[ℝ] F)
    {A : F → F →L[ℝ] F} {k : ℕ∞ω} (hA : ContDiff ℝ k A) :
    ContDiff ℝ k (rawCellCoefficient L A) :=
  (contDiff_linearPullbackCoefficient L hA).comp (rawCellEuclidean m).contDiff

theorem rawCellCoefficient_flux (L : OAI.Analysis.PDE.Variational.CellVectors m ≃L[ℝ] F)
    (A : F → F →L[ℝ] F) {u : F → ℝ} {x : OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hu : DifferentiableAt ℝ u (cellPhysicalEquiv L x)) :
    rawCellCoefficient L A x (OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellPhysicalEquiv L) x) =
      L.symm (A (cellPhysicalEquiv L x) (gradient u (cellPhysicalEquiv L x))) := by
  have hcomp : u ∘ cellPhysicalEquiv L = (u ∘ L) ∘ rawCellEuclidean m := rfl
  have hu' : DifferentiableAt ℝ u (L (rawCellEuclidean m x)) := hu
  have huL : DifferentiableAt ℝ (u ∘ L) (rawCellEuclidean m x) :=
    hu'.comp _ L.differentiableAt
  rw [hcomp, cellGradient_comp_raw huL]
  exact linearPullbackCoefficient_flux L A hu

theorem rawCellCoefficient_elliptic (L : OAI.Analysis.PDE.Variational.CellVectors m ≃L[ℝ] F)
    (A : F → F →L[ℝ] F) {x : OAI.Analysis.PDE.Variational.CellCoordinates m} {lam : ℝ} (hlam : 0 ≤ lam)
    (hell : ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A (cellPhysicalEquiv L x) z) z)
    (v : OAI.Analysis.PDE.Variational.CellVectors m) :
    (lam / (‖L.toContinuousLinearMap‖ + 1) ^ 2) * ‖v‖ ^ 2 ≤
      inner ℝ (rawCellCoefficient L A x v) v :=
  linearPullbackCoefficient_elliptic L A hlam hell v

end Coefficients

/-- The complete raw-cell to physical-coordinate identity for the actual
Moore operator. Both the coordinate norm change and the arbitrary lattice
linear map have been accounted for. -/
theorem rawCell_moore_flux_divergence {m n : ℕ}
    (L : OAI.Analysis.PDE.Variational.CellVectors m ≃L[ℝ] CoordinateSpace n 4)
    {ψ u : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ) (hu : ContDiff ℝ 2 u)
    (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
    OAI.Analysis.PDE.Weak.classicalDivergence (fun y ↦ rawCellCoefficient L
      (fun z ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
        (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z))) y
      (OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellPhysicalEquiv L) y)) x =
        mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u (cellPhysicalEquiv L x) := by
  let A := fun z ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z)
  let H := fun y : OAI.Analysis.PDE.Variational.CellVectors m ↦ L.symm (indexedFlux A u (L y))
  have hA : ContDiff ℝ 1 A :=
    (contDiff_mooreRealMatrix n 1).comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hψ)
  have hH : ContDiff ℝ 1 H :=
    L.symm.contDiff.comp ((contDiff_indexedFlux hA hu).comp L.contDiff)
  have he : (fun y ↦ rawCellCoefficient L
      (fun z ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ) (A z)) y
        (OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellPhysicalEquiv L) y)) = H ∘ rawCellEuclidean m := by
    funext y
    rw [rawCellCoefficient_flux L _ (hu.differentiable (by norm_num) _),
      ← indexedFlux_eq_matrix_gradient A u]
    rfl
  change OAI.Analysis.PDE.Weak.classicalDivergence (fun y ↦ rawCellCoefficient L
      (fun z ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ) (A z)) y
        (OAI.Analysis.PDE.Variational.cellGradient (u ∘ cellPhysicalEquiv L) y)) x = _
  rw [he, classicalDivergence_comp_raw (hH.differentiable one_ne_zero _)]
  change indexedDivergence (fun y ↦ L.symm (indexedFlux A u (L y))) _ = _
  rw [indexedDivergence_linear_pullback L
    ((contDiff_indexedFlux hA hu).differentiable one_ne_zero _)]
  exact moore_flux_divergence hψ hu _

theorem moore_linearization_of_rawCell_equation {m n : ℕ}
    (L : OAI.Analysis.PDE.Variational.CellVectors m ≃L[ℝ] CoordinateSpace n 4)
    {ψ : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ)
    {v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ} (hv : ContDiff ℝ 2 v) {x : OAI.Analysis.PDE.Variational.CellCoordinates m} {g : ℝ}
    (heq : -OAI.Analysis.PDE.Weak.classicalDivergence (fun y ↦ rawCellCoefficient L
      (fun z ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
        (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z))) y (OAI.Analysis.PDE.Variational.cellGradient v y)) x = -g) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ)
      (v ∘ (cellPhysicalEquiv L).symm) (cellPhysicalEquiv L x) = g := by
  have hu := hv.comp (cellPhysicalEquiv L).symm.contDiff
  have hc : (v ∘ (cellPhysicalEquiv L).symm) ∘ cellPhysicalEquiv L = v := by
    funext y
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  have h := rawCell_moore_flux_divergence L hψ hu x
  rw [hc] at h
  exact h.symm.trans (neg_injective heq)

end OAI.Analysis.PDE.Dirichlet
