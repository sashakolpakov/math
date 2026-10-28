import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.PivotLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Transitions

/-! # Condition -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Condition.Grassmannian

noncomputable section

/-! The polynomial pivot conditions and their overlap rule after arbitrary coefficient specialization. -/

universe u

variable {R T : Type u} [CommRing R] [CommRing T]
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]

theorem fullMatrixPivotCondition_iff
    (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν) (φ : R →+* T) :
    Locus.Grassmannian.matrixPivotCondition (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A φ ↔
      IsUnit ((A.map φ).submatrix b a).det ∧ PivotCokernel.Grassmannian.fullPivotResidual (A.map φ) a b = 0 := by
  have hd : φ (A.submatrix b a).det = ((A.map φ).submatrix b a).det := φ.map_det (A.submatrix b a)
  have he : PivotCokernel.Grassmannian.fullPivotResidual (A.map φ) a b = (PivotCokernel.Grassmannian.fullPivotResidual A a b).map φ :=
    (Cokernel.Grassmannian.pivotResidual_map φ (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A).symm
  rw [Locus.Grassmannian.matrixPivotCondition, hd, he]
  apply and_congr_right
  intro _
  constructor
  · intro h
    ext i j
    exact h (i, j)
  · intro h p
    exact congrArg (fun B : Matrix ν μ T => B p.1 p.2) h

theorem fullMatrixPivotCondition_transition
    (A : Matrix ν μ R) (a c : ι → μ) (b d : ι → ν) (φ : R →+* T)
    (h : Locus.Grassmannian.matrixPivotCondition (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A φ)
    (hu : IsUnit (φ (A.submatrix d c).det)) :
    Locus.Grassmannian.matrixPivotCondition (A.submatrix d c) (A.submatrix d id) (A.submatrix id c) A φ := by
  obtain ⟨hminor, hres⟩ := (fullMatrixPivotCondition_iff A a b φ).mp h
  apply (fullMatrixPivotCondition_iff A c d φ).mpr
  have hd : φ (A.submatrix d c).det = ((A.map φ).submatrix d c).det := φ.map_det (A.submatrix d c)
  have hu' : IsUnit ((A.map φ).submatrix d c).det := hd ▸ hu
  exact ⟨hu', Transitions.Grassmannian.fullPivotResidual_transition (A.map φ) a c b d hminor hres hu'⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Condition.Grassmannian
