import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Rank
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Locus

/-! # Pivot Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.PivotLocus.Grassmannian

noncomputable section

/-! Relative representing schemes for pivot charts of the original finite presentation matrix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι μ ν : Type u} [Fintype ι] [Fintype μ] [Fintype ν]
variable [DecidableEq ι] [DecidableEq μ] [DecidableEq ν]

variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤)) (a : ι → μ) (b : ι → ν)

def fullMatrixPivotSubfunctor : Subfunctor (yoneda.obj M) :=
  Locus.Grassmannian.matrixPivotSubfunctor M (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A

omit [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν] in
theorem full_matrix_pivot_locus_representable :
    ∃ (U : Over S) (j : U ⟶ M), IsOpenImmersion j.left ∧
      ∃ (Z : Over S) (k : Z ⟶ U), IsClosedImmersion k.left ∧
        ∃ e : yoneda.obj Z ≅ (fullMatrixPivotSubfunctor M A a b).toFunctor,
          e.hom ≫ (fullMatrixPivotSubfunctor M A a b).ι = yoneda.map (k ≫ j) :=
  Locus.Grassmannian.matrix_pivot_locus_representable M (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A

def fullMatrixPivotPointCokernelEquiv {T : Over S}
    (x : (fullMatrixPivotSubfunctor M A a b).toFunctor.obj (Opposite.op T)) :
    ((ν → Γ(T.left, ⊤)) ⧸ (Matrix.toLin' (A.map x.val.left.appTop.hom)).range) ≃ₗ[Γ(T.left, ⊤)]
      ({j : ν // j ∉ Set.range b} → Γ(T.left, ⊤)) := by
  let φ := x.val.left.appTop.hom
  have hu : IsUnit ((A.map φ).submatrix b a).det := by
    have hd : φ (A.submatrix b a).det = ((A.map φ).submatrix b a).det := φ.map_det (A.submatrix b a)
    exact hd ▸ x.property.1
  have hz : PivotCokernel.Grassmannian.fullPivotResidual (A.map φ) a b = 0 := by
    change Cokernel.Grassmannian.pivotResidual ((A.submatrix b a).map φ) ((A.submatrix b id).map φ)
      ((A.submatrix id a).map φ) (A.map φ) = 0
    rw [← Cokernel.Grassmannian.pivotResidual_map φ]
    ext i j
    exact x.property.2 (i, j)
  exact PivotCokernel.Grassmannian.fullMatrixPivotCokernelEquiv (A.map φ) a b hu hz

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.PivotLocus.Grassmannian
