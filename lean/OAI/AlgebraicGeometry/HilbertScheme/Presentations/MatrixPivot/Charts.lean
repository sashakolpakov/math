import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Condition
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.UnitOpen
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-! # Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Charts.Grassmannian

noncomputable section

/-! Chosen, already constructed pivot charts and their concrete universal maps into the matrix parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

abbrev MatrixPivotIndex (ι μ ν : Type u) := (ι ↪ μ) × (ι ↪ ν)

structure MatrixPivotChartModel (p : MatrixPivotIndex ι μ ν) where
  carrier : Over S
  inclusion : carrier ⟶ M
  mono : Mono inclusion
  surjectiveOnStalks : SurjectiveOnStalks inclusion.left
  representation : yoneda.obj carrier ≅ (PivotLocus.Grassmannian.fullMatrixPivotSubfunctor M A p.1 p.2).toFunctor
  inclusion_eq : representation.hom ≫ (PivotLocus.Grassmannian.fullMatrixPivotSubfunctor M A p.1 p.2).ι = yoneda.map inclusion

def matrixPivotChartModel (p : MatrixPivotIndex ι μ ν) : MatrixPivotChartModel M A p := by
  apply Classical.choice
  obtain ⟨U, j, hj, Z, k, hk, e, he⟩ := PivotLocus.Grassmannian.full_matrix_pivot_locus_representable M A p.1 p.2
  let := hj
  let := hk
  have : Mono j := Over.mono_of_mono_left j
  have : Mono k := Over.mono_of_mono_left k
  exact ⟨⟨Z, k ≫ j, inferInstance, by
    change SurjectiveOnStalks (k.left ≫ j.left)
    infer_instance, e, he⟩⟩

def matrixPivotChart (p : MatrixPivotIndex ι μ ν) : Over S := (matrixPivotChartModel M A p).carrier

def matrixPivotChartInclusion (p : MatrixPivotIndex ι μ ν) : matrixPivotChart M A p ⟶ M :=
  (matrixPivotChartModel M A p).inclusion

instance matrixPivotChartInclusion_mono (p : MatrixPivotIndex ι μ ν) :
    Mono (matrixPivotChartInclusion M A p) := (matrixPivotChartModel M A p).mono

instance matrixPivotChartInclusion_surjectiveOnStalks (p : MatrixPivotIndex ι μ ν) :
    SurjectiveOnStalks (matrixPivotChartInclusion M A p).left := (matrixPivotChartModel M A p).surjectiveOnStalks

def matrixPivotChartPointEquiv (p : MatrixPivotIndex ι μ ν) (T : Over S) :
    (T ⟶ matrixPivotChart M A p) ≃ (PivotLocus.Grassmannian.fullMatrixPivotSubfunctor M A p.1 p.2).obj (Opposite.op T) :=
  ((matrixPivotChartModel M A p).representation.app (Opposite.op T)).toEquiv

theorem matrixPivotChartPointEquiv_val (p : MatrixPivotIndex ι μ ν) {T : Over S}
    (y : T ⟶ matrixPivotChart M A p) :
    (matrixPivotChartPointEquiv M A p T y).val = y ≫ matrixPivotChartInclusion M A p := by
  change (((matrixPivotChartModel M A p).representation.hom.app (Opposite.op T)) y).val =
    y ≫ (matrixPivotChartModel M A p).inclusion
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (matrixPivotChartModel M A p).inclusion_eq (Opposite.op T)) y

theorem matrixPivotChart_condition (p : MatrixPivotIndex ι μ ν) {T : Over S}
    (y : T ⟶ matrixPivotChart M A p) :
    Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id) (A.submatrix id p.1) A
      (y ≫ matrixPivotChartInclusion M A p).left.appTop.hom := by
  have h := (matrixPivotChartPointEquiv M A p T y).property
  change Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id) (A.submatrix id p.1) A
    (matrixPivotChartPointEquiv M A p T y).val.left.appTop.hom at h
  rwa [matrixPivotChartPointEquiv_val] at h

def matrixPivotChartLift (p : MatrixPivotIndex ι μ ν) {T : Over S} (x : T ⟶ M)
    (hx : Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id) (A.submatrix id p.1) A
      x.left.appTop.hom) : T ⟶ matrixPivotChart M A p :=
  (matrixPivotChartPointEquiv M A p T).symm ⟨x, hx⟩

theorem matrixPivotChartLift_inclusion (p : MatrixPivotIndex ι μ ν) {T : Over S} (x : T ⟶ M)
    (hx : Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id) (A.submatrix id p.1) A
      x.left.appTop.hom) :
    matrixPivotChartLift M A p x hx ≫ matrixPivotChartInclusion M A p = x := by
  rw [← matrixPivotChartPointEquiv_val]
  exact congrArg Subtype.val ((matrixPivotChartPointEquiv M A p T).apply_symm_apply ⟨x, hx⟩)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Charts.Grassmannian
