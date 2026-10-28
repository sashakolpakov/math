import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Charts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ZeroLocusRecognition
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Ambient Open -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.AmbientOpen.Grassmannian

noncomputable section

/-! Each constructed pivot chart is closed in its specified determinant-open
subscheme of the parameter scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

def matrixPivotAmbientOpen (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) : Over S :=
  Relative.UnitOpen.relativeUnitOpen M (A.submatrix p.2 p.1).det

def matrixPivotAmbientOpenInclusion (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) : matrixPivotAmbientOpen M A p ⟶ M :=
  Relative.UnitOpen.relativeUnitOpenInclusion M (A.submatrix p.2 p.1).det

instance matrixPivotAmbientOpenInclusion_isOpenImmersion (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsOpenImmersion (matrixPivotAmbientOpenInclusion M A p).left :=
  Relative.UnitOpen.relativeUnitOpenInclusion_isOpenImmersion _ _

instance matrixPivotAmbientOpenInclusion_mono (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    Mono (matrixPivotAmbientOpenInclusion M A p) := Over.mono_of_mono_left _

theorem matrixPivotChart_unit (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsUnit ((Charts.Grassmannian.matrixPivotChartInclusion M A p).left.appTop (A.submatrix p.2 p.1).det) := by
  simpa only [Category.id_comp] using (Charts.Grassmannian.matrixPivotChart_condition M A p (𝟙 _)).1

def matrixPivotChartToAmbientOpen (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    Charts.Grassmannian.matrixPivotChart M A p ⟶ matrixPivotAmbientOpen M A p :=
  (Relative.UnitOpen.relativeUnitOpenPointEquiv M (A.submatrix p.2 p.1).det _).symm
    ⟨Charts.Grassmannian.matrixPivotChartInclusion M A p, matrixPivotChart_unit M A p⟩

theorem matrixPivotChartToAmbientOpen_inclusion (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotChartToAmbientOpen M A p ≫ matrixPivotAmbientOpenInclusion M A p =
      Charts.Grassmannian.matrixPivotChartInclusion M A p :=
  congrArg Subtype.val ((Relative.UnitOpen.relativeUnitOpenPointEquiv M (A.submatrix p.2 p.1).det _).apply_symm_apply
    ⟨Charts.Grassmannian.matrixPivotChartInclusion M A p, matrixPivotChart_unit M A p⟩)

instance matrixPivotChartToAmbientOpen_mono (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    Mono (matrixPivotChartToAmbientOpen M A p) := by
  have : Mono (matrixPivotChartToAmbientOpen M A p ≫ matrixPivotAmbientOpenInclusion M A p) := by
    rw [matrixPivotChartToAmbientOpen_inclusion]
    infer_instance
  exact mono_of_mono (matrixPivotChartToAmbientOpen M A p) (matrixPivotAmbientOpenInclusion M A p)

instance matrixPivotChartToAmbientOpen_isClosedImmersion (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsClosedImmersion (matrixPivotChartToAmbientOpen M A p).left := by
  let u := matrixPivotAmbientOpenInclusion M A p
  let s := fun q : ν × μ => u.left.appTop
    (Cokernel.Grassmannian.pivotResidual (A.submatrix p.2 p.1) (A.submatrix p.2 id) (A.submatrix id p.1) A q.1 q.2)
  apply ZeroLocusRecognition.isClosedImmersion_of_section_zero_universal (matrixPivotChartToAmbientOpen M A p) s
  · intro q
    change (matrixPivotChartToAmbientOpen M A p ≫ u).left.appTop
      (Cokernel.Grassmannian.pivotResidual (A.submatrix p.2 p.1) (A.submatrix p.2 id) (A.submatrix id p.1) A q.1 q.2) = 0
    rw [show matrixPivotChartToAmbientOpen M A p ≫ u = Charts.Grassmannian.matrixPivotChartInclusion M A p from
      matrixPivotChartToAmbientOpen_inclusion M A p]
    simpa only [Category.id_comp] using (Charts.Grassmannian.matrixPivotChart_condition M A p (𝟙 _)).2 q
  · intro T x hx
    have hunit : IsUnit ((x ≫ u).left.appTop (A.submatrix p.2 p.1).det) :=
      (Relative.UnitOpen.relativeUnitOpenInclusion_isUnit M (A.submatrix p.2 p.1).det).map x.left.appTop.hom
    have h : Locus.Grassmannian.matrixPivotCondition (A.submatrix p.2 p.1) (A.submatrix p.2 id)
        (A.submatrix id p.1) A (x ≫ u).left.appTop.hom := ⟨hunit, hx⟩
    refine ⟨Charts.Grassmannian.matrixPivotChartLift M A p (x ≫ u) h, ?_⟩
    apply (cancel_mono u).mp
    rw [Category.assoc, matrixPivotChartToAmbientOpen_inclusion]
    exact Charts.Grassmannian.matrixPivotChartLift_inclusion M A p (x ≫ u) h

instance matrixPivotChartInclusion_locallyOfFiniteType (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    LocallyOfFiniteType (Charts.Grassmannian.matrixPivotChartInclusion M A p).left := by
  rw [← matrixPivotChartToAmbientOpen_inclusion]
  change LocallyOfFiniteType ((matrixPivotChartToAmbientOpen M A p).left ≫
    (matrixPivotAmbientOpenInclusion M A p).left)
  infer_instance

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.AmbientOpen.Grassmannian
