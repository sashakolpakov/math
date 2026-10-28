import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Charts
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Overlaps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Overlaps.Grassmannian

noncomputable section

/-! Determinant-open overlaps and canonical transition maps for the constructed matrix-pivot atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

def matrixPivotOverlapSection (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) : Γ((Charts.Grassmannian.matrixPivotChart M A p).left, ⊤) :=
  (Charts.Grassmannian.matrixPivotChartInclusion M A p).left.appTop (A.submatrix q.2 q.1).det

def matrixPivotOverlap (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) : Over S :=
  Relative.UnitOpen.relativeUnitOpen (Charts.Grassmannian.matrixPivotChart M A p) (matrixPivotOverlapSection M A p q)

def matrixPivotOverlapInclusion (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) : matrixPivotOverlap M A p q ⟶ Charts.Grassmannian.matrixPivotChart M A p :=
  Relative.UnitOpen.relativeUnitOpenInclusion (Charts.Grassmannian.matrixPivotChart M A p) (matrixPivotOverlapSection M A p q)

instance matrixPivotOverlapInclusion_isOpenImmersion (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsOpenImmersion (matrixPivotOverlapInclusion M A p q).left :=
  inferInstanceAs (IsOpenImmersion (Relative.UnitOpen.relativeUnitOpenInclusion (Charts.Grassmannian.matrixPivotChart M A p)
    (matrixPivotOverlapSection M A p q)).left)

instance matrixPivotOverlapInclusion_mono (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    Mono (matrixPivotOverlapInclusion M A p q) := Over.mono_of_mono_left _

def matrixPivotOverlapParameter (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) : matrixPivotOverlap M A p q ⟶ M :=
  matrixPivotOverlapInclusion M A p q ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p

instance matrixPivotOverlapParameter_mono (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    Mono (matrixPivotOverlapParameter M A p q) := inferInstanceAs
  (Mono (matrixPivotOverlapInclusion M A p q ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p))

theorem matrixPivotOverlap_unit (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) {T : Over S}
    (y : T ⟶ matrixPivotOverlap M A p q) :
    IsUnit ((y ≫ matrixPivotOverlapParameter M A p q).left.appTop (A.submatrix q.2 q.1).det) :=
  (Relative.UnitOpen.relativeUnitOpenInclusion_isUnit (Charts.Grassmannian.matrixPivotChart M A p)
    (matrixPivotOverlapSection M A p q)).map y.left.appTop.hom

def matrixPivotOverlapLift (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) {T : Over S}
    (f : T ⟶ Charts.Grassmannian.matrixPivotChart M A p)
    (h : IsUnit ((f ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p).left.appTop (A.submatrix q.2 q.1).det)) :
    T ⟶ matrixPivotOverlap M A p q :=
  (Relative.UnitOpen.relativeUnitOpenPointEquiv (Charts.Grassmannian.matrixPivotChart M A p) (matrixPivotOverlapSection M A p q) T).symm ⟨f, h⟩

theorem matrixPivotOverlapLift_inclusion (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) {T : Over S}
    (f : T ⟶ Charts.Grassmannian.matrixPivotChart M A p)
    (h : IsUnit ((f ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p).left.appTop (A.submatrix q.2 q.1).det)) :
    matrixPivotOverlapLift M A p q f h ≫ matrixPivotOverlapInclusion M A p q = f :=
  congrArg Subtype.val ((Relative.UnitOpen.relativeUnitOpenPointEquiv (Charts.Grassmannian.matrixPivotChart M A p)
    (matrixPivotOverlapSection M A p q) T).apply_symm_apply ⟨f, h⟩)

def matrixPivotOverlapToSecond (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotOverlap M A p q ⟶ Charts.Grassmannian.matrixPivotChart M A q :=
  Charts.Grassmannian.matrixPivotChartLift M A q (matrixPivotOverlapParameter M A p q) (by
    apply Condition.Grassmannian.fullMatrixPivotCondition_transition A p.1 q.1 p.2 q.2 _
      (Charts.Grassmannian.matrixPivotChart_condition M A p (matrixPivotOverlapInclusion M A p q))
    change IsUnit ((matrixPivotOverlapParameter M A p q).left.appTop (A.submatrix q.2 q.1).det)
    simpa only [Category.id_comp] using matrixPivotOverlap_unit M A p q (𝟙 _))

theorem matrixPivotOverlapToSecond_inclusion (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotOverlapToSecond M A p q ≫ Charts.Grassmannian.matrixPivotChartInclusion M A q = matrixPivotOverlapParameter M A p q :=
  Charts.Grassmannian.matrixPivotChartLift_inclusion M A q _ _

def matrixPivotOverlapSwap (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotOverlap M A p q ⟶ matrixPivotOverlap M A q p :=
  matrixPivotOverlapLift M A q p (matrixPivotOverlapToSecond M A p q) (by
    rw [matrixPivotOverlapToSecond_inclusion]
    exact (Charts.Grassmannian.matrixPivotChart_condition M A p (matrixPivotOverlapInclusion M A p q)).1)

theorem matrixPivotOverlapSwap_parameter (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotOverlapSwap M A p q ≫ matrixPivotOverlapParameter M A q p = matrixPivotOverlapParameter M A p q := by
  change matrixPivotOverlapSwap M A p q ≫
    (matrixPivotOverlapInclusion M A q p ≫ Charts.Grassmannian.matrixPivotChartInclusion M A q) = _
  rw [← Category.assoc, matrixPivotOverlapSwap, matrixPivotOverlapLift_inclusion, matrixPivotOverlapToSecond_inclusion]

theorem matrixPivotOverlapSwap_inverse (p q : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotOverlapSwap M A p q ≫ matrixPivotOverlapSwap M A q p = 𝟙 _ := by
  apply (cancel_mono (matrixPivotOverlapParameter M A p q)).mp
  rw [Category.assoc, matrixPivotOverlapSwap_parameter, matrixPivotOverlapSwap_parameter, Category.id_comp]

theorem matrixPivotOverlapSwap_self (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotOverlapSwap M A p p = 𝟙 _ := by
  apply (cancel_mono (matrixPivotOverlapParameter M A p p)).mp
  rw [matrixPivotOverlapSwap_parameter, Category.id_comp]

instance matrixPivotOverlapInclusion_self_isIso (p : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    IsIso (matrixPivotOverlapInclusion M A p p) := by
  have hs : IsUnit (matrixPivotOverlapSection M A p p) := by
    change IsUnit ((Charts.Grassmannian.matrixPivotChartInclusion M A p).left.appTop.hom (A.submatrix p.2 p.1).det)
    simpa only [Category.id_comp] using (Charts.Grassmannian.matrixPivotChart_condition M A p (𝟙 _)).1
  apply (isIso_iff_of_reflects_iso _ (Over.forget S)).mp
  change IsIso (matrixPivotOverlapInclusion M A p p).left
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  change ((Charts.Grassmannian.matrixPivotChart M A p).left.basicOpen (matrixPivotOverlapSection M A p p)).ι.opensRange = ⊤
  rw [Scheme.Opens.opensRange_ι]
  exact (Charts.Grassmannian.matrixPivotChart M A p).left.basicOpen_of_isUnit hs

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Overlaps.Grassmannian
