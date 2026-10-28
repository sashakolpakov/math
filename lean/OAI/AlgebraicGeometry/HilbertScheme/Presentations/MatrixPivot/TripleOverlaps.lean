import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Overlaps

/-! # Triple Overlaps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.TripleOverlaps.Grassmannian

noncomputable section

/-! Triple-overlap maps and their cocycle identity for the matrix-pivot atlas. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι μ ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} (M : Over S) (A : Matrix ν μ Γ(M.left, ⊤))

def matrixPivotTripleLift (p q r : Charts.Grassmannian.MatrixPivotIndex ι μ ν) {T : Over S}
    (f : T ⟶ Overlaps.Grassmannian.matrixPivotOverlap M A p q) (g : T ⟶ Overlaps.Grassmannian.matrixPivotOverlap M A p r)
    (h : f ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q = g ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p r) :
    T ⟶ Overlaps.Grassmannian.matrixPivotOverlap M A q r :=
  Overlaps.Grassmannian.matrixPivotOverlapLift M A q r
    ((f ≫ Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q) ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q p) (by
      have he : f ≫ Overlaps.Grassmannian.matrixPivotOverlapParameter M A p q = g ≫ Overlaps.Grassmannian.matrixPivotOverlapParameter M A p r := by
        change f ≫ (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p) =
          g ≫ (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p r ≫ Charts.Grassmannian.matrixPivotChartInclusion M A p)
        rw [← Category.assoc, ← Category.assoc, h]
      change IsUnit (((f ≫ Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q) ≫
        Overlaps.Grassmannian.matrixPivotOverlapParameter M A q p).left.appTop (A.submatrix r.2 r.1).det)
      rw [Category.assoc, Overlaps.Grassmannian.matrixPivotOverlapSwap_parameter, he]
      exact Overlaps.Grassmannian.matrixPivotOverlap_unit M A p r g)

theorem matrixPivotTripleLift_inclusion (p q r : Charts.Grassmannian.MatrixPivotIndex ι μ ν) {T : Over S}
    (f : T ⟶ Overlaps.Grassmannian.matrixPivotOverlap M A p q) (g : T ⟶ Overlaps.Grassmannian.matrixPivotOverlap M A p r)
    (h : f ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q = g ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p r) :
    matrixPivotTripleLift M A p q r f g h ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q r =
      (f ≫ Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q) ≫ Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q p :=
  Overlaps.Grassmannian.matrixPivotOverlapLift_inclusion M A q r _ _

def matrixPivotTripleMap (p q r : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    pullback (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q) (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p r) ⟶
      pullback (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q r) (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q p) :=
  pullback.lift (matrixPivotTripleLift M A p q r (pullback.fst _ _) (pullback.snd _ _) pullback.condition)
    (pullback.fst _ _ ≫ Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q)
    (matrixPivotTripleLift_inclusion M A p q r _ _ _)

theorem matrixPivotTripleMap_snd (p q r : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotTripleMap M A p q r ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q :=
  pullback.lift_snd _ _ _

theorem matrixPivotTripleMap_parameter (p q r : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotTripleMap M A p q r ≫ pullback.fst _ _ ≫ Overlaps.Grassmannian.matrixPivotOverlapParameter M A q r =
      pullback.fst _ _ ≫ Overlaps.Grassmannian.matrixPivotOverlapParameter M A p q := by
  rw [← Category.assoc, matrixPivotTripleMap, pullback.lift_fst]
  change matrixPivotTripleLift M A p q r _ _ _ ≫
    (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A q r ≫ Charts.Grassmannian.matrixPivotChartInclusion M A q) = _
  rw [← Category.assoc, matrixPivotTripleLift_inclusion, Category.assoc]
  change (pullback.fst _ _ ≫ Overlaps.Grassmannian.matrixPivotOverlapSwap M A p q) ≫ Overlaps.Grassmannian.matrixPivotOverlapParameter M A q p = _
  rw [Category.assoc, Overlaps.Grassmannian.matrixPivotOverlapSwap_parameter]

theorem matrixPivotTripleMap_cocycle (p q r : Charts.Grassmannian.MatrixPivotIndex ι μ ν) :
    matrixPivotTripleMap M A p q r ≫ matrixPivotTripleMap M A q r p ≫ matrixPivotTripleMap M A r p q = 𝟙 _ := by
  apply (cancel_mono (pullback.fst (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p q)
    (Overlaps.Grassmannian.matrixPivotOverlapInclusion M A p r) ≫ Overlaps.Grassmannian.matrixPivotOverlapParameter M A p q)).mp
  simp only [Category.assoc, matrixPivotTripleMap_parameter, Category.id_comp]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.TripleOverlaps.Grassmannian
