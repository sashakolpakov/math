import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberFormulaTransfer
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeFieldPoints

/-! # Reduction Point Projection -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection.CM

/-! The two canonical residue-fiber identifications preserve the
projection of a reduced point to the original arithmetic source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FiberFormulaTransfer.CM

variable {S T U : Scheme} (r : U ⟶ T) (b : T ⟶ S) (c : U ⟶ S)
  (w : r ≫ b = c) (X : Over S)

theorem factor_inv_projection :
    (BaseChangeSquare.CM.factorIso r b c w X).inv.left ≫ pullback.fst X.hom c =
      pullback.fst (pullback.snd X.hom b) r ≫ pullback.fst X.hom b := by
  let e := BaseChangeSquare.CM.factorIso r b c w X
  let P := pullback.fst (pullback.snd X.hom b) r ≫ pullback.fst X.hom b
  have hh : e.hom.left ≫ P = pullback.fst X.hom c :=
    Source.SquareProjection.CM.factor_hom_projection r b c w X
  have he : e.inv.left ≫ e.hom.left = 𝟙 _ := congrArg Over.Hom.left e.inv_hom_id
  exact (congrArg (e.inv.left ≫ ·) hh.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ P) he).trans (Category.id_comp P)))

theorem fiberPoint_projection {A : Over U} {B : Over T}
    (e : (Over.map r).obj A ≅ B) (Y : Over T) (x : B ⟶ Y) :
    (FiberFormulaTransfer.CM.fiberPoint r A B e Y x).left ≫ pullback.fst Y.hom r = e.hom.left ≫ x.left := by
  exact congrArg Over.Hom.left (FiberFormulaTransfer.CM.fiberPoint_evaluation r A B e Y x)

variable {k : Type} [Field k] (g : Spec (.of k) ⟶ U) (u : Spec (.of k) ⟶ T)
  (wu : g ≫ r = u)

def reducedPoint (x : Over.mk u ⟶ (Over.pullback b).obj X) :
    Over.mk g ⟶ (Over.pullback c).obj X :=
  FiberFormulaTransfer.CM.fiberPoint r (Over.mk g) (Over.mk u) (PrimeFieldPoints.CM.testIso r g u wu)
    ((Over.pullback b).obj X) x ≫ (BaseChangeSquare.CM.factorIso r b c w X).inv

theorem reducedPoint_projection (x : Over.mk u ⟶ (Over.pullback b).obj X) :
    (reducedPoint r b c w X g u wu x).left ≫ pullback.fst X.hom c =
      x.left ≫ pullback.fst X.hom b := by
  let e := PrimeFieldPoints.CM.testIso r g u wu
  let y := FiberFormulaTransfer.CM.fiberPoint r (Over.mk g) (Over.mk u) e ((Over.pullback b).obj X) x
  change (y.left ≫ (BaseChangeSquare.CM.factorIso r b c w X).inv.left) ≫ _ = _
  rw [Category.assoc, factor_inv_projection, ← Category.assoc]
  have hp : y.left ≫ pullback.fst (pullback.snd X.hom b) r = x.left :=
    (fiberPoint_projection r e ((Over.pullback b).obj X) x).trans (Category.id_comp x.left)
  exact congrArg (· ≫ pullback.fst X.hom b) hp

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection.CM.Recovery

/-! Equality of the arithmetic projections identifies the constructed
residue point with the prescribed geometric point in the prime-field
fiber. The second pullback projection is fixed by the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimeFieldPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection.CM

theorem point_eq_of_projection {S T : Scheme} (b : T ⟶ S) (X : Over S) (A : Over T)
    (x y : A ⟶ (Over.pullback b).obj X)
    (h : x.left ≫ pullback.fst X.hom b = y.left ≫ pullback.fst X.hom b) : x = y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact x.w.trans y.w.symm

variable {S T U : Scheme} (r : U ⟶ T) (b : T ⟶ S) (c : U ⟶ S)
  (w : r ≫ b = c) (X : Over S)
  {k : Type} [Field k] (g : Spec (.of k) ⟶ U) (u : Spec (.of k) ⟶ T)
  (wu : g ≫ r = u) (d : Spec (.of k) ⟶ S) (wd : g ≫ c = d)

theorem reducedPoint_recovers (x : Over.mk u ⟶ (Over.pullback b).obj X)
    (p : Geometric.PointExt.CM.pointBase k ⟶ (Over.pullback d).obj X)
    (h : x.left ≫ pullback.fst X.hom b = p.left ≫ pullback.fst X.hom d) :
    reducedPoint r b c w X g u wu x = PrimeFieldPoints.CM.pointEquiv c g d wd X p :=
  point_eq_of_projection c X (Over.mk g) _ _
    ((reducedPoint_projection r b c w X g u wu x).trans
      (h.trans (PrimeFieldPoints.CM.pointEquiv_projection c g d wd X p).symm))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection.CM.Recovery

end

end OAI
