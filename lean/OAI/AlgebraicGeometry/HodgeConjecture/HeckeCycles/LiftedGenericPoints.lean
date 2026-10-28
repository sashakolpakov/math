import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PointLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase

/-! # Lifted Generic Points -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedGenericPoints.CM

noncomputable section

/-! The native geometric point lifts give genuine points of the same
characteristic-zero model, first over the Witt fraction field and then
over its algebraic closure as required by TateComparison's point formula. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} {R : M.GoodIntegralReduction q j}
  {hden : Nat.Coprime q M.arithmetic.denominator}
  (X : Over M.arithmetic.base)
  {p : Geometric.PointExt.CM.pointBase (Witt.ArithmeticBase.CM.k (q := q)) ⟶ (Over.pullback R.geometricBase).obj X}
  (l : LiftMap.CM.SmoothPoint.IntegralLift X (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.residueIso (q := q))
    (Witt.ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p)

def genericPoint : Over.mk (Witt.ArithmeticBase.CM.Generic.numberFieldBase j) ⟶ (Over.pullback M.arithmetic.generic).obj X :=
  Over.homMk
    (pullback.lift (Witt.ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map) (Witt.ArithmeticBase.CM.Generic.numberFieldBase j) (by
      rw [Category.assoc, l.overBase]
      exact Witt.ArithmeticBase.CM.Generic.generic_square j hden))
    (pullback.lift_snd _ _ _)

theorem genericPoint_projection :
    (genericPoint X l).left ≫ pullback.fst X.hom M.arithmetic.generic =
      Witt.ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map := pullback.lift_fst _ _ _

abbrev geometricField (q : ℕ) [Fact q.Prime] := AlgebraicClosure (Witt.ArithmeticBase.CM.Generic.F q)

def algebraicClosureBase : Spec (.of (geometricField q)) ⟶ Spec (.of (Witt.ArithmeticBase.CM.Generic.F q)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.Generic.F q) (geometricField q)))

def geometricGenericBase (j : M.QadicChoice q) :
    Spec (.of (geometricField q)) ⟶ Spec (.of M.arithmetic.extension.carrier) :=
  algebraicClosureBase (q := q) ≫ Witt.ArithmeticBase.CM.Generic.numberFieldBase j

def geometricGenericPoint :
    Over.mk (geometricGenericBase j) ⟶ (Over.pullback M.arithmetic.generic).obj X :=
  Over.homMk (algebraicClosureBase (q := q) ≫ (genericPoint X l).left) (by
    rw [Category.assoc, (genericPoint X l).w]
    rfl)

theorem geometricGenericPoint_projection :
    (geometricGenericPoint X l).left ≫ pullback.fst X.hom M.arithmetic.generic =
      algebraicClosureBase (q := q) ≫ Witt.ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map := by
  change (algebraicClosureBase (q := q) ≫ (genericPoint X l).left) ≫ _ = _
  rw [Category.assoc, genericPoint_projection]

theorem smooth_point_has_geometric_generic_lift
    (hs : Smooth X.hom)
    (p : Geometric.PointExt.CM.pointBase (Witt.ArithmeticBase.CM.k (q := q)) ⟶ (Over.pullback R.geometricBase).obj X) :
    ∃ l : LiftMap.CM.SmoothPoint.IntegralLift X (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.residueIso (q := q))
      (Witt.ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p,
      ∃ z : Over.mk (geometricGenericBase j) ⟶ (Over.pullback M.arithmetic.generic).obj X,
        z.left ≫ pullback.fst X.hom M.arithmetic.generic =
          algebraicClosureBase (q := q) ≫ Witt.ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map := by
  let : Smooth X.hom := hs
  let : IsAdicComplete (IsLocalRing.maximalIdeal (Witt.ArithmeticBase.CM.W (q := q))) (Witt.ArithmeticBase.CM.W (q := q)) :=
    Witt.LiftBase.CM.complete q (Witt.ArithmeticBase.CM.k (q := q))
  obtain ⟨l⟩ := LiftMap.CM.SmoothPoint.integralLift_exists X (Witt.ArithmeticBase.CM.W (q := q))
    (Witt.ArithmeticBase.CM.residueIso (q := q)) (Witt.ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase
      (Witt.ArithmeticBase.CM.geometric_square R hden) p
  exact ⟨l, geometricGenericPoint X l, geometricGenericPoint_projection X l⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedGenericPoints.CM
