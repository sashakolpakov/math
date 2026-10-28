import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula

/-! # Tate Comparison Point Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEvaluation.CM

noncomputable section

/-! TateComparison's point action is evaluation of its identical integral
endomorphism. Thus its original geometric formula can be used directly
in faithful field descent and proper specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem evaluate_eq_endPoint {T : Over (Spec (.of K))} (f : D.EndK)
    (z : Additive (T ⟶ D.albaneseGroup.X)) :
    PointSpecializationFormula.CM.Points.evaluateAt D.albaneseGroup T f z = D.endPoint f z := by
  apply Additive.toMul.injective
  exact AbelianScheme.TateComparison.End.endSchemeMap_points D.albaneseGroup.X f T z.toMul

variable (hg : D.HasIntegralModelGeometry) {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (t : AbelianScheme.TateComparison.Local.IntegralType s) (f : D.EndK)
  (i : Fin D.componentCount) (x y : Over.mk b ⟶ D.componentGeneric i)

theorem raw_equation_evaluated (h : TateComparisonPointEquation.CM.Raw.RawPointEquation D hg b t f i x y) :
    PointSpecializationFormula.CM.Points.evaluateAt D.albaneseGroup (Over.mk b) f (D.aPoint hg i x - D.aPoint hg i y) =
      ((D.neighbors t b (x ≫ D.componentInclusion i)).map (D.aTotalPoint hg)).sum -
        ((D.neighbors t b (y ≫ D.componentInclusion i)).map (D.aTotalPoint hg)).sum :=
  (evaluate_eq_endPoint D f _).trans h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEvaluation.CM
