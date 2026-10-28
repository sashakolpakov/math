import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusComparison

/-! # Point Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM

noncomputable section

/-! A genuine algebraic-endomorphism ring acts on every point functor.
The algebraic and functorial Frobenius actions agree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointSpecializationFormula.CM.Points OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

variable {S : Scheme} (G : CommGrp (Over S)) (T : Over S)

def action : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd G.X →+* AddMonoid.End (Additive (T ⟶ G.X)) :=
  (PointSpecializationFormula.CM.Points.evaluateAt G T).comp (EndomorphismComparison.CM.integralEquiv G.X).symm.toRingHom

theorem action_integral (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) :
    action G T (EndomorphismComparison.CM.integralEquiv G.X f) = PointSpecializationFormula.CM.Points.evaluateAt G T f :=
  congrArg (PointSpecializationFormula.CM.Points.evaluateAt G T) ((EndomorphismComparison.CM.integralEquiv G.X).symm_apply_apply f)

theorem action_apply (f : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd G.X) (p : T ⟶ G.X) :
    (action G T f (Additive.ofMul p)).toMul = p ≫ f.toMul.hom.hom := by
  have h := congrArg (fun z : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd G.X => z.toMul.hom.hom)
    ((EndomorphismComparison.CM.integralEquiv G.X).apply_symm_apply f)
  exact (AbelianScheme.TateComparison.End.endSchemeMap_points G.X ((EndomorphismComparison.CM.integralEquiv G.X).symm f) T p).trans
    (congrArg (p ≫ ·) h)

variable {k : Type} [Field k] [Fintype k]
  (A : CommGrp (Over (Spec (.of k)))) (U : Over (Spec (.of k)))

theorem action_frobenius :
    action A U (FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A.X) = PointSpecializationFormula.CM.Points.evaluateAt A U (Finite.FieldFrobenius.CM.integralFrobenius A) :=
  (congrArg (action A U) (FrobeniusComparison.CM.integralEquiv_frobenius A).symm).trans
    (action_integral A U (Finite.FieldFrobenius.CM.integralFrobenius A))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM
