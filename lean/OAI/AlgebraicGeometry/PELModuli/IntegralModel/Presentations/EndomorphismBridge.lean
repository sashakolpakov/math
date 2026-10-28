import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismEquationBridge

/-! # Endomorphism Bridge -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies

noncomputable section

/-! The corrected Presentations endomorphism functor agrees naturally, on every test
scheme, with the actual endomorphism ring of the pulled-back abelian scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem e34_preservesGroupLaw_iff {T : Over S} (f : T ⨯ A.scheme ⟶ A.scheme) :
    HilbertScheme.Presentations.Endomorphisms.Core.PreservesGroupLaw A.scheme f ↔ Group.HomEquations.GroupHomEquations.RespectsGroup A.scheme f := by
  constructor
  · intro h
    exact Group.HomEvaluationCriterion.GroupHomEquations.respectsGroup_of_evaluation A.scheme f
      (fun U t => (h U t).1) (fun U t => (h U t).2)
  · intro h U t
    exact ⟨Group.HomEvaluation.GroupHomEquations.eval_one A.scheme f h t,
      Group.HomEvaluation.GroupHomEquations.eval_mul A.scheme f h t⟩

def e34EndomorphismEquiv (T : Over S) :
    Finite.Actions.GroupEndRing (A.pullback T.hom) ≃
      (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismSubfunctor A.scheme).toFunctor.obj (op T) where
  toFun r := ⟨EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T (r.hom (A.pullback T.hom)),
    (e34_preservesGroupLaw_iff A _).mpr (EndomorphismEquationBridge.EndomorphismFamilies.relativeHom_group_equations A T r)⟩
  invFun f := EndomorphismEquationBridge.EndomorphismFamilies.groupEndOfFamily A T f.val ((e34_preservesGroupLaw_iff A f.val).mp f.property)
  left_inv r := by
    apply EndomorphismHom.EndomorphismFamilies.homInclusion_injective A T
    exact EndomorphismEquationBridge.EndomorphismFamilies.groupEndOfFamily_spec A T _ _
  right_inv f := Subtype.ext (EndomorphismEquationBridge.EndomorphismFamilies.groupEndOfFamily_spec A T _ _)

def e34EndomorphismFunctorIso :
    (EndomorphismFamiliesId.EndomorphismFamilies.endomorphismFunctor A ⋙ forget RingCat) ≅
      (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismSubfunctor A.scheme).toFunctor :=
  NatIso.ofComponents (fun T => (e34EndomorphismEquiv A T.unop).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro r
    apply Subtype.ext
    exact EndomorphismHom.EndomorphismFamilies.relativeHom_restrict A f.unop r)

def e34TupleProjection (n : ℕ) (i : Fin n) :
    HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme n ⟶
      (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismSubfunctor A.scheme).toFunctor where
  app _ := ↾fun f => f i
  naturality _ _ _ := rfl

def e34PrimitiveEndomorphism :
    HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1 ⟶
      (EndomorphismFamiliesId.EndomorphismFamilies.endomorphismFunctor A ⋙ forget RingCat) :=
  e34TupleProjection A 1 0 ≫ (e34EndomorphismFunctorIso A).inv

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EndomorphismBridge.EndomorphismFamilies
