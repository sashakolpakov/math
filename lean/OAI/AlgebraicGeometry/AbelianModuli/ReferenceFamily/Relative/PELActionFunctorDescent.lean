import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PELActionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionFunctorDescent
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.BaseRosatiCondition

/-! # PEL Action Functor Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionFunctorDescent

noncomputable section

/-! Effective descent of actual PEL-action values over noetherian
tests, including the literal Rosati and arithmetic Lie-rank conditions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PELActionBaseChange.ActionBaseChange
variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N M.left)
    {B : Scheme.{0}} (b : B ⟶ M.left) [IsNoetherian B] (C : B.OpenCover)

theorem existsUnique_pel_value_of_functor_matching
    (u : ∀ i, (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj
      (op ((Over.map b).obj (Over.mk (C.f i)))))
    (hmatch : ∀ i j (T : Over B)
      (f : T ⟶ Over.mk (C.f i)) (h : T ⟶ Over.mk (C.f j)),
      (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map ((Over.map b).map f).op (u i) =
        (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map ((Over.map b).map h).op (u j)) :
    ∃! q : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op (Over.mk b)),
      ∀ i, (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).map
        (PELModuli.IntegralModel.ActionCanonicalRestriction.ActionBaseChange.testInclusion b (Over.mk (C.f i))).op q = u i := by
  obtain ⟨q, hq, huniq⟩ := Integral.ActionFunctorDescent.existsUnique_action_of_functor_matching A.abelian b C
    (fun i => (u i).val) (fun i j T f h => congrArg Subtype.val (hmatch i j T f h))
  let v := fun i => (PELModuli.IntegralModel.Relative.PELActionBaseChange.ActionBaseChange.pelEquiv P iotaO M A b (Over.mk (C.f i))).symm (u i)
  have hv (i) : PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A.abelian b (Over.mk (C.f i)) (v i).val = (u i).val :=
    congrArg Subtype.val ((PELModuli.IntegralModel.Relative.PELActionBaseChange.ActionBaseChange.pelEquiv P iotaO M A b (Over.mk (C.f i))).apply_symm_apply (u i))
  have hpull (i) : q.pullback (C.f i) = (v i).val := by
    apply (PELModuli.IntegralModel.Integral.IntegralActionBaseChange.ActionBaseChange.actionEquiv A.abelian b (Over.mk (C.f i))).injective
    exact (PELModuli.IntegralModel.ActionCanonicalRestriction.ActionBaseChange.actionEquiv_pullback A.abelian b (Over.mk (C.f i)) q).symm.trans
      ((hq i).trans (hv i).symm)
  have hRos : ActionData.RosatiConjugation (A.pullback b) q := by
    apply Open.BaseRosatiCondition.rosati_of_open_base_cover C (A.pullback b) q
    intro i
    exact (hpull i).symm ▸ (v i).property.1
  have hLie : PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO (Over.mk (b ≫ M.hom)) (A.abelian.pullback b) q := by
    apply PELModuli.IntegralModel.Open.BaseConditions.integralLieRanks_of_open_base_cover P iotaO (Over.mk (b ≫ M.hom)) C
      (A.abelian.pullback b) q
    intro i
    rw [hpull i]
    exact (v i).property.2
  let w : (PELModuli.IntegralModel.Relative.ActionFunctor.relativePELActionFunctor P iotaO M A).obj (op (Over.mk b)) := ⟨q, hRos, hLie⟩
  refine ⟨w, fun i => Subtype.ext (hq i), fun z hz => ?_⟩
  apply Subtype.ext
  exact huniq z.val (fun i => congrArg Subtype.val (hz i))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELActionFunctorDescent
