import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEvaluation

/-! # Hom Evaluation Criterion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEvaluationCriterion.GroupHomEquations

noncomputable section

/-! The two scheme equations are detected on the actual universal
parameterized points of the group and its square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] {T : Over S}

omit [GrpObj G] in
theorem product_parameter_lift (d : G ⨯ G ⟶ G) :
    prod.lift (prod.fst : T ⨯ (G ⨯ G) ⟶ T) (prod.snd ≫ d) = prod.map (𝟙 T) d := by
  apply prod.hom_ext
  · simp only [prod.lift_fst, prod.map_fst, Category.comp_id]
  · simp only [prod.lift_snd, prod.map_snd]

theorem respectsGroup_of_evaluation (f : T ⨯ G ⟶ G)
    (hone : ∀ (W : Over S) (b : W ⟶ T), prod.lift b (1 : W ⟶ G) ≫ f = 1)
    (hmul : ∀ (W : Over S) (b : W ⟶ T) (x y : W ⟶ G),
      prod.lift b (x * y) ≫ f = (prod.lift b x ≫ f) * (prod.lift b y ≫ f)) :
    HomEquations.GroupHomEquations.RespectsGroup G f := by
  refine ⟨hone T (𝟙 T), ?_⟩
  have hm := hmul (T ⨯ (G ⨯ G)) prod.fst (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd)
  rw [← MonObj.comp_mul, product_parameter_lift, product_parameter_lift, product_parameter_lift] at hm
  exact hm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEvaluationCriterion.GroupHomEquations
