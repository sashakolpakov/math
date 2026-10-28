import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEquations

/-! # Hom Evaluation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEvaluation.GroupHomEquations

noncomputable section

/-! The closed group equations act by genuine group homomorphisms on
every parameterized family of points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]
  {T W : Over S} (f : T ⨯ G ⟶ G) (hf : HomEquations.GroupHomEquations.RespectsGroup G f) (b : W ⟶ T)

include hf in
theorem eval_one : prod.lift b (1 : W ⟶ G) ≫ f = 1 := by
  have hb : prod.lift b (1 : W ⟶ G) = b ≫ HomEquations.GroupHomEquations.unitAxis G T := by
    simp only [HomEquations.GroupHomEquations.unitAxis, prod.comp_lift, Category.comp_id, MonObj.comp_one]
  rw [hb, Category.assoc, hf.1, MonObj.comp_one]

include hf in
theorem eval_mul (x y : W ⟶ G) :
    prod.lift b (x * y) ≫ f = (prod.lift b x ≫ f) * (prod.lift b y ≫ f) := by
  let l : W ⟶ T ⨯ (G ⨯ G) := prod.lift b (prod.lift x y)
  have hm : l ≫ prod.map (𝟙 T) (prod.fst * prod.snd : G ⨯ G ⟶ G) =
      prod.lift b (x * y) := by
    apply prod.hom_ext
    · simp only [l, Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
    · simp only [l, Category.assoc, prod.map_snd, MonObj.comp_mul,
        prod.lift_snd_assoc, prod.lift_fst, prod.lift_snd]
  have hx : l ≫ prod.map (𝟙 T) (prod.fst : G ⨯ G ⟶ G) = prod.lift b x := by
    apply prod.hom_ext
    · simp only [l, Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
    · simp only [l, Category.assoc, prod.map_snd, prod.lift_snd_assoc,
        prod.lift_fst, prod.lift_snd]
  have hy : l ≫ prod.map (𝟙 T) (prod.snd : G ⨯ G ⟶ G) = prod.lift b y := by
    apply prod.hom_ext
    · simp only [l, Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
    · simp only [l, Category.assoc, prod.map_snd, prod.lift_snd_assoc, prod.lift_snd]
  have he := congrArg (fun r => l ≫ r) hf.2
  change l ≫ (prod.map (𝟙 T) (prod.fst * prod.snd : G ⨯ G ⟶ G) ≫ f) =
    l ≫ ((prod.map (𝟙 T) prod.fst ≫ f) * (prod.map (𝟙 T) prod.snd ≫ f)) at he
  simpa only [MonObj.comp_mul, ← Category.assoc, hm, hx, hy] using he

def evaluationHom : (W ⟶ G) →* (W ⟶ G) where
  toFun x := prod.lift b x ≫ f
  map_one' := eval_one G f hf b
  map_mul' := eval_mul G f hf b

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.HomEvaluation.GroupHomEquations
