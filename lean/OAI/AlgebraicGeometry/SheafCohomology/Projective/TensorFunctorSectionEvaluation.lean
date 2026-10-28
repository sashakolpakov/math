import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleRightTensorMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections

/-! # Tensor Functor Section Evaluation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFunctorSectionEvaluation

noncomputable section

/-! Direct evaluation of tensor functors and base-linear global section maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
local instance tensorFunctorEvaluationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem invertibleRightTensorEquivalence_map_tensor {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) {A B : X.Modules} (f : A ⟶ B) :
    (InvertibleTensorEquivalence.invertibleRightTensorEquivalence M hM).functor.map f = f ⊗ₘ 𝟙 M := by
  rw [tensorHom_id, InvertibleRightTensorMap.invertibleRightTensorEquivalence_map]

theorem baseGlobalSectionsFunctor_map_apply {X S : Scheme.{u}} (π : X ⟶ S)
    {M N : X.Modules} (f : M ⟶ N) (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor π).obj M) :
    (AdditiveCoproductSections.baseGlobalSectionsFunctor π).map f x = f.val.app (op ⊤) x := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFunctorSectionEvaluation
