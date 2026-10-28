import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence

/-! # Invertible Right Tensor Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleRightTensorMap

noncomputable section

/-! The actual map underlying the right-tensor equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u
local instance rightTensorMapMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem invertibleRightTensorEquivalence_map {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) {A B : X.Modules} (f : A ⟶ B) :
    (InvertibleTensorEquivalence.invertibleRightTensorEquivalence M hM).functor.map f = f ▷ M := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleRightTensorMap
