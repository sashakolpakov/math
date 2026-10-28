import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalTensorUnit

/-! # Tensor By Section Evaluation -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBySectionEvaluation.Construction

noncomputable section

/-! Multiplication by a unit section is the actual pure tensor map on every open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite

universe u

local instance tensorBySectionEvaluationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem rightUnitor_inv_local_section {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (x : Γ(M, U)) :
    (ρ_ M).inv.val.app (op U) x =
      AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection M (𝟙_ X.Modules) U x (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U) := by
  have : IsIso ((ρ_ M).hom.app U) := TensorSectionFrame.Construction.moduleMap_app_isIso_of_pullback (ρ_ M).hom U
  apply (ConcreteCategory.bijective_of_isIso ((ρ_ M).hom.app U)).injective
  exact (TensorUnitCoefficient.Construction.moduleIso_inv_hom_app (ρ_ M) U x).trans (LocalTensorUnit.Construction.rightUnitor_local_tensorSection M U x).symm

theorem tensorByUnitSection_local_section {X : Scheme.{u}} (M : X.Modules) {P : X.Modules}
    (s : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X ⟶ P) (U : X.Opens) (x : Γ(M, U)) :
    (TensorSectionFrame.Construction.tensorByUnitSection M ((AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom ≫ s)).app U x =
      AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection M P U x (s.app U (1 : Γ(X, U))) := by
  let a := (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).hom ≫ s
  have ha : a.val.app (op U) (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U) = s.app U (1 : Γ(X, U)) :=
    congrArg (s.app U) (TensorUnitCoefficient.Construction.moduleIso_inv_hom_app (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X) U (show Γ(X, U) from 1))
  change (𝟙 M ⊗ₘ a).val.app (op U) ((ρ_ M).inv.val.app (op U) x) = _
  rw [rightUnitor_inv_local_section]
  have ht := AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections.tensorSection_map (𝟙 M) a U x (AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing.localMonoidalUnitSection X U)
  exact ht.trans (congrArg (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection M P U x) ha)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBySectionEvaluation.Construction
