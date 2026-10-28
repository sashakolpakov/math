import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections

/-! # Invertible Cancellation Pairing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleCancellationPairing

noncomputable section

/-! The invertible evaluation isomorphism has the genuine sheaf dual pairing as its map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u
local instance invertibleCancellationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def invertibleDualPairingIso {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) :
    M ⊗ Dual.Scheme.Modules.dualObj M ≅ Invertible.Scheme.Modules.unitObj X := by
  letI : IsIso (Evaluation.Scheme.Modules.ev M) := InvertibleEvaluation.Scheme.Modules.isIso_eval_of_isInvertible hM
  letI : IsIso (TensorFrameSections.dualPairing M) := by
    unfold TensorFrameSections.dualPairing
    infer_instance
  exact asIso (TensorFrameSections.dualPairing M)

theorem invertibleDualPairingIso_hom {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) :
    (invertibleDualPairingIso M hM).hom = TensorFrameSections.dualPairing M := rfl

theorem invertibleCancellationPairing_hom {X : Scheme.{u}}
    (M : X.Modules) (hM : Invertible.Scheme.Modules.IsInvertible M) :
    (TensorSections.monoidalTensorObjIso M (Dual.Scheme.Modules.dualObj M) ≪≫
      InvertibleEvaluation.Scheme.Modules.invertibleEvaluationIso hM ≪≫ (TensorSections.monoidalUnitObjIso X).symm).hom ≫
        (TensorSections.monoidalUnitObjIso X).hom = TensorFrameSections.dualPairing M := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleCancellationPairing
