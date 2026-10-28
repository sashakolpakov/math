import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField
import OAI.RepresentationTheory.Weil.UnitarySplitting.Characters

/-! # Quadratic Local Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter

noncomputable section

/-! UnitarySplitting's field-norm character condition is proved for the concrete
nonarchimedean quadratic character, via the actual quadratic field model. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.Characters.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalField

theorem model_quadratic_character
    {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [LocallyCompactSpace k]
    [IsUltrametricDist k] [CharZero k]
    (d : k) (hd : d ≠ 0) (hns : ¬ IsSquare d) (hnd : ¬ DiscreteTopology k) :
    Weil.UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := QuadraticLocalField.FieldModel k d hns)
      (QuadraticNormCharacter.nonarchimedeanNormCharacter d hd hnd) := by
  intro a
  rw [QuadraticNormCharacter.nonarchimedeanNormCharacter_kernel]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨Units.map (QuadraticLocalField.algebraEquiv k d hns).symm.toMonoidHom b, ?_⟩
    change Algebra.norm k ((QuadraticLocalField.algebraEquiv k d hns).symm b.val) = a.val
    rw [QuadraticLocalField.model_norm, AlgEquiv.apply_symm_apply]
    exact congrArg Units.val hb
  · rintro ⟨b, hb⟩
    refine ⟨Units.map (QuadraticLocalField.algebraEquiv k d hns).toMonoidHom b, ?_⟩
    apply Units.ext
    change QuadraticAlgebra.norm (QuadraticLocalField.algebraEquiv k d hns b.val) = a.val
    rw [← QuadraticLocalField.model_norm]
    exact hb

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalCharacter
