import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter
import OAI.RepresentationTheory.Theta.Adelic.RationalGraph
import OAI.RepresentationTheory.Theta.Adelic.ExactLevi

/-! # Rational Oscillator -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalOscillator.CM

noncomputable section

/-! ThetaCycle: the actual rational oscillator homomorphism and its exact theta
invariance, instantiated with the constructed standard trace character.
There is no input character, rational lift, or unitary splitting package. -/

open scoped _root_.NumberField Classical

open OAI.RepresentationTheory.Theta.Adelic.RationalGraph OAI.RepresentationTheory.Theta.Adelic.ExactLevi.RationalTheta

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem exists_field_rational_oscillator :
    ∃ r : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N →* RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F),
      (∀ γ a, (γ, a) ∈ RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.rationalGraph F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) ↔ r γ = a) ∧
      ∀ γ, RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.globalProjection F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) (r γ) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.rationalSymplectic F N γ :=
  RepresentationTheory.Theta.Adelic.RationalGraph.rationalGraph_realization F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F)
    (FieldAdelicCharacter.CM.field_adelic_character_continuous F) (FieldAdelicCharacter.CM.field_adelic_character_unitary F)
    (FieldAdelicCharacter.CM.field_adelic_character_nontrivial F) (FieldAdelicCharacter.CM.field_adelic_character_principal F)

def fieldRationalOscillator : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N →* RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) :=
  (exists_field_rational_oscillator F N).choose

theorem field_rational_oscillator_graph (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N)
    (a : RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.GlobalCover F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F)) :
    (γ, a) ∈ RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.rationalGraph F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) ↔ fieldRationalOscillator F N γ = a :=
  (exists_field_rational_oscillator F N).choose_spec.1 γ a

theorem field_rational_oscillator_covers (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N) :
    RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.globalProjection F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) (fieldRationalOscillator F N γ) =
      RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.rationalSymplectic F N γ :=
  (exists_field_rational_oscillator F N).choose_spec.2 γ

theorem field_rational_oscillator_theta (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N) (f : RepresentationTheory.Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    RepresentationTheory.Weil.AdelicSplitting.ThetaScalarKernel.Construction.globalTheta F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) (fieldRationalOscillator F N γ) f = f.theta F N := by
  apply (RepresentationTheory.Theta.Adelic.ExactLevi.RationalTheta.mem_globalThetaStabilizer_iff F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) _).mp
  have h := RepresentationTheory.Theta.Adelic.ExactLevi.RationalTheta.rationalGraph_stabilizes_theta F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F)
    (FieldAdelicCharacter.CM.field_adelic_character_continuous F) (FieldAdelicCharacter.CM.field_adelic_character_unitary F)
    (FieldAdelicCharacter.CM.field_adelic_character_nontrivial F) (FieldAdelicCharacter.CM.field_adelic_character_principal F)
      ((field_rational_oscillator_graph F N γ _).mpr rfl)
  exact h

theorem exists_restricted_field_rational_oscillator (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N) :
    ∃ a : RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F),
      RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) a = fieldRationalOscillator F N γ :=
  QuotientGroup.mk'_surjective
    (RepresentationTheory.Weil.AdelicSplitting.CentralProduct.Construction.scalarKernel (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F))
      (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.scalarAt F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F))) (fieldRationalOscillator F N γ)

def restrictedFieldRationalOscillator (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N) :
    RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) :=
  (exists_restricted_field_rational_oscillator F N γ).choose

theorem restricted_field_rational_oscillator_assemble (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N) :
    RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.assembleGlobalCover F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) (restrictedFieldRationalOscillator F N γ) =
      fieldRationalOscillator F N γ :=
  (exists_restricted_field_rational_oscillator F N γ).choose_spec

theorem restricted_field_rational_oscillator_theta (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N)
    (f : RepresentationTheory.Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N) :
    (f.act F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) (restrictedFieldRationalOscillator F N γ)).theta F N =
      f.theta F N := by
  apply RepresentationTheory.Theta.Adelic.ExactLevi.RationalTheta.rational_theta F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F)
    (FieldAdelicCharacter.CM.field_adelic_character_continuous F) (FieldAdelicCharacter.CM.field_adelic_character_unitary F)
    (FieldAdelicCharacter.CM.field_adelic_character_nontrivial F) (FieldAdelicCharacter.CM.field_adelic_character_principal F) γ
  rw [restricted_field_rational_oscillator_assemble]
  exact (field_rational_oscillator_graph F N γ _).mpr rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalOscillator.CM
