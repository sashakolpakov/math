import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalOscillator
import OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

/-! # Finite Cover Operator -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FiniteCoverOperator.CM

noncomputable section

section

/-! ThetaCycle: actual finite and archimedean operators of a restricted oscillator
lift. The finite operator acts on the entire native Schwartz tensor space. -/

open scoped Classical _root_.NumberField
open Filter
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted
open OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

theorem restricted_test_family_ext {F : Type} [Field F] [NumberField F] {N : ℕ}
    {f g : RepresentationTheory.Weil.AdelicSplitting.RestrictedTestFamilies.Construction.RestrictedTestFamily F N} (h : ∀ v, f.component v = g.component v) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := funext h
      subst g
      rfl

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
    (ψ : AddChar (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)

local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : NumberField.InfinitePlace F) : MeasurableSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := borel _
local instance (v : NumberField.InfinitePlace F) : BorelSpace (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) := ⟨rfl⟩

def finiteRestrictedCover (a : RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ) :
    RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F N ψ (.inr v)) :=
  ⟨fun v => a (.inr v), Sum.inr_injective.tendsto_cofinite.eventually a.property⟩

theorem finite_cover_operator_vacuum :
    ∀ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F in cofinite,
      ∀ g ∈ RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F N ψ (.inr v),
        RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)) g
          (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v :=
  Eventually.of_forall (fun _ _ hg => hg.2)

def finiteCoverOperator (a : RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ) : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N :=
  RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.action (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) (fun v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F => RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.coverIntegral F N ψ (.inr v))
    (fun v => RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v)))
    (finite_cover_operator_vacuum F N ψ) (finiteRestrictedCover F N ψ a)

def archimedeanCoverOperator (a : RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ) (φ : RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests F N) :
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests F N :=
  fun v => RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl v)) N (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inl v))
    (a (.inl v)) (φ v)

theorem finite_cover_family_restricted (a : RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    ∀ᶠ v in cofinite,
      RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v))
        (a (.inr v)) (f v) = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v := by
  filter_upwards [(finiteRestrictedCover F N ψ a).property, hf] with v ha hv
  rw [hv]
  exact ha.2

theorem finite_cover_operator_pure (a : RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    finiteCoverOperator F N ψ a (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) f hf) =
      RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)
        (fun v => RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v))
          (a (.inr v)) (f v)) (finite_cover_family_restricted F N ψ a f hf) := by
  apply Subtype.ext
  exact RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.fullAction_pure _ _ _ f

theorem test_family_cover_action (a : RepresentationTheory.Weil.AdelicSplitting.Rational.Construction.RestrictedCover F N ψ) (φ : RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests F N)
    (f : ∀ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace F, RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (v.adicCompletion F) N)
    (hf : ∀ᶠ v in cofinite, f v = RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N v) :
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.testFamily F N (archimedeanCoverOperator F N ψ a φ)
        (fun v => RepresentationTheory.Weil.AdelicSplitting.Oscillator.Construction.localOperator (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inr v)) N (RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v))
          (a (.inr v)) (f v)) (finite_cover_family_restricted F N ψ a f hf) =
      (RepresentationTheory.Theta.Adelic.ThetaEvaluation.testFamily F N φ f hf).act F N ψ a := by
  apply restricted_test_family_ext
  intro v
  cases v <;> rfl

end

/-! ThetaCycle: exact rational theta covariance on the entire finite Schwartz
tensor space. Linearity extends native pure-family theta invariance. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.TensorProjective.Restricted
open OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem rational_tensor_theta_covariance (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic F N)
    (φ : RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests F N) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N) :
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F N
        (archimedeanCoverOperator F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F)
          (RationalOscillator.CM.restrictedFieldRationalOscillator F N γ) φ)
        (finiteCoverOperator F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F)
          (RationalOscillator.CM.restrictedFieldRationalOscillator F N γ) f) = RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F N φ f := by
  let a := RationalOscillator.CM.restrictedFieldRationalOscillator F N γ
  let l : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N →ₗ[ℂ] ℂ :=
    (RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F N (archimedeanCoverOperator F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) a φ)).comp
      (finiteCoverOperator F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) a).toLinearMap
  let r := RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F N φ
  have hall : ∀ x (hx : x ∈ RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.restrictedTensor (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N)), l ⟨x, hx⟩ = r ⟨x, hx⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      change RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F N (archimedeanCoverOperator F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) a φ)
        (finiteCoverOperator F N (FieldAdelicCharacter.CM.fieldAdelicCharacter F) a (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) g hg)) =
          RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta F N φ (RepresentationTheory.Theta.Adelic.TensorProjective.Restricted.pure (RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.finiteVacuum F N) g hg)
      rw [finite_cover_operator_pure, RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta_pure, RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta_pure, test_family_cover_action]
      exact RationalOscillator.CM.restricted_field_rational_oscillator_theta F N γ (RepresentationTheory.Theta.Adelic.ThetaEvaluation.testFamily F N φ g hg)
    | zero =>
      change l 0 = r 0
      rw [map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      change l (⟨x, hx⟩ + ⟨y, hy⟩) = r (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
    | smul c x hx ih =>
      change l (c • (⟨x, hx⟩ : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N)) = r (c • (⟨x, hx⟩ : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F N))
      rw [map_smul, map_smul, ih]
  exact hall f.val f.property

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FiniteCoverOperator.CM
