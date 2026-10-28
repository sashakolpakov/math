import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Finiteness
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SourceTrivializationTop
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantLocalizationIs
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-! # Flat Finiteness -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatFiniteness.Construction.FlatFinitenessDescent

/-!
# Finite presentation descends along finite locally free extensions

Local finite bases reduce the argument to the module-retraction form of
Artin--Tate. The resulting target localizations cover the whole spectrum.
-/

open _root_.Module

universe u v w

variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]

/-- Finite presentation descends along an injective finite, flat, finitely
presented algebra extension. No noetherian hypothesis is needed. -/
theorem finitePresentation
    [Algebra.FinitePresentation R A] [Module.Finite B A] [Module.Flat B A]
    [Algebra.FinitePresentation B A]
    (hinj : Function.Injective (algebraMap B A)) : Algebra.FinitePresentation R B := by
  have : Module.FinitePresentation B A :=
    Module.FinitePresentation.of_finite_of_finitePresentation B A
  let D := {r : B | ∃ n : ℕ,
    Nonempty (Basis (Fin n) (Localization.Away r) (LocalizedModule.Away r A))}
  have hD : Ideal.span D = ⊤ := SourceTrivializationTop.Construction.SourceTrivialization.basis_denominators_span_top
  apply Algebra.FinitePresentation.of_span_eq_top_target D hD
  intro r hr
  obtain ⟨n, ⟨b⟩⟩ := hr
  let B₁ := Localization.Away r
  let A₁ := Localization.Away (algebraMap B A r)
  let f := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap (algebraMap B A) r (algebraMap B A r) rfl
  let : Algebra B₁ A₁ := f.toAlgebra
  have hf (x : B) : algebraMap B₁ A₁ (algebraMap B B₁ x) = algebraMap B A₁ x :=
    InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap (algebraMap B A) r _ rfl x
  have : IsScalarTower B B₁ A₁ := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  have : IsScalarTower R B₁ A₁ := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R B B₁, hf, ← IsScalarTower.algebraMap_apply R B A₁]
  let b₁ : Basis (Fin n) B₁ A₁ := SourceTrivializationTop.Construction.SourceTrivialization.algebraBasis r b
  have : Module.Free B₁ A₁ := Module.Free.of_basis b₁
  have : Module.Finite B₁ A₁ := Module.Finite.of_basis b₁
  have : Algebra.FinitePresentation R A₁ := Algebra.FinitePresentation.trans R A A₁
  exact FiniteDescent.Finiteness.Construction.FinitenessDescent.finitePresentation_of_finite_free
    (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_injective (algebraMap B A) r _ rfl hinj)

/-- Flatness over the original base descends through the same finite locally
free extension. -/
theorem flat
    [Module.Flat R A] [Module.Finite B A] [Module.Flat B A]
    [Algebra.FinitePresentation B A]
    (hinj : Function.Injective (algebraMap B A)) : Module.Flat R B := by
  have : Module.FinitePresentation B A :=
    Module.FinitePresentation.of_finite_of_finitePresentation B A
  let D := {r : B | ∃ n : ℕ,
    Nonempty (Basis (Fin n) (Localization.Away r) (LocalizedModule.Away r A))}
  have hD : Ideal.span D = ⊤ := SourceTrivializationTop.Construction.SourceTrivialization.basis_denominators_span_top
  apply Module.flat_of_isLocalized_span (R := R) B B D hD
    (fun r => Localization.Away r.val) (fun r => Algebra.linearMap B (Localization.Away r.val))
  intro r
  obtain ⟨n, ⟨b⟩⟩ := r.property
  let r := r.val
  let B₁ := Localization.Away r
  let A₁ := Localization.Away (algebraMap B A r)
  let f := InvariantLocalizationIs.Construction.InvariantLocalization.awayMap (algebraMap B A) r (algebraMap B A r) rfl
  let : Algebra B₁ A₁ := f.toAlgebra
  have hf (x : B) : algebraMap B₁ A₁ (algebraMap B B₁ x) = algebraMap B A₁ x :=
    InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_algebraMap (algebraMap B A) r _ rfl x
  have : IsScalarTower B B₁ A₁ := IsScalarTower.of_algebraMap_eq fun x => (hf x).symm
  have : IsScalarTower R B₁ A₁ := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R B B₁, hf, ← IsScalarTower.algebraMap_apply R B A₁]
  let b₁ : Basis (Fin n) B₁ A₁ := SourceTrivializationTop.Construction.SourceTrivialization.algebraBasis r b
  have : Module.Free B₁ A₁ := Module.Free.of_basis b₁
  have : Module.Flat R A₁ := Module.Flat.trans R A A₁
  exact FiniteDescent.Finiteness.Construction.FinitenessDescent.flat_of_free
    (InvariantLocalizationIs.Construction.InvariantLocalization.awayMap_injective (algebraMap B A) r _ rfl hinj)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatFiniteness.Construction.FlatFinitenessDescent
