import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Source Trivialization Top -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SourceTrivializationTop.Construction.SourceTrivialization

/-!
# Local bases for the finite locally free subgroup

The finite-free source assumption in the affine quotient construction is
available locally on the base of a finite, flat, finitely presented morphism.
We extract explicit principal-open denominators and finite bases.
-/

open _root_.Module _root_.AlgebraicGeometry

universe u v

/-- A finite flat finitely presented module has a finite basis on a principal
neighborhood of each prime. -/
theorem exists_basis_away
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] [Module.FinitePresentation R M]
    (p : PrimeSpectrum R) :
    ∃ r ∉ p.asIdeal, ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r) (LocalizedModule.Away r M)) := by
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule.AtPrime p.asIdeal M
  have : Module.Free Rₚ Mₚ := Module.free_of_flat_of_isLocalRing
  have : Module.Finite Rₚ Mₚ := inferInstance
  obtain ⟨r, hr, b, _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) Rₚ
    (Module.finBasis Rₚ Mₚ)
  exact ⟨r, hr, Module.finrank Rₚ Mₚ, ⟨b⟩⟩

/-- The principal opens carrying finite bases cover the entire spectrum. -/
theorem basis_denominators_span_top
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] [Module.FinitePresentation R M] :
    Ideal.span {r : R | ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r) (LocalizedModule.Away r M))} = ⊤ := by
  by_contra h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨r, hr, hb⟩ := exists_basis_away (M := M) ⟨P, hP.isPrime⟩
  exact hr (hle (Ideal.subset_span hb))

/-- A basis of the localized module gives a basis of any corresponding
localized algebra, using its actual ring of scalars. -/
noncomputable def algebraBasis
    {R A R₁ A₁ : Type*} [CommRing R] [CommRing A] [CommRing R₁] [CommRing A₁]
    [Algebra R A] [Algebra R R₁] [Algebra A A₁] [Algebra R A₁] [Algebra R₁ A₁]
    [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁]
    (r : R) [IsLocalization.Away r R₁]
    [IsLocalization.Away (algebraMap R A r) A₁]
    [Module R₁ (LocalizedModule.Away r A)]
    [IsScalarTower R R₁ (LocalizedModule.Away r A)]
    {ι : Type*} (b : Basis ι R₁ (LocalizedModule.Away r A)) : Basis ι R₁ A₁ := by
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers r)) A₁ := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) A)
    (IsScalarTower.toAlgHom R A A₁).toLinearMap
  exact b.map (e.extendScalarsOfIsLocalization (Submonoid.powers r) R₁)

/-- The hypotheses on the finite locally free subgroup give the needed local
bases of its affine coordinate algebra over every affine base. -/
theorem affine_morphism_exists_basis_away
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (p : PrimeSpectrum Γ(S, ⊤)) :
    letI := f.appTop.hom.toAlgebra
    ∃ r ∉ p.asIdeal, ∃ n : ℕ,
      Nonempty (Basis (Fin n) (Localization.Away r) (LocalizedModule.Away r Γ(X, ⊤))) := by
  let := f.appTop.hom.toAlgebra
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Module.Finite Γ(S, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : Module.Flat Γ(S, ⊤) Γ(X, ⊤) := f.flat_appTop
  have : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) := f.finitePresentation_appTop
  have : Module.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation Γ(S, ⊤) Γ(X, ⊤)
  exact exists_basis_away p

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SourceTrivializationTop.Construction.SourceTrivialization
