import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! # Module Local Basis -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasis.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: finite polynomial trivializations of the actual finite projective symmetric spectrum -/

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Module.Finite R M]

theorem projectiveSymmetric_exists_trivialization (p : Ideal R) [p.IsPrime] :
    ∃ (r : R), r ∉ p ∧ ∃ (ι : Type) (_ : Finite ι)
      (e : Symmetric.LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M (Submonoid.powers r) ≃+* MvPolynomial ι (Localization.Away r)),
      ∀ a : Localization.Away r,
        e (Symmetric.LocalizationLift.BundleCycles.localizedSymmetricScalarMap M (Submonoid.powers r) (Localization.Away r) a) = MvPolynomial.C a := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  have : Module.Flat (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    inferInstance
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  let := hfree
  let N := LocalizedModule.Away r M
  let S := Localization.Away r
  have hD : Submonoid.powers r ≤ Submonoid.comap (RingHom.id R) p.primeCompl := by
    change Submonoid.powers r ≤ p.primeCompl
    exact Submonoid.powers_le.mpr hr
  have : Nontrivial S :=
    (IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
      hD : S →+* Localization.AtPrime p).domain_nontrivial
  let f : M →ₗ[R] N := LocalizedModule.mkLinearMap (Submonoid.powers r) M
  have : Module.Finite S N := Module.Finite.of_isLocalizedModule (Submonoid.powers r) f
  let ι := Module.Free.ChooseBasisIndex S N
  let b : Module.Basis ι S N := Module.Free.chooseBasis S N
  have : Finite ι := Module.Finite.finite_basis b
  let e := (Symmetric.LocalizationEquiv.BundleCycles.symmetricLocalizationEquiv M (Submonoid.powers r) S f).trans
    (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv
  refine ⟨r, hr, ι, inferInstance, e, ?_⟩
  intro a
  change (SymmetricAlgebra.equivMvPolynomial b)
    (Symmetric.LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) (Submonoid.powers r) f
      (Symmetric.LocalizationLift.BundleCycles.localizedSymmetricScalarMap M (Submonoid.powers r) S a)) = _
  rw [Symmetric.LocalizationEquiv.BundleCycles.symmetricLocalizationMap_scalar]
  exact (SymmetricAlgebra.equivMvPolynomial b).commutes a

end

/-! A finite projective module has an actual finite basis on a
principal coefficient neighborhood of each prime. -/

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Projective R M] [Module.Finite R M]

theorem projectiveModule_exists_localBasis (p : Ideal R) [p.IsPrime] :
    ∃ (r : R), r ∉ p ∧ ∃ (ι : Type) (_ : Finite ι),
      Nonempty (Module.Basis ι (Localization.Away r) (LocalizedModule.Away r M)) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  have : Module.Flat (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := inferInstance
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  let := hfree
  let N := LocalizedModule.Away r M
  let S := Localization.Away r
  have hD : Submonoid.powers r ≤ Submonoid.comap (RingHom.id R) p.primeCompl := by
    change Submonoid.powers r ≤ p.primeCompl
    exact Submonoid.powers_le.mpr hr
  let : Nontrivial S := (IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
    hD : S →+* Localization.AtPrime p).domain_nontrivial
  let f : M →ₗ[R] N := LocalizedModule.mkLinearMap (Submonoid.powers r) M
  let : Module.Finite S N := Module.Finite.of_isLocalizedModule (Submonoid.powers r) f
  let ι := Module.Free.ChooseBasisIndex S N
  let b : Module.Basis ι S N := Module.Free.chooseBasis S N
  exact ⟨r, hr, ι, Module.Finite.finite_basis b, ⟨b⟩⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleLocalBasis.BundleCycles
