import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Generic Flatness -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFlatness.Construction

noncomputable section

/-! The generic-flatness step for finite morphisms in the Openness development. -/

open scoped TensorProduct

universe u

/-- At a minimal prime of a reduced ring, every localized module is free
because the local ring is a field. -/
theorem minimalPrime_mem_freeLocus
    (R M : Type*) [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) :
    (⟨q, hq.1.1⟩ : PrimeSpectrum R) ∈ Module.freeLocus R M := by
  have : q.IsPrime := hq.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime q) :=
    Ring.KrullDimLE.of_isLocalization q hq _
  let : Field (Localization.AtPrime q) :=
    Ring.KrullDimLE.isField_of_isReduced.toField
  change Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M)
  infer_instance

/-- The free locus is dense over a reduced base. Finite presentation will
add openness, yielding the generic-flatness neighborhood. -/
theorem dense_freeLocus_of_reduced
    (R M : Type*) [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] : Dense (Module.freeLocus R M) := by
  intro p
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal R)) (J := p.asIdeal) bot_le
  let q' : PrimeSpectrum R := ⟨q, hq.1.1⟩
  have hspec : q' ⤳ p := (PrimeSpectrum.le_iff_specializes q' p).mp hqp
  exact hspec.mem_closed isClosed_closure
    (subset_closure (minimalPrime_mem_freeLocus R M q hq))

/-- A finitely presented module over a reduced ring is locally free on
a dense open subset of the spectrum. -/
theorem dense_open_freeLocus_of_reduced
    (R M : Type*) [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    IsOpen (Module.freeLocus R M) ∧ Dense (Module.freeLocus R M) :=
  ⟨Module.isOpen_freeLocus, dense_freeLocus_of_reduced R M⟩

/-- A finitely presented module over a domain is free after inverting
one nonzero element. -/
theorem exists_nonzero_free_localization
    (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
  let K := FractionRing R
  let f : M →ₗ[R] K ⊗[R] M := TensorProduct.mk R K M 1
  have : IsLocalizedModule (nonZeroDivisors R) f := by
    dsimp [f, K]
    infer_instance
  have : Module.Free K (K ⊗[R] M) := by
    change Module.Free (FractionRing R) (FractionRing R ⊗[R] M)
    infer_instance
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors R) f K
  exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hfree⟩

/-- The resulting principal open has a flat localized module. -/
theorem exists_nonzero_flat_localization
    (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Flat (Localization.Away r) (LocalizedModule.Away r M) := by
  obtain ⟨r, hr, hfree⟩ := exists_nonzero_free_localization R M
  have : Module.Free (Localization.Away r) (LocalizedModule.Away r M) := hfree
  exact ⟨r, hr, inferInstance⟩

/-- The same generic-flatness statement in the tensor-product model of base change. -/
theorem exists_nonzero_flat_tensorLocalization
    (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Flat (Localization.Away r) (Localization.Away r ⊗[R] M) := by
  obtain ⟨r, hr, hflat⟩ := exists_nonzero_flat_localization R M
  have : Module.Flat (Localization.Away r) (LocalizedModule.Away r M) := hflat
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv
  exact ⟨r, hr, Module.Flat.of_linearEquiv e⟩

/-- A finite-presentation algebra module over a domain has a flat affine
base change over a nonempty principal open. -/
theorem exists_nonzero_flat_affine_baseChange
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Module.FinitePresentation R B] :
    ∃ r : R, r ≠ 0 ∧
      AlgebraicGeometry.Flat
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] B)))) := by
  obtain ⟨r, hr, hflat⟩ := exists_nonzero_flat_tensorLocalization R B
  have : Module.Flat (Localization.Away r) (Localization.Away r ⊗[R] B) := hflat
  refine ⟨r, hr, AlgebraicGeometry.Flat.SpecMap_iff.mpr ?_⟩
  exact (RingHom.flat_algebraMap_iff).mpr inferInstance

/-- Generic flatness over a nonzero reduced ring, without requiring the
base to be irreducible. The localization is explicitly nontrivial. -/
theorem exists_nontrivial_flat_affine_baseChange_of_reduced
    (R B : Type u) [CommRing R] [IsReduced R] [Nontrivial R]
    [CommRing B] [Algebra R B] [Module.FinitePresentation R B] :
    ∃ r : R, Nontrivial (Localization.Away r) ∧
      AlgebraicGeometry.Flat
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] B)))) := by
  have : Nonempty (PrimeSpectrum R) := PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
  obtain ⟨q, hq⟩ := (dense_freeLocus_of_reduced R B).nonempty
  have : Module.Free (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl B) := hq
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl B)
      (Localization.AtPrime q.asIdeal)
  let φ : Localization.Away r →+* Localization.AtPrime q.asIdeal :=
    IsLocalization.map (M := Submonoid.powers r) (T := q.asIdeal.primeCompl)
      (Localization.AtPrime q.asIdeal) (RingHom.id R) (Submonoid.powers_le.mpr hr)
  have : Module.Free (Localization.Away r) (LocalizedModule.Away r B) := hfree
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) B)).equiv
  have : Module.Flat (Localization.Away r) (Localization.Away r ⊗[R] B) :=
    Module.Flat.of_linearEquiv e
  exact ⟨r, φ.domain_nontrivial,
    AlgebraicGeometry.Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.GenericFlatness.Construction
