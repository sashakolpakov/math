import OAI.AlgebraicGeometry.Resolution.Blowups.LocalizedCotangentMap
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Localized Conormal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction

noncomputable section

section

/-! The coefficient quotient and conormal module of an actual localized center. -/

open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem quotient_extended_ideal_isLocalization
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R) :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map (algebraMap R S)) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  let : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) ((R ⧸ I) ⊗[R] S) := inferInstance
  exact IsLocalization.isLocalization_of_algEquiv _ e.symm

theorem quotient_extended_ideal_isLocalizationAway
    (r : R) [IsLocalization.Away r S] (I : Ideal R) :
    IsLocalization.Away (Ideal.Quotient.mk I r) (S ⧸ I.map (algebraMap R S)) := by
  have h := quotient_extended_ideal_isLocalization (S := S) (Submonoid.powers r) I
  rwa [Algebra.algebraMapSubmonoid_powers] at h

abbrev extendedCotangentQuotientModule (I : Ideal R) :
    Module (R ⧸ I) (I.map (algebraMap R S)).Cotangent :=
  Module.compHom _ (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))

theorem extendedCotangentQuotientModule_scalarTower (I : Ideal R) :
    letI := extendedCotangentQuotientModule (S := S) I
    IsScalarTower R (R ⧸ I) (I.map (algebraMap R S)).Cotangent := by
  let : Module (R ⧸ I) (I.map (algebraMap R S)).Cotangent := extendedCotangentQuotientModule I
  constructor
  intro r q x
  change algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)) ((algebraMap R (R ⧸ I) r) * q) • x =
    r • (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)) q • x)
  rw [map_mul, mul_smul, ← IsScalarTower.algebraMap_apply R (R ⧸ I) (S ⧸ I.map (algebraMap R S))]
  rw [IsScalarTower.algebraMap_apply R S (S ⧸ I.map (algebraMap R S)), algebraMap_smul, algebraMap_smul]

end

/-! Conormal localization is linear over the original quotient ring. -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def extendedQuotientCotangentMap (I : Ideal R) :
    letI := extendedCotangentQuotientModule (S := S) I
    I.Cotangent →ₗ[R ⧸ I] (I.map (algebraMap R S)).Cotangent := by
  let : Module (R ⧸ I) (I.map (algebraMap R S)).Cotangent := extendedCotangentQuotientModule I
  let : IsScalarTower R (R ⧸ I) (I.map (algebraMap R S)).Cotangent :=
    extendedCotangentQuotientModule_scalarTower I
  exact (LocalizedCotangentMap.Construction.extendedIdealCotangentMap (S := S) I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

theorem extendedQuotientCotangentMap_restrictScalars (I : Ideal R) :
    letI := extendedCotangentQuotientModule (S := S) I
    letI := extendedCotangentQuotientModule_scalarTower (S := S) I
    (extendedQuotientCotangentMap (S := S) I).restrictScalars R = LocalizedCotangentMap.Construction.extendedIdealCotangentMap (S := S) I := rfl

theorem extendedQuotientCotangentMap_isLocalizedModule (r : R) [IsLocalization.Away r S] (I : Ideal R) :
    letI := extendedCotangentQuotientModule (S := S) I
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk I r)) (extendedQuotientCotangentMap (S := S) I) := by
  let : Module (R ⧸ I) (I.map (algebraMap R S)).Cotangent := extendedCotangentQuotientModule I
  let : IsScalarTower R (R ⧸ I) (I.map (algebraMap R S)).Cotangent :=
    extendedCotangentQuotientModule_scalarTower I
  let : IsLocalizedModule (Submonoid.powers r)
      ((extendedQuotientCotangentMap (S := S) I).restrictScalars R) :=
    LocalizedCotangentMap.Construction.extendedIdealCotangentMap_isLocalizedModule (Submonoid.powers r) I
  have h := IsLocalizedModule.of_restrictScalars (Submonoid.powers r) (extendedQuotientCotangentMap (S := S) I)
  rwa [Algebra.algebraMapSubmonoid_powers] at h

theorem extendedQuotientCotangentMap_scalarTower (I : Ideal R) :
    letI := extendedCotangentQuotientModule (S := S) I
    IsScalarTower (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (I.map (algebraMap R S)).Cotangent := by
  let : Module (R ⧸ I) (I.map (algebraMap R S)).Cotangent := extendedCotangentQuotientModule I
  constructor
  intro r s x
  rw [Algebra.smul_def]
  change (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)) r * s) • x =
    algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)) r • (s • x)
  exact mul_smul _ _ _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.LocalizedConormal.Construction
