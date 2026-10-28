import OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueEmbedding
import OAI.NumberTheory.PadicHodge.PeriodInvariants.TiltConstants
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueCoefficients

/-! # Embedding -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.PeriodInvariants.Embedding.UnramifiedConstants

/-!
# Unramified Witt constants in the actual A_inf

The residue field of K embeds canonically, relative to the chosen closure
embedding, into the tilt of O_Cp. Its Witt vectors therefore embed into A_inf.
The local Galois action fixes these constants, and Witt Frobenius is preserved.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars
  ResidueCoefficients ResidueEmbedding TiltConstants

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

local instance residueFintype : Fintype (IntegralGeometry.ResidueField p K) := Fintype.ofFinite _

def residueTiltMap : IntegralGeometry.ResidueField p K →+* PreTilt 𝓞_ℂ_[p] p :=
  TiltConstants.tiltConstants p (IntegralGeometry.ResidueField p K) (ResidueEmbedding.residueEmbedding p K)

theorem residueTiltMap_injective : Function.Injective (residueTiltMap p K) :=
  TiltConstants.tiltConstants_injective p (IntegralGeometry.ResidueField p K) (ResidueEmbedding.residueEmbedding p K)

theorem residueTiltMap_galois (σ : CrystallineScalars.LocalGalois K) (a : IntegralGeometry.ResidueField p K) :
    PeriodRing.tiltMap p (PeriodRing.galoisIntegerEquiv p (CrystallineScalars.galoisToPadic p K σ)).toRingHom (residueTiltMap p K a) =
      residueTiltMap p K a := by
  have he : (IsLocalRing.ResidueField.map (PeriodRing.galoisIntegerEquiv p (CrystallineScalars.galoisToPadic p K σ)).toRingHom).comp
      (ResidueEmbedding.residueEmbedding p K) = ResidueEmbedding.residueEmbedding p K :=
    RingHom.ext (ResidueEmbedding.residueEmbedding_galois p K σ)
  have h := TiltConstants.tiltConstants_natural p (IntegralGeometry.ResidueField p K) (ResidueEmbedding.residueEmbedding p K)
    (PeriodRing.galoisIntegerEquiv p (CrystallineScalars.galoisToPadic p K σ)) a
  rw [he] at h
  exact h

def ainfConstants : ResidueCoefficients.WittCoefficients p K →+* PeriodRing.Ainf p := WittVector.map (residueTiltMap p K)

theorem ainfConstants_injective : Function.Injective (ainfConstants p K) :=
  WittVector.map_injective (residueTiltMap p K) (residueTiltMap_injective p K)

theorem ainfConstants_galois (σ : CrystallineScalars.LocalGalois K) (x : ResidueCoefficients.WittCoefficients p K) :
    PeriodRing.ainfMap p (PeriodRing.galoisIntegerEquiv p (CrystallineScalars.galoisToPadic p K σ)).toRingHom (ainfConstants p K x) =
      ainfConstants p K x := by
  apply WittVector.ext
  intro n
  exact residueTiltMap_galois p K σ (x.coeff n)

theorem ainfConstants_frobenius (x : ResidueCoefficients.WittCoefficients p K) :
    AdicEstimates.Frobenius.ainfFrobenius p (ainfConstants p K x) = ainfConstants p K (WittVector.frobenius x) := by
  apply WittVector.ext
  intro n
  simp only [AdicEstimates.Frobenius.ainfFrobenius, ainfConstants, WittVector.frobeniusEquiv_apply, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff, map_pow]

theorem ainfConstants_padicInt (x : ℤ_[p]) :
    ainfConstants p K (ResidueCoefficients.padicIntToWitt p K x) = PeriodRing.padicIntToAinf p x := by
  have he : (residueTiltMap p K).comp (ZMod.castHom (dvd_refl p) (IntegralGeometry.ResidueField p K)) =
      ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p) := Subsingleton.elim _ _
  apply WittVector.ext
  intro n
  exact DFunLike.congr_fun he ((WittVector.fromPadicInt p x).coeff n)

end NumberTheory.PadicHodge.PeriodInvariants.Embedding.UnramifiedConstants

namespace NumberTheory.PadicHodge.PeriodInvariants.Embedding.Period

/-!
# The actual unramified coefficient field inside crystalline periods

The constructed Witt constants extend through p-inversion to K_0. Their
embedding into B_cris is fixed by G_K and preserves Frobenius and Q_p.
This constructs K_0 inside the fixed scalars; surjectivity onto all fixed
scalars is not assumed or asserted.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates.Frobenius OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic OAI.NumberTheory.PadicHodge.PeriodInvariants.TateCyclotomic.Galois OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars
  IntegralGeometry CrystallineScalars ResidueCoefficients UnramifiedConstants

variable (p : ℕ) [Fact p.Prime]

local instance bcrisQpSMul : SMul ℚ_[p] (PeriodRing.Bcris p) := (PeriodRing.bcris_padicAlgebra p).toSMul

def ainfToBcris : PeriodRing.Ainf p →+* PeriodRing.Bcris p :=
  (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p)).comp
    ((algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p)).comp
      ((algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p)).comp (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p))))

theorem ainfToBcris_galois (σ : PeriodRing.PadicGalois p) (x : PeriodRing.Ainf p) :
    TateCyclotomic.Galois.galoisBcrisAction p σ (ainfToBcris p x) =
      ainfToBcris p (PeriodRing.ainfMap p (PeriodRing.galoisIntegerEquiv p σ).toRingHom x) := by
  change TateCyclotomic.Galois.bcrisGaloisMap p σ
    (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p)
      (algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p) (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) x)))) = _
  rw [TateCyclotomic.Galois.bcrisGaloisMap_algebraMap, PeriodRing.bcrisPlusEquiv_algebraMap, PeriodRing.acrisEquiv_algebraMap,
    PeriodRing.acrisZeroMap_algebraMap]
  rfl

theorem ainfToBcris_frobenius (x : PeriodRing.Ainf p) :
    CrystallineScalars.bcrisFrobeniusAlg p (ainfToBcris p x) = ainfToBcris p (AdicEstimates.Frobenius.ainfFrobenius p x) := by
  change Cyclotomic.bcrisFrobenius p
    (algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p)
      (algebraMap (PeriodRing.AcrisZero p) (PeriodRing.Acris p) (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) x)))) = _
  rw [Cyclotomic.bcrisFrobenius_algebraMap, AdicEstimates.Frobenius.bcrisPlusFrobenius_algebraMap, CrystallineScalars.acrisFrobenius_algebraMap,
    CrystallineScalars.acrisZeroFrobenius_algebraMap]
  rfl

theorem ainfToBcris_padicInt (x : ℤ_[p]) :
    ainfToBcris p (PeriodRing.padicIntToAinf p x) = PeriodRing.padicFieldToBcris p (algebraMap ℤ_[p] ℚ_[p] x) := by
  change ainfToBcris p (PeriodRing.padicIntToAinf p x) =
    algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) (PeriodRing.padicFieldToBcrisPlus p (algebraMap ℤ_[p] ℚ_[p] x))
  rw [PeriodRing.padicFieldToBcrisPlus_int]
  rfl

variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

def wittToBcris : ResidueCoefficients.WittCoefficients p K →+* PeriodRing.Bcris p := (ainfToBcris p).comp (UnramifiedConstants.ainfConstants p K)

theorem wittToBcris_galois (σ : CrystallineScalars.LocalGalois K) (x : ResidueCoefficients.WittCoefficients p K) :
    CrystallineScalars.localPeriodAction p K σ (wittToBcris p K x) = wittToBcris p K x := by
  change TateCyclotomic.Galois.galoisBcrisAction p (CrystallineScalars.galoisToPadic p K σ) (ainfToBcris p (UnramifiedConstants.ainfConstants p K x)) = _
  rw [ainfToBcris_galois, UnramifiedConstants.ainfConstants_galois]
  rfl

theorem wittToBcris_frobenius (x : ResidueCoefficients.WittCoefficients p K) :
    CrystallineScalars.bcrisFrobeniusAlg p (wittToBcris p K x) = wittToBcris p K (WittVector.frobenius x) := by
  change CrystallineScalars.bcrisFrobeniusAlg p (ainfToBcris p (UnramifiedConstants.ainfConstants p K x)) = _
  rw [ainfToBcris_frobenius, UnramifiedConstants.ainfConstants_frobenius]
  rfl

theorem wittToBcris_padicInt (x : ℤ_[p]) :
    wittToBcris p K (ResidueCoefficients.padicIntToWitt p K x) = PeriodRing.padicFieldToBcris p (algebraMap ℤ_[p] ℚ_[p] x) := by
  change ainfToBcris p (UnramifiedConstants.ainfConstants p K (ResidueCoefficients.padicIntToWitt p K x)) = _
  rw [UnramifiedConstants.ainfConstants_padicInt]
  exact ainfToBcris_padicInt p x

/-- The actual W(k)[1/p] coefficient map into B_cris. -/
def k0ToBcris : ResidueCoefficients.K0 p K →+* PeriodRing.Bcris p :=
  IsLocalization.Away.lift (p : ResidueCoefficients.WittCoefficients p K) (g := wittToBcris p K)
    (by rw [map_natCast]; exact PeriodRing.p_isUnit_bcris p)

theorem k0ToBcris_algebraMap (x : ResidueCoefficients.WittCoefficients p K) :
    k0ToBcris p K (algebraMap (ResidueCoefficients.WittCoefficients p K) (ResidueCoefficients.K0 p K) x) = wittToBcris p K x :=
  IsLocalization.Away.lift_eq _ _ x

theorem k0ToBcris_injective : Function.Injective (k0ToBcris p K) := (k0ToBcris p K).injective

theorem k0ToBcris_galois (σ : CrystallineScalars.LocalGalois K) (x : ResidueCoefficients.K0 p K) :
    CrystallineScalars.localPeriodAction p K σ (k0ToBcris p K x) = k0ToBcris p K x := by
  have he : (CrystallineScalars.localPeriodAction p K σ).toRingHom.comp (k0ToBcris p K) = k0ToBcris p K := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (p : ResidueCoefficients.WittCoefficients p K))
    apply RingHom.ext
    intro a
    change CrystallineScalars.localPeriodAction p K σ (k0ToBcris p K (algebraMap (ResidueCoefficients.WittCoefficients p K) (ResidueCoefficients.K0 p K) a)) =
      k0ToBcris p K (algebraMap (ResidueCoefficients.WittCoefficients p K) (ResidueCoefficients.K0 p K) a)
    exact (congrArg (CrystallineScalars.localPeriodAction p K σ) (k0ToBcris_algebraMap p K a)).trans
      ((wittToBcris_galois p K σ a).trans (k0ToBcris_algebraMap p K a).symm)
  exact DFunLike.congr_fun he x

theorem k0ToBcris_frobenius (x : ResidueCoefficients.K0 p K) :
    CrystallineScalars.bcrisFrobeniusAlg p (k0ToBcris p K x) = k0ToBcris p K (ResidueCoefficients.coefficientFrobenius p K x) := by
  have he : (CrystallineScalars.bcrisFrobeniusAlg p).toRingHom.comp (k0ToBcris p K) =
      (k0ToBcris p K).comp (ResidueCoefficients.coefficientFrobenius p K).toRingHom := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (p : ResidueCoefficients.WittCoefficients p K))
    apply RingHom.ext
    intro a
    change CrystallineScalars.bcrisFrobeniusAlg p (k0ToBcris p K (algebraMap (ResidueCoefficients.WittCoefficients p K) (ResidueCoefficients.K0 p K) a)) =
      k0ToBcris p K (ResidueCoefficients.coefficientFrobenius p K (algebraMap (ResidueCoefficients.WittCoefficients p K) (ResidueCoefficients.K0 p K) a))
    rw [k0ToBcris_algebraMap, ResidueCoefficients.coefficientFrobenius_algebraMap, k0ToBcris_algebraMap]
    exact wittToBcris_frobenius p K a
  exact DFunLike.congr_fun he x

theorem k0ToBcris_padic (x : ℚ_[p]) :
    k0ToBcris p K (ResidueCoefficients.padicToK0 p K x) = PeriodRing.padicFieldToBcris p x := by
  have he : (k0ToBcris p K).comp (ResidueCoefficients.padicToK0 p K) = PeriodRing.padicFieldToBcris p := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    apply RingHom.ext
    intro a
    change k0ToBcris p K (ResidueCoefficients.padicToK0 p K (algebraMap ℤ_[p] ℚ_[p] a)) =
      PeriodRing.padicFieldToBcris p (algebraMap ℤ_[p] ℚ_[p] a)
    rw [ResidueCoefficients.padicToK0_int]
    change k0ToBcris p K (algebraMap (ResidueCoefficients.WittCoefficients p K) (ResidueCoefficients.K0 p K) (ResidueCoefficients.padicIntToWitt p K a)) = _
    rw [k0ToBcris_algebraMap]
    exact wittToBcris_padicInt p K a
  exact DFunLike.congr_fun he x

instance bcris_k0Algebra : Algebra (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p) := (k0ToBcris p K).toAlgebra

instance bcris_k0SMul : SMul (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p) := (bcris_k0Algebra p K).toSMul

instance bcris_k0Module : Module (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p) := (bcris_k0Algebra p K).toModule

instance bcris_k0ScalarTower : IsScalarTower ℚ_[p] (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p) :=
  IsScalarTower.of_algebraMap_eq (fun x => (k0ToBcris_padic p K x).symm)

def k0ToFixedScalars : ResidueCoefficients.K0 p K →ₐ[ℚ_[p]] CrystallineScalars.localFixedScalars p K where
  toFun x := ⟨k0ToBcris p K x, fun σ => k0ToBcris_galois p K σ x⟩
  map_zero' := Subtype.ext (map_zero (k0ToBcris p K))
  map_one' := Subtype.ext (map_one (k0ToBcris p K))
  map_add' x y := Subtype.ext (map_add (k0ToBcris p K) x y)
  map_mul' x y := Subtype.ext (map_mul (k0ToBcris p K) x y)
  commutes' a := Subtype.ext (k0ToBcris_padic p K a)

theorem k0ToFixedScalars_injective : Function.Injective (k0ToFixedScalars p K) :=
  (k0ToFixedScalars p K).injective

theorem k0ToFixedScalars_frobenius (x : ResidueCoefficients.K0 p K) :
    CrystallineScalars.localScalarFrobenius p K (k0ToFixedScalars p K x) =
      k0ToFixedScalars p K (ResidueCoefficients.coefficientFrobenius p K x) :=
  Subtype.ext (k0ToBcris_frobenius p K x)

def localPeriodActionOverK0 : CrystallineScalars.LocalGalois K →* (PeriodRing.Bcris p ≃ₐ[ResidueCoefficients.K0 p K] PeriodRing.Bcris p) where
  toFun σ := { (CrystallineScalars.localPeriodAction p K σ).toRingEquiv with commutes' := k0ToBcris_galois p K σ }
  map_one' := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun (CrystallineScalars.localPeriodAction p K).map_one x
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun ((CrystallineScalars.localPeriodAction p K).map_mul σ τ) x

theorem bcrisFrobenius_k0_smul (a : ResidueCoefficients.K0 p K) (b : PeriodRing.Bcris p) :
    CrystallineScalars.bcrisFrobeniusAlg p (a • b) = ResidueCoefficients.coefficientFrobenius p K a • CrystallineScalars.bcrisFrobeniusAlg p b := by
  change CrystallineScalars.bcrisFrobeniusAlg p (k0ToBcris p K a * b) =
    k0ToBcris p K (ResidueCoefficients.coefficientFrobenius p K a) * CrystallineScalars.bcrisFrobeniusAlg p b
  rw [map_mul, k0ToBcris_frobenius]

end NumberTheory.PadicHodge.PeriodInvariants.Embedding.Period

end

end OAI
