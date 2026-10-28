import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrimeBounds
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion

/-! # Hecke Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic

noncomputable section

/-! The later local characters are constructed on the previously chosen
IntegralModel model. Its full geometry and every good-prime condition are proved
for the identical integral spread and principal level. -/

open scoped Classical _root_.Matrix
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)

def retainedLocalCharacter (w : Fin s × Bool) : NumberField.RingOfIntegers E →+* ℤ_[q] :=
  HeckeCycles.PairedCompletion.CM.pairedCharacter E j (algebraMap E M.integral.base.extension.carrier)
    (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) w

variable (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
  ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver))

abbrev retainedHeckeModel : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E M.integral.base.extension.carrier s q :=
  M.integral.heckeData C (retainedLocalCharacter E P hP hμ v hv W R M j)

theorem retainedHeckeModel_geometry :
    (retainedHeckeModel E P hP hμ v hv W R M j C).HasIntegralModelGeometry :=
  M.integral.heckeData_geometry C (retainedLocalCharacter E P hP hμ v hv W R M j)
    hP (by simpa only [RingHom.comp_id] using hμ.symm) M.deep

theorem retainedHeckeModel_good_prime
    (hgood : PrimeBounds.Intrinsic.RetainedPrimeConditions E P hP hμ v hv W R M q) :
    (retainedHeckeModel E P hP hμ v hv W R M j C).IsGoodCompletelySplitPrime := by
  refine ⟨?_, ?_, hgood.level_coprime, hgood.denominator_coprime, hgood.polarization_coprime⟩
  · exact HeckeCycles.PairedCompletion.CM.pairedCompletion_bijective E j (algebraMap E M.integral.base.extension.carrier)
      (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ)
      (hgood.split_coordinates M.integral.base.extension.carrier M.integral.base.embedding
        (algebraMap E M.integral.base.extension.carrier) j)
  · exact HeckeCycles.PairedCompletion.CM.pairedCharacter_conjugate E j (algebraMap E M.integral.base.extension.carrier)
      (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic
