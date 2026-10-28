import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryHeckeModel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FixedOrdinaryReduction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AbsorbedPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OrdinaryPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource

/-! # Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Polynomial

noncomputable section

/-! The ordinary reduction at the opposite place uses the same retained
local characters and the identical IntegralModel Hecke model. -/

open scoped Classical
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting.CM OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Prerequisites
attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing
attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)
  (R : PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W)
  (M : Moduli.Intrinsic.RetainedModuli E P hP hμ v hv W R)
  {q : ℕ} [Fact q.Prime]
  (j₀ : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.integral.base.generic).obj M.integral.spread.toOver))

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice M.integral.base.extension.carrier M.integral.base.embedding q)
  (hj : (HeckeCycles.QadicModelMap.CM.localFieldEmbedding j).comp (algebraMap E M.integral.base.extension.carrier) =
    LocalEmbedding.ParameterChoices.nativeFieldEmbedding (HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C) (P.distinguished, true))

local notation "Q" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryModel.Intrinsic.retainedOrdinaryModel E P hP hμ v hv W R M
local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HeckeModel.Intrinsic.retainedHeckeModel E P hP hμ v hv W R M j₀ C
local notation "labels" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryLabels.Intrinsic.retainedOrdinaryLabels E P hP hμ
local notation "hlabels" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryLabels.Intrinsic.retainedOrdinaryLabels_conjugate E P hP hμ
local notation "a₀" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryHeckeModel.Intrinsic.retainedOrdinaryIndex E P hP hμ v hv W R M

variable (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)

local notation "hQ" => OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryModel.Intrinsic.retainedOrdinaryModel_periods E P hP hμ v hv W R M hs hdegree

def retainedOrdinarySide : Fin s → Bool := FixedOrdinaryReduction.Ordinary.fixedOrdinaryMultiplicative Q hQ labels a₀

include hj in
theorem retained_integral_ordinary_polynomial
    (hzero : P.distinguished.val = 0)
    (hsplit : j.HasSplitCoordinates (Q).extendedEmbedding)
    (T : (Q).GoodIntegralReduction q j) (hgeom : AbelianScheme.FrobeniusKernel.CMPoints.Construction.GeometricConclusion T)
    (ho : IsOpen (T.ordinaryLocus a₀))
    (hd : ∀ x : T.geom a₀, Dense {y : connectedComponent x | T.IsOrdinary a₀ y.val})
    (hden : Nat.Coprime q (Q).arithmetic.denominator)
    (hNeighborCounting : HeckeCycles.Neighbor.Counting.CM.NeighborCountingInput) (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{0, 0}) (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0}) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    (hg : (HD).HasIntegralModelGeometry) (hq : (HD).IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : (HD).RealizesIsogenyQuotient) :
    OrdinaryPolynomial.NativeOrdinaryPolynomial HD hg hq hIsogenyQuotient
      (retainedOrdinarySide E P hP hμ v hv W R M hs hdegree) j := by
  have hz : P.distinguished = (⟨0, hs⟩ : Fin s) := Fin.ext hzero
  have hlactive : labels (⟨0, (hQ).1⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E := by
    rw [← hz]
    exact OrdinaryLabels.Intrinsic.retainedOrdinaryLabels_active E P hP hμ
  obtain ⟨Y, Z, hred, _, _⟩ := FixedOrdinaryReduction.Ordinary.fixed_labels_native_reductions Q hQ j hsplit T
    hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient hgeom hden labels hlabels hlactive a₀
  let HD' := HeckeCycles.Witt.PELSource.CM.heckeData Q a₀ C
    (fun w => j.localCharacter (Q).extendedEmbedding (labels w))
  have heD : HD' = HD := OrdinaryHeckeModel.Intrinsic.retained_ordinary_hecke_model_eq E P hP hμ v hv W R M j₀ C j hj
  have hpol : ∀ (hg' : HD'.HasIntegralModelGeometry) (hq' : HD'.IsGoodCompletelySplitPrime)
      (hIsogenyQuotient' : HD'.RealizesIsogenyQuotient),
      OrdinaryPolynomial.NativeOrdinaryPolynomial HD' hg' hq' hIsogenyQuotient'
        (retainedOrdinarySide E P hP hμ v hv W R M hs hdegree) j := by
    intro hg' hq' hIsogenyQuotient' A' hA'
    apply SpecializedPolynomialPredicate.Intrinsic.specializedOrdinaryPolynomial_value (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model HD' hg' hq' j)
      (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization HD' hg' hq' hIsogenyQuotient' A' hA' j)
      (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke HD' A' (retainedOrdinarySide E P hP hμ v hv W R M hs hdegree))
    apply AbsorbedPolynomial.Ordinary.native_absorbed_polynomial Q hQ j hsplit T labels hlabels a₀ hden C
      (retainedOrdinarySide E P hP hμ v hv W R M hs hdegree) hTorsionQuotient Z Y hq' hg' hIsogenyQuotient' A' hA' ho hd
    change HeckeCycles.Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions Q hQ j hsplit T labels hlabels a₀ hden
      P.distinguished (FixedOrdinaryReduction.Ordinary.fixedOrdinaryMultiplicative Q hQ labels a₀) hTorsionQuotient Z Y
    rw [hz]
    exact hred
  exact OrdinaryPolynomial.native_ordinary_polynomial_transport HD' HD heD
    (retainedOrdinarySide E P hP hμ v hv W R M hs hdegree) j j (HEq.rfl) hpol
    hg hq hIsogenyQuotient

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Polynomial
