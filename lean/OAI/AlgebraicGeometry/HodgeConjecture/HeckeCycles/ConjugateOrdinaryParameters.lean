import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Identity
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComparisonPlaceValuations
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ParameterArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenOccurrence

/-! # Conjugate Ordinary Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConjugateOrdinaryParameters.CM.Ordinary

noncomputable section

/-! Supply the exact ordinary-neighbor character values and the valuation
at the original comparison place, for every conjugate of the same full
source character. No operator or comparison-place matching is assumed. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenOccurrence.Spectral

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
  (hA : A.IsRealization D.pel hg hq hIsogenyQuotient)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.pel.complexEmbedding q)
  (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
  (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))

include hA in
theorem values
    (hdegree : Module.finrank ℚ E = 2 * s) (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D.pel hg hq hIsogenyQuotient)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (fullSide : Fin s → Bool)
    (hιE : ιE.toRingHom = j.fieldInClosure.comp D.pel.fieldEmbedding)
    (hχ : D.pel.localCharacter (D.pel.reference.distinguished, false) =
      j.localCharacter D.pel.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (a : CMExtraction.ParameterChoices.Qbar)
    (hnorm : ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j.complexClosure (σ a)‖ = 1)
    (hocc : HeckeCharacters.CM.Projectors.jointSpace (CMExtraction.Intrinsic.CentralFinite.nativeFullHeckeActionOver D.pel CMExtraction.ParameterChoices.Qbar A) (CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ) ≠ ⊥)
    (hproj : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual
      (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D.pel CMExtraction.ParameterChoices.Qbar A (CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ))
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure) a))
    (hval : ∀ (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) (z : CMExtraction.ParameterChoices.Qbar),
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple D.pel CMExtraction.ParameterChoices.Qbar A
        (CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ) σ))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure) z) →
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) z =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2))
    (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) :
    ∃ z b : CMExtraction.ParameterChoices.Qbar,
      z ≠ 0 ∧ b ≠ 0 ∧ (∀ γ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j.complexClosure (γ z)‖ = 1) ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * z) ^ n = 1) ∧
      (∀ i : Fin 3,
        σ (χ (A.basis (Neighbor.Types.CM.integralType D.pel.reference.distinguished fullSide i).val)) =
          (![(q : CMExtraction.ParameterChoices.Qbar) * b * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ + z),
            (q : CMExtraction.ParameterChoices.Qbar) * b ^ 2 * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ +
              CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * z + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ * z),
            b ^ 3 * z] : Fin 3 → CMExtraction.ParameterChoices.Qbar) i) ∧
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q j.iota z = (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) := by
  obtain ⟨z, b, hz, hb, hn, hp, hc, hvalues⟩ := CMExtraction.Intrinsic.ParameterArithmetic.native_conjugate_parameter_arithmetic
    D hg hq hIsogenyQuotient hdegree hTateComparison A hA hElementaryDivisors fullSide j.complexClosure a
    (CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ) hnorm hocc hproj σ
  refine ⟨z, b, hz, hb, hn, hc, ?_, ?_⟩
  · intro i
    have h := hvalues i
    rw [Ordinary.Identity.CM.OrdinaryHecke.native_operator fullSide D hg hq hIsogenyQuotient A hA i] at h
    simpa only [CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter_one_tmul, CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational_one_tmul] using h
  · exact ComparisonPlaceValuations.CM.normalized E ιE v D.pel A (CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ)
      j.complexClosure a hnorm hproj hval j.iota
      (ReferenceComparisonPlace.CM.Reference.closure_restriction E D.pel j ιE hιE hχ) σ z hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConjugateOrdinaryParameters.CM.Ordinary
