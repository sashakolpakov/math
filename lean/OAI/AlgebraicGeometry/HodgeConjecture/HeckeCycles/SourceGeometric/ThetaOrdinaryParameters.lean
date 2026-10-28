import Lean.LibrarySuggestions.Basic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaParameters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConjugateOrdinaryParameters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum

/-! # Theta Ordinary Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaOrdinaryParameters.CM.Ordinary

noncomputable section

/-! Every nonzero projector on an original-source GeometricTheta theta class
has the exact ordinary-neighbor character values and original-place
valuation signs at all conjugates, from the full named prerequisites. -/

open scoped Classical TensorProduct _root_.Matrix BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K places.count q) (hb : D.reference.b = B.b)
  (hμ : D.reference.μ = E.val.toRingHom)
  {J : Type*} [Fintype J] [DecidableEq J] [Submodule.IsLattice ℚ D.reference.lattice]
  (b : Module.Basis J ℤ D.reference.lattice) (hN : 0 < D.level)

local notation "T" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM.data E L D hb b hN

--
include hμ in
abbrev parameters
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, 0, 0, 0})
    (hTateComparison : TateComparison.CM.TateComparisonInput) (hConstruction : PELModuli.IntegralModel.Albanese.ConstructionInput)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness T hg hq hIsogenyQuotient)
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
    (hd : ∀ τ, d τ = v.val τ⁻¹)
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (hχ : D.localCharacter (D.reference.distinguished, false) =
      j.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
    (fullSide : Fin places.count → Bool)
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.H1))
    (hP : ∀ h, Commute P ((W.action.cohomologyAction h).baseChange ℂ))
    (hspace : LinearMap.range P ≤ HeckeCharacters.CM.Projectors.jointSpace (fun h => (W.action.cohomologyAction h).baseChange ℂ)
      (fun h => j.complexClosure (χ h)))
    (f : (T).sphericalInputs) (hne : P (Geometric.ThetaBettiClass.CM.classMap T hg hq hIsogenyQuotient W f) ≠ 0) :
    ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ∃ z c : CMExtraction.ParameterChoices.Qbar,
      z ≠ 0 ∧ c ≠ 0 ∧ (∀ γ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j.complexClosure (γ z)‖ = 1) ∧
      (∃ n : ℕ, 0 < n ∧ (c ^ 3 * z) ^ n = 1) ∧
      (∀ i : Fin 3,
        σ (χ (W.action.basis (Neighbor.Types.CM.integralType D.reference.distinguished fullSide i).val)) =
          (![(q : CMExtraction.ParameterChoices.Qbar) * c * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ + z),
            (q : CMExtraction.ParameterChoices.Qbar) * c ^ 2 * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ +
              CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure * z + (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j.complexClosure)⁻¹ * z),
            c ^ 3 * z] : Fin 3 → CMExtraction.ParameterChoices.Qbar) i) ∧
      NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q j.iota z =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E (ReferenceComparisonPlace.CM.SourceClosureChoice.embedding E D j) σ)) : ℚ) * (-3 / 2) := by
  let ιE := ReferenceComparisonPlace.CM.SourceClosureChoice.embedding E D j
  have hf := ThetaParameters.CM.parameters E L D hb hμ b hN
    hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy hg hq hIsogenyQuotient W v hv hd
    j.complexClosure ιE (ReferenceComparisonPlace.CM.SourceClosureChoice.complex_compatibility E D j hg hμ)
    hElementaryDivisors χ P hP hspace f hne
  let a := Classical.choose hf
  have ha := Classical.choose_spec hf
  have hdegree := ReferenceDatum.CM.source_degree E places
  have hc : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D hg hq hIsogenyQuotient :=
    hTateComparison places.count hdegree.1 hdegree.2 q D hg hq hIsogenyQuotient hConstruction hElementaryDivisors
  exact fun σ => ConjugateOrdinaryParameters.CM.Ordinary.values E T hg hq hIsogenyQuotient W.action W.realization
    j ιE v hdegree.2 hc hElementaryDivisors fullSide rfl hχ χ (a : CMExtraction.ParameterChoices.Qbar)
    ha.1 ha.2.1 ha.2.2.1 (fun τ z hz => (ha.2.2.2 τ).2 z hz) σ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaOrdinaryParameters.CM.Ordinary
