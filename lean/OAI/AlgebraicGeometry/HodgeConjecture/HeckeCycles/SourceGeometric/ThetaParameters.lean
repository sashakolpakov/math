import Lean.LibrarySuggestions.Basic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectorParameters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Auxiliary
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRadialCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaReferenceCoverMap

/-! # Theta Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaParameters

noncomputable section

/-! Extract the same full Hecke character's parameters from the literal
original-source GeometricTheta theta class. Both finite-coordinate identities and
the complete auxiliary dilation family are constructed from named inputs. -/

-- Avoid expensive dependent-let cleanup in this large theorem.
set_option cleanup.letToHave false
open scoped Classical TensorProduct _root_.Matrix BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaCandidate.CM

namespace CM

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
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (W : Geometric.ThetaWitness.CM.Witness T hg hq hIsogenyQuotient)
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
    (hd : ∀ τ, d τ = v.val τ⁻¹)
    (j : CMExtraction.ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (hι : ∀ x : E, j (ιE x) = (x : ℂ))
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.H1))
    (hP : ∀ h, Commute P ((W.action.cohomologyAction h).baseChange ℂ))
    (hspace : LinearMap.range P ≤ HeckeCharacters.CM.Projectors.jointSpace (fun h => (W.action.cohomologyAction h).baseChange ℂ)
      (fun h => j (χ h)))
    (f : (T).sphericalInputs) (hne : P (Geometric.ThetaBettiClass.CM.classMap T hg hq hIsogenyQuotient W f) ≠ 0) :
    let Ψ := CMExtraction.ChosenOccurrence.Spectral.fullCharacterOfRational (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q) χ
    ∃ a : CMExtraction.ParameterChoices.Qbarˣ,
      (∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ (a : CMExtraction.ParameterChoices.Qbar))‖ = 1) ∧
      HeckeCharacters.CM.Projectors.jointSpace (CMExtraction.Intrinsic.CentralFinite.nativeFullHeckeActionOver (T).pel CMExtraction.ParameterChoices.Qbar W.action) Ψ ≠ ⊥ ∧
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple (T).pel CMExtraction.ParameterChoices.Qbar W.action Ψ)
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) (a : CMExtraction.ParameterChoices.Qbar)) ∧
      ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ),
        let Q := CMExtraction.Intrinsic.MinusculeParameters.nativeFullParameterTriple (T).pel CMExtraction.ParameterChoices.Qbar W.action
          (CMExtraction.Intrinsic.ParameterConjugation.Central.conjugateFullCharacter (F := CMExtraction.ParameterChoices.Qbar) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke places.count q) Ψ σ)
        (∃ z : CMExtraction.ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual Q (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) z)) ∧
        ∀ z : CMExtraction.ParameterChoices.Qbar, RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual Q (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple (CMExtraction.DualRadialSatake.Iwasawa.algebraicSqrt q j) z) →
          NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding (T).pel ιE ((T).pel.reference.distinguished, false)) z =
            (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (3 / 2) := by
  have hf := Source.Auxiliary.CM.exists_family E L T
    hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy hg hq hb j ιE hι v hv hd
  let u := Classical.choose hf
  have hu := (Classical.choose_spec hf).1
  have hfamily := (Classical.choose_spec hf).2
  let c := Fintype.equivFin (GeometricSource.CM.Positions E places)
  exact Source.ProjectorParameters.CM.parameter_from_family E L T rfl rfl
    (Geometric.ThetaReferenceCoverMap.CM.domain_eq E T B hb hμ) hg hq hIsogenyQuotient W v hv hd
    j ιE u hfamily c
    (ThetaRadialCoordinates.CM.active E L D hb b hN c u hu hq)
    (fun g _ p t => ThetaRadialCoordinates.CM.away E L D hb b hN c u hu g p t)
    hElementaryDivisors χ P hP hspace f hne

end CM

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaParameters
