import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Projective
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedAuxiliary
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedOrdinary
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedGeometric
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Established
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedField
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedAnalytic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedCMExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedPoissonAutomorphy

/-! # Input Assembly -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.InputAssembly.CM

noncomputable section

/-! Assemble the constructed input suppliers for the literal original
HeckeCycles target. The full ReferenceFamily, IntegralModel and GeometricComparison propositions remain explicit
premises. This is a conditional intermediate theorem. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem extraction_from_remaining_inputs
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
    (d : Gal(E/ℚ) → Bool) (hd : ∀ τ, d τ = v.val τ⁻¹)
    (Nbase : ℕ) (hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (hH : ∀ N, Albanese.Definitions.CM.HodgeComparison.IsCanonicalH1 (X N) (H N))
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : GeometricSource.CM.IsSourceBallThetaFamily E d Nbase X Θ)
    (hReferenceFamily : Moduli.CM.ReferenceFamilyInput) (hIntegralModel : ArithmeticModels.CM.IntegralModelInput)
    (hGeometricComparison : NumberTheory.PadicHodge.GeometricComparisonAdapter.CM.ExtremeSlopes.GeometricComparisonInput) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧
      ∀ N, 0 < N → N₀ ∣ N → Θ N ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v (H N) :=
  Projective.CM.extraction_from_named_inputs.{0} E v hv d hd Nbase hNbase X H hH Θ hsource
    (EstablishedAuxiliary.CM.reference_datum E) hReferenceFamily hIntegralModel
    EstablishedOrdinary.CM.Ordinary.native_reduction EstablishedOrdinary.CM.Ordinary.ordinary_operators
    EstablishedOrdinary.CM.Ordinary.ordinary_primes EstablishedAuxiliary.CM.cartier_duality_and_blocks
    EstablishedGeometric.CM.torsion_parameters (EstablishedField.CM.active_embedding E)
    EstablishedAnalytic.CM.determinant_cotangent EstablishedAnalytic.CM.completed_theta
    EstablishedField.CM.norm_one_scalar EstablishedField.CM.schrodinger_generators
    EstablishedPoissonAutomorphy.CM.full_input Established.CM.Hecke.spherical_hecke
    Established.CM.Hecke.theta_covariance EstablishedGeometric.CM.albanese
    EstablishedGeometric.CM.albanese_hodge_comparison EstablishedGeometric.CM.hodge_decomposition
    EstablishedAuxiliary.CM.elementary_divisors hGeometricComparison EstablishedCMExtraction.CM.full_input

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.InputAssembly.CM
