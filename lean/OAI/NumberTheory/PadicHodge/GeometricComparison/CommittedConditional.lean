import OAI.NumberTheory.PadicHodge.GeometricComparison.GraphPrerequisite
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Target

/-! # Committed Conditional -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CommittedConditional

noncomputable section

/-! GeometricComparison conditional on the nine named committed graph prerequisites.
The native construction proves the remaining geometric identifications.
Its assembly uses Cohomology, Completion, IntegralComparison and BettiComparison; the other graph prerequisites are
explicitly available in this entry point. The same constructed comparison
is used for naturality, endomorphism compatibility and weak admissibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem albanese_hecke_frobenius_comparison_of_committed_prerequisites
    (_hC44 : GraphPrerequisite.GeometricInput) (_hC47 : GraphPrerequisite.HeckeInput)
    (_hE20 : GraphPrerequisite.HodgeInput) (_hE61 : PeriodInvariants.CrystallineComparisonInput)
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (_hE63 : WeakAdmissibility.WeakAdmissibilityInput)
    (hCompletion : Completion.GeometricWeightInput.{0}) (hIntegralComparison : Integral.Shared.CharpolyInput.{0})
    (hBettiComparison : Betti.ComparisonInput)
    {K : Type} [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime]
    (κ : K →+* AlgebraicClosure ℚ)
    (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (jq : K →+* ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (A : Geometry.AbelianH1Model K q jq)
    (H : Type) [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ :=
  A.comparisonTarget_of_native_construction hCohomology hCompletion hIntegralComparison hBettiComparison
    κ jComplex ι hplace ρ P ℓ hℓq

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CommittedConditional
