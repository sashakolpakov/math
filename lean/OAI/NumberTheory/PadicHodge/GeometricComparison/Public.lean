import Lean.Util.CollectAxioms
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
import OAI.NumberTheory.PadicHodge.GeometricComparison.CommittedConditional
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.Target

/-! # Public -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Public

noncomputable section

set_option Elab.async false

/-!
GeometricComparison for the original geometric model, with its preserved nine-prerequisite
conditional variant. The input is an actual number-field abelian variety
with an abelian scheme over ℤ_q and a compatible generic-fiber identification.
A projective embedding of the fixed complex fiber makes its genuine Hodge
subspaces explicit. Hecke operators are given by rational combinations of
extending integral endomorphisms, representing the specified algebra action.

Crystalline cohomology uses IntegralComparison's big Witt-vector crystalline site. The
unconditional proof uses the constructed integral comparison and its naturality,
the native top-degree point comparison, and the projective complex-form comparison.
Finiteness, comparisons, Frobenius weights, and weak admissibility occur only
in the conclusion, not in the geometric model or its construction helpers.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The preserved comparison theorem conditional on the nine stated prerequisites. -/
theorem comparison_and_weak_admissibility_on_hecke_summands_of_prerequisites
    (hIntegralModel : GraphPrerequisite.GeometricInput) (hTateComparison : GraphPrerequisite.HeckeInput)
    (hHodgeDecomposition : GraphPrerequisite.HodgeInput) (hPeriodInvariants : PeriodInvariants.CrystallineComparisonInput)
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hWeakAdmissibility : WeakAdmissibility.WeakAdmissibilityInput)
    (hCompletion : Completion.GeometricWeightInput.{0}) (hIntegralComparison : Integral.Shared.CharpolyInput.{0})
    (hBettiComparison : Betti.ComparisonInput)
    {K : Type} [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime]
    (κ : K →+* AlgebraicClosure ℚ)
    (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (jq : K →+* ℚ_[q])
    (hplace :
      (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (A : Geometry.AbelianH1Model K q jq)
    (H : Type) [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ := by
  exact CommittedConditional.albanese_hecke_frobenius_comparison_of_committed_prerequisites
    hIntegralModel hTateComparison hHodgeDecomposition hPeriodInvariants hCohomology hWeakAdmissibility hCompletion hIntegralComparison hBettiComparison
    q κ jComplex ι jq hplace A H ρ P ℓ hℓq

/-- Comparison and weak admissibility on the algebraic Hecke summands,
including scalar-conjugated eigendata on the same complex variety. -/
theorem comparison_and_weak_admissibility_on_hecke_summands
    {K : Type} [Field K] [NumberField K]
    (q : ℕ) [Fact q.Prime]
    (κ : K →+* AlgebraicClosure ℚ)
    (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (jq : K →+* ℚ_[q])
    (hplace :
      (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (A : Geometry.AbelianH1Model K q jq)
    (H : Type) [CommRing H] [Algebra ℚ H]
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ P ℓ := by
  exact A.native_comparisonTarget κ jComplex ι hplace ρ P ℓ hℓq

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Public
