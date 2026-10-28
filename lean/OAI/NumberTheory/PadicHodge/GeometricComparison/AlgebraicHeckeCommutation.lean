import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicHeckeComparisons
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianComparisonNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCommutationTransport
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.HeckeAction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ComplexBetti

/-! # Algebraic Hecke Commutation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Pairwise commutation of the actual complex, number-field, and local Hecke operators follows from the rational action and the constructed geometric comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : A.HeckeRealization H)

include P in
theorem Geometry.AbelianH1Model.complexBettiHecke_commute (h k : H) :
    Commute (A.complexBettiHecke j ρ h) (A.complexBettiHecke j ρ k) :=
  HeckeCommutationTransport.GeneralizedHecke.commute_transport (A.rationalComplexBettiEquiv j P)
    ((A.bettiHecke j ρ h).baseChange ℂ) ((A.bettiHecke j ρ k).baseChange ℂ)
    (A.complexBettiHecke j ρ h) (A.complexBettiHecke j ρ k)
    (A.rationalComplexBettiEquiv_hecke j P ρ h) (A.rationalComplexBettiEquiv_hecke j P ρ k)
    (HeckeCommutation.GeneralizedHecke.commutes_baseChange ℂ _ _ (A.bettiHecke_commute j P ρ h k))

include P in
theorem Geometry.AbelianH1Model.algebraicHecke_commute (hBettiComparison : Betti.ComparisonInput) (h k : H) :
    Commute (A.algebraicHecke ρ h) (A.algebraicHecke ρ k) := by
  let : Algebra K ℂ := j.toAlgebra
  obtain ⟨cmp, hcmp, _⟩ := A.algebraicBettiComparison_exists hBettiComparison j P
  apply HeckeCommutationTransport.GeneralizedHecke.commute_baseChange_reflect ℂ
  exact HeckeCommutationTransport.GeneralizedHecke.commute_reflect cmp
    (A.complexAlgebraicHecke j ρ h) (A.complexAlgebraicHecke j ρ k)
    (A.complexBettiHecke j ρ h) (A.complexBettiHecke j ρ k)
    (A.algebraicBettiComparison_hecke j cmp hcmp ρ h) (A.algebraicBettiComparison_hecke j cmp hcmp ρ k)
    (A.complexBettiHecke_commute j P ρ h k)

include P in
theorem Geometry.AbelianH1Model.deRhamHecke_commute (hBettiComparison : Betti.ComparisonInput) (h k : H) :
    Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k) := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  exact HeckeCommutationTransport.GeneralizedHecke.commute_transport A.localAlgebraicComparison
    (A.localAlgebraicHecke ρ h) (A.localAlgebraicHecke ρ k) (A.deRhamHecke ρ h) (A.deRhamHecke ρ k)
    (A.localAlgebraicComparison_hecke ρ h) (A.localAlgebraicComparison_hecke ρ k)
    (HeckeCommutation.GeneralizedHecke.commutes_baseChange ℚ_[q] _ _ (A.algebraicHecke_commute j P ρ hBettiComparison h k))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
