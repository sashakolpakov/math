import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.Invertibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.IntrinsicNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Composition
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCommutation

/-! # Hecke Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Construct the actual de Rham Frobenius and its restriction to every supplied finite-coefficient Hecke summand. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.deRhamFrobeniusEquiv (hCohomology : Cohomology.Good.GoodReductionInput.{0}) : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham :=
  WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv (A.crystallineDeRhamEquiv hCohomology) (A.crystallineFrobeniusEquiv hCohomology)

theorem Geometry.AbelianH1Model.crystallinePullback_commutes_equiv (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (f : A.ExtendingEndomorphism) :
    Commute (A.crystallinePullback f) (A.crystallineFrobeniusEquiv hCohomology).toLinearMap := by
  rw [A.crystallineFrobeniusEquiv_toLinearMap]
  exact (A.crystallineFrobenius_commutes f).symm

theorem Geometry.AbelianH1Model.deRhamPullback_commutes_frobenius (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (f : A.ExtendingEndomorphism) :
    Commute (A.deRhamPullback f) (A.deRhamFrobeniusEquiv hCohomology).toLinearMap :=
  HeckeCommutation.GeneralizedHecke.conjugate_commutes (A.crystallineDeRhamEquiv hCohomology)
    (A.crystallinePullback f) (A.deRhamPullback f) (A.crystallineFrobeniusEquiv hCohomology)
    (A.crystallineDeRhamEquiv_naturality hCohomology f) (A.crystallinePullback_commutes_equiv hCohomology f)

variable {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.deRhamHecke_commutes_frobenius (hCohomology : Cohomology.Good.GoodReductionInput.{0})
    (ρ : A.HeckeRealization H) (h : H) :
    Commute (A.deRhamHecke ρ h) (A.deRhamFrobeniusEquiv hCohomology).toLinearMap :=
  HeckeCommutation.GeneralizedHecke.commutes_weighted_sum (ρ.presentation h) (fun a : ℚ => (a : ℚ_[q]))
    A.deRhamPullback (A.deRhamFrobeniusEquiv hCohomology).toLinearMap (A.deRhamPullback_commutes_frobenius hCohomology)

def Geometry.AbelianH1Model.heckeSummandFrobenius (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (ρ : A.HeckeRealization H)
    (χ : H → AlgebraicClosure ℚ_[q]) (L : Linear.FiniteHeckeCoefficientField q χ) :
    A.deRhamHeckeSummand ρ χ L ≃ₗ[L.field] A.deRhamHeckeSummand ρ χ L :=
  HeckeSummandStability.GeneralizedHecke.restriction
    ((A.deRhamFrobeniusEquiv hCohomology).baseChange ℚ_[q] L.field A.DeRham A.DeRham)
    (fun h => (A.deRhamHecke ρ h).baseChange L.field) L.character
    (fun h => HeckeCommutation.GeneralizedHecke.commutes_baseChange L.field (A.deRhamHecke ρ h)
      (A.deRhamFrobeniusEquiv hCohomology).toLinearMap (A.deRhamHecke_commutes_frobenius hCohomology ρ h))

theorem Geometry.AbelianH1Model.heckeSummandFrobenius_apply (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (ρ : A.HeckeRealization H)
    (χ : H → AlgebraicClosure ℚ_[q]) (L : Linear.FiniteHeckeCoefficientField q χ)
    (x : A.deRhamHeckeSummand ρ χ L) :
    (A.heckeSummandFrobenius hCohomology ρ χ L x : L.field ⊗[ℚ_[q]] A.DeRham) =
      Linear.coefficientFrobenius L.field (A.deRhamFrobeniusEquiv hCohomology).toLinearMap
        (x : L.field ⊗[ℚ_[q]] A.DeRham) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
