import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExactPairDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactFiniteness

/-! # Cohomology Dimension Balance -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyDimensionBalance

noncomputable section

/-! The dimension defect of the three cohomology terms is the sum of the adjacent connecting-map ranks. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem coefficientCohomology_dimension_balance_zero
    {K : Type u} [Field K] {X : Scheme.{u}} (c : K →+* Γ(X, ⊤))
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Module.Finite K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).obj S.X₂)]
    [Module.Finite K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).obj S.X₃)] :
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).obj S.X₁) +
      Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).obj S.X₃) =
        Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).obj S.X₂) +
          Module.finrank K (LinearMap.range (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS 0).hom) := by
  have : Mono S.f := hS.mono_f
  have hf := LinearMap.finrank_range_of_inj (CoefficientCohomology.ZeroInjection.ZariskiCohomology.coefficientCohomology_zero_injective c S.f)
  have hb := ExactPairDimension.exact_pair_dimension ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).map S.f).hom
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).map S.g).hom (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_middle c hS 0)
  have hc := ExactPairDimension.exact_pair_dimension ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).map S.g).hom
    (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS 0).hom (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_right c hS 0)
  omega

theorem coefficientCohomology_dimension_balance_succ
    {K : Type u} [Field K] {X : Scheme.{u}} (c : K →+* Γ(X, ⊤))
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (q : ℕ)
    [Module.Finite K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj S.X₁)]
    [Module.Finite K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj S.X₂)]
    [Module.Finite K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj S.X₃)] :
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj S.X₁) +
      Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj S.X₃) =
        Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj S.X₂) +
          Module.finrank K (LinearMap.range (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS q).hom) +
          Module.finrank K (LinearMap.range (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS (q + 1)).hom) := by
  have ha := ExactPairDimension.exact_pair_dimension (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS q).hom
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).map S.f).hom (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_left c hS q)
  have hb := ExactPairDimension.exact_pair_dimension ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).map S.f).hom
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).map S.g).hom (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_middle c hS (q + 1))
  have hc := ExactPairDimension.exact_pair_dimension ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).map S.g).hom
    (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS (q + 1)).hom (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_right c hS (q + 1))
  omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyDimensionBalance
