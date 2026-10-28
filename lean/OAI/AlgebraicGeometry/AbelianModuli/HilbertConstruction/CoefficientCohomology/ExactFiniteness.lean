import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ZeroInjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.FinitenessProperty
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiniteExact
import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-! # Exact Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology

noncomputable section

/-! Finiteness of genuine coefficient cohomology in all degrees is stable under each two-out-of-three operation in a short exact sequence. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R] [IsNoetherianRing R]
    (c : R →+* Γ(X, ⊤)) {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS

theorem FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.middle (h₁ : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₁)
    (h₃ : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₃) : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₂ := by
  intro n
  have : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj S.X₁) := h₁ n
  have : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj S.X₃) := h₃ n
  exact Noetherian.FiniteExact.noetherian_finite_of_exact ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).map S.f).hom
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).map S.g).hom (ExactPairs.ZariskiCohomology.coefficientCohomology_exact_middle c hS n)

theorem FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.right (h₁ : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₁)
    (h₂ : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₂) : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₃ := by
  intro n
  have : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj S.X₂) := h₂ n
  have : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj S.X₁) := h₁ (n + 1)
  exact Noetherian.FiniteExact.noetherian_finite_of_exact ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).map S.g).hom
    (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS n).hom (ExactPairs.ZariskiCohomology.coefficientCohomology_exact_right c hS n)

theorem FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.left (h₂ : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₂)
    (h₃ : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₃) : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c S.X₁ := by
  intro n
  cases n with
  | zero =>
      have : Mono S.f := hS.mono_f
      have : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).obj S.X₂) := h₂ 0
      exact Module.Finite.of_injective ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c 0).map S.f).hom
        (ZeroInjection.ZariskiCohomology.coefficientCohomology_zero_injective c S.f)
  | succ n =>
      have : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n).obj S.X₃) := h₃ n
      have : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).obj S.X₂) := h₂ (n + 1)
      exact Noetherian.FiniteExact.noetherian_finite_of_exact (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS n).hom
        ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (n + 1)).map S.f).hom (ExactPairs.ZariskiCohomology.coefficientCohomology_exact_left c hS n)

omit hS

instance FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.closedUnderExtensions : (FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.middle c hS h₁ h₃

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology
