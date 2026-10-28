import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.Additivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorFiniteCoproducts

/-! # Finite Coproducts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology

noncomputable section

/-! Finite direct sums preserve finiteness of genuine coefficient cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite.coproduct {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) {ι : Type u} [Finite ι] (M : ι → X.Modules)
    (hM : ∀ i, FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c (M i)) : FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite c (∐ M) := by
  intro n
  exact Additive.FunctorFiniteCoproducts.additive_functor_finite_coproduct (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c n) M (fun i ↦ hM i n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology
