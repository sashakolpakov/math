import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults
import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent

/-! # Known Algebraicity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Algebraic realization of rational maps on abelian `H¹`

The established full-faithfulness of the weight-one realization is used
only in its fullness direction, allowing rational multiples of actual
algebraic group homomorphisms. Pullbacks are the existing singular
cohomology pullbacks induced by those scheme morphisms.

Source: Milne, *Shimura varieties and moduli*, Theorems 4.4 and 7.12,
after clearing denominators and dualizing. No higher-degree cycle
algebraicity is assumed.
-/

open _root_.CategoryTheory

section

/-- The actual rational pullback of an algebraic map between abelian varieties. -/
def CMAbelianVariety.CM.AbelianVariety.h1Pullback {A B : CMAbelianVariety.CM.AbelianVariety} (f : B.toOver ⟶ A.toOver) :
    A.variety.rationalCohomology 1 →ₗ[ℚ] B.variety.rationalCohomology 1 :=
  (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom

/-- Complex span of scalar-extended pullbacks by genuine algebraic group
homomorphisms; the direction is contravariant. -/
def CMAbelianVariety.CM.AbelianVariety.algebraicH1PullbackSpan (A B : CMAbelianVariety.CM.AbelianVariety) :
    Submodule ℂ (WeightOne.CM.Complexification (A.variety.rationalCohomology 1) →ₗ[ℂ]
      WeightOne.CM.Complexification (B.variety.rationalCohomology 1)) :=
  Submodule.span ℂ {f | ∃ g : B.toOver ⟶ A.toOver,
    IsMonHom g ∧ (CMAbelianVariety.CM.AbelianVariety.h1Pullback g).baseChange ℂ = f}

end

namespace KnownAlgebraicity.CM.KnownResults

/-- Rational type-preserving maps of actual abelian `H¹` come from
rational multiples of algebraic group homomorphisms. Both types are
expressed using the actual closed-form Betti subspaces. -/
def RationalH1MapsAreAlgebraic : Prop :=
  ∀ (A B : CMAbelianVariety.CM.AbelianVariety)
    (f : A.variety.rationalCohomology 1 →ₗ[ℚ] B.variety.rationalCohomology 1),
    (∀ x ∈ A.h1Holomorphic, f.baseChange ℂ x ∈ B.h1Holomorphic) →
    (∀ x ∈ A.h1Antiholomorphic, f.baseChange ℂ x ∈ B.h1Antiholomorphic) →
    ∃ (r : ℚ) (g : B.toOver ⟶ A.toOver), IsMonHom g ∧ f = r • CMAbelianVariety.CM.AbelianVariety.h1Pullback g

end KnownAlgebraicity.CM.KnownResults

variable (hknown : KnownAlgebraicity.CM.KnownResults.RationalH1MapsAreAlgebraic) (A B : CMAbelianVariety.CM.AbelianVariety)
  (H : WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
  (J : WeightOne.CM.WeightOneHodgeStructure (B.variety.rationalCohomology 1))
  (hH : H.holomorphic = A.h1Holomorphic) (aH : H.antiholomorphic = A.h1Antiholomorphic)
  (hJ : J.holomorphic = B.h1Holomorphic) (aJ : J.antiholomorphic = B.h1Antiholomorphic)

include hknown hH aH hJ aJ

/-- Apply fullness to the project's rational Hodge-map predicate. -/
theorem CMAbelianVariety.CM.AbelianVariety.hodgeMap_eq_rational_pullback
    (f : A.variety.rationalCohomology 1 →ₗ[ℚ] B.variety.rationalCohomology 1)
    (hf : WeightOne.CM.IsHodgeMap H J f) :
    ∃ (r : ℚ) (g : B.toOver ⟶ A.toOver), IsMonHom g ∧ f = r • CMAbelianVariety.CM.AbelianVariety.h1Pullback g := by
  apply hknown A B f
  · intro x hx
    rw [← hH] at hx
    rw [← hJ]
    exact hf x hx
  · intro x hx
    rw [← aH] at hx
    rw [← aJ]
    exact hf.map_antiholomorphic hx

/-- The already proved trace-descent span can now be interpreted as a
span of actual algebraic pullbacks, using only the established `H¹` input. -/
theorem CMAbelianVariety.CM.AbelianVariety.rationalHodgeMapSpan_le_algebraicH1PullbackSpan :
    Hodge.MapDescent.CM.rationalHodgeMapSpan H J ≤ A.algebraicH1PullbackSpan B := by
  apply Submodule.span_le.mpr
  rintro f ⟨q, hq, rfl⟩
  obtain ⟨r, g, hg, rfl⟩ := CMAbelianVariety.CM.AbelianVariety.hodgeMap_eq_rational_pullback hknown A B H J hH aH hJ aJ q hq
  rw [LinearMap.baseChange_smul]
  apply Submodule.smul_of_tower_mem
  exact Submodule.subset_span ⟨g, hg, rfl⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication
