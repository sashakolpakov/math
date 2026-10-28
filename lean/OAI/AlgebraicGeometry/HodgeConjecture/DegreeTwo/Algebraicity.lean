import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Established

/-! # Algebraicity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Algebraicity.CM

/-!
# DegreeTwo: unconditional algebraicity in weight one and degree two

These entrypoints discharge every external proof input in the accepted
conditional proof. The original conditional declarations remain unchanged.
All maps, Hodge pieces, positive denominator bounds, pointed universal
properties, and geometric cycle constructors are the original ones.
-/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

/-- Every rational Hodge map on H¹ is an algebraic group pullback after
multiplication by a positive integer. -/
theorem weight_one_algebraicity_unconditional
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ]
      B.variety.rationalCohomology 1)
    (hu10 : ∀ x ∈ A.h1Holomorphic,
      u.baseChange ℂ x ∈ B.h1Holomorphic)
    (hu01 : ∀ x ∈ A.h1Antiholomorphic,
      u.baseChange ℂ x ∈ B.h1Antiholomorphic) :
    ∃ n : ℕ, 0 < n ∧
      ∃ g : B.toOver ⟶ A.toOver,
        IsMonHom g ∧
        ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g = (n : ℚ) • u := by
  exact IntrinsicWeight.Constructions.weight_one_algebraicity
    Established.Constructions.e06Input Established.Constructions.e07Input Established.Constructions.e08Input A B u hu10 hu01

/-- The pointed Albanese pullback identifies actual rational H¹ and both
complex Hodge pieces, with the full algebraic universal property. -/
theorem albanese_h1_identification_unconditional
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (a : X.toOver ⟶ A.toOver)
      (eQ : A.variety.rationalCohomology 1 ≃ₗ[ℚ]
        X.rationalCohomology 1)
      (eC : A.variety.complexCohomology 1 ≃ₗ[ℂ]
        X.complexCohomology 1),
      x₀ ≫ a = η[A.toOver] ∧
      (∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
        x₀ ≫ f = η[B.toOver] →
          ∃! g : A.toOver ⟶ B.toOver,
            IsMonHom g ∧ a ≫ g = f) ∧
      eQ.toLinearMap =
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom ∧
      eC.toLinearMap =
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 a).hom ∧
      (A.variety.pureBettiSubspace 1 0).map eC.toLinearMap =
        X.pureBettiSubspace 1 0 ∧
      (A.variety.pureBettiSubspace 0 1).map eC.toLinearMap =
        X.pureBettiSubspace 0 1 := by
  exact Transport.Constructions.albanese_h1_identification
    Established.Constructions.e07Input Established.Constructions.e08Input X x₀

/-- Every rational degree-two Hodge class is the actual geometric class of
a rational algebraic cycle of codimension one. -/
theorem degree_two_algebraicity_unconditional
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (α : V.rationalCohomology 2)
    (hα : V.IsRationalHodgeClass 1 α) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1,
      V.geometricCycleClassMap 1 z = α := by
  have hspan := Established.Constructions.e09Input V.presentation α
    (Presentation.Constructions.presentation_isRationalHodgeClass V 1 α hα)
  have hgeometric : Submodule.span ℚ
      (Set.range (DivisorClass.Chern.First.firstChernClassQ V.presentation)) ≤
      LinearMap.range (V.geometricCycleClassMap 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨L, rfl⟩
    rw [L.firstChernClassQ_eq_algebraicDivisorClass]
    exact Established.Constructions.algebraicDivisorClass_is_geometric V L
  exact hgeometric hspan

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Algebraicity.CM
