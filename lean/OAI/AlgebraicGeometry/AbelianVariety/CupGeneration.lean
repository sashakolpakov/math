import OAI.AlgebraicGeometry.AbelianVariety.CupRange
import OAI.AlgebraicGeometry.AbelianVariety.DoublingDifference
import OAI.AlgebraicGeometry.AbelianVariety.ProductSpanning

/-! # Cup Generation -/

namespace OAI.AlgebraicGeometry.AbelianVariety.CupGeneration.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory

theorem doublingDifference_mem_exteriorCup_range (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (hn : 1 < n)
    (ih : ∀ k < n, Function.Surjective (CupMap.Constructions.ExteriorCohomology.exteriorCup A k))
    (x : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) n) :
    DoublingDifference.Constructions.ExteriorCohomology.doublingDifference A n x ∈ LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A n) := by
  let S := (LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A n)).comap (DoublingDifference.Constructions.ExteriorCohomology.doublingDifference A n)
  have htop : S = ⊤ := by
    apply ProductSpanning.Constructions.ExteriorCohomology.abelianProduct_cohomology_spanned A n S
    intro p q hpq a b
    subst n
    change DoublingDifference.Constructions.ExteriorCohomology.doublingDifference A (p + q)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A) p q
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodFst p a)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) TopCat.prodSnd q b)) ∈
      LinearMap.range (CupMap.Constructions.ExteriorCohomology.exteriorCup A (p + q))
    rw [DoublingDifference.Constructions.ExteriorCohomology.doublingDifference_cross]
    by_cases hp : p = 0
    · subst p
      have hq : q ≠ 0 := by omega
      simp only [zero_pow hq, pow_zero, sub_zero, sub_self, zero_smul]
      exact (LinearMap.range _).zero_mem
    by_cases hq : q = 0
    · subst q
      simp only [pow_zero, zero_pow hp, sub_self, zero_smul]
      exact (LinearMap.range _).zero_mem
    simp only [zero_pow hq, zero_pow hp, sub_zero, one_smul]
    exact CupRange.Constructions.ExteriorCohomology.cup_mem_exteriorCup_range A p q a (ih p (by omega) a) b (ih q (by omega) b)
  have hx : x ∈ S := htop.symm ▸ Submodule.mem_top
  exact hx

/-- The genuine rational cohomology ring of an abelian variety is generated in degree one. -/
theorem exteriorCup_surjective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Function.Surjective (CupMap.Constructions.ExteriorCohomology.exteriorCup A n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n
      exact (CupDimensions.Constructions.ExteriorCohomology.exteriorCup_zero_bijective A).surjective
    by_cases h1 : n = 1
    · subst n
      exact (CupMap.Constructions.ExteriorCohomology.exteriorCup_one_bijective A).surjective
    have hn : 1 < n := by omega
    intro a
    have hmem := doublingDifference_mem_exteriorCup_range A n hn ih
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A) n a)
    rw [DoublingDifference.Constructions.ExteriorCohomology.doublingDifference_mulPullback] at hmem
    have hc : (2 : ℚ) ^ n - 2 ≠ 0 := by
      have hlt : (2 : ℚ) < 2 ^ n := by
        simpa only [pow_one] using pow_lt_pow_right₀ (show (1 : ℚ) < 2 by norm_num) hn
      exact sub_ne_zero.mpr (ne_of_gt hlt)
    exact (Submodule.smul_mem_iff_of_isUnit _ (isUnit_iff_ne_zero.mpr hc)).mp hmem

/-- Cup product induces the rational exterior-cohomology isomorphism in every degree. -/
theorem exteriorCup_bijective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Function.Bijective (CupMap.Constructions.ExteriorCohomology.exteriorCup A n) :=
  ⟨(CupDimensions.Constructions.ExteriorCohomology.exteriorCup_injective_iff_surjective A n).mpr (exteriorCup_surjective A n),
    exteriorCup_surjective A n⟩

def rationalExteriorCupEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    (⋀[ℚ]^n (A.variety.rationalCohomology 1)) ≃ₗ[ℚ] A.variety.rationalCohomology n :=
  LinearEquiv.ofBijective (CupMap.Constructions.ExteriorCohomology.exteriorCup A n) (exteriorCup_bijective A n)

end

end OAI.AlgebraicGeometry.AbelianVariety.CupGeneration.Constructions.ExteriorCohomology
