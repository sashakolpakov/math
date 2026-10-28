import OAI.AlgebraicGeometry.AbelianVariety.CupMap
import OAI.AlgebraicGeometry.AbelianVariety.BettiNumbers

/-! # Cup Dimensions -/

namespace OAI.AlgebraicGeometry.AbelianVariety.CupDimensions.Constructions.ExteriorCohomology

noncomputable section

open _root_.CategoryTheory
open scoped TensorProduct

/-- The source and target of the canonical cup map have the same finite dimension. -/
theorem exteriorCup_finrank_eq (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Module.finrank ℚ (⋀[ℚ]^n (A.variety.rationalCohomology 1)) =
      Module.finrank ℚ (A.variety.rationalCohomology n) := by
  let : Module.Finite ℚ (A.variety.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety 1
  rw [exteriorPower.finrank_eq, BettiNumbers.Constructions.ExteriorCohomology.abelian_h1_finrank, BettiNumbers.Constructions.ExteriorCohomology.abelian_rational_betti_number]

theorem exteriorCup_injective_iff_surjective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    Function.Injective (CupMap.Constructions.ExteriorCohomology.exteriorCup A n) ↔ Function.Surjective (CupMap.Constructions.ExteriorCohomology.exteriorCup A n) := by
  let : Module.Finite ℚ (A.variety.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety 1
  let : Module.Finite ℚ (A.variety.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety n
  exact LinearMap.injective_iff_surjective_of_finrank_eq_finrank (exteriorCup_finrank_eq A n)

theorem abelian_cupUnit_ne_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℚ) (Betti.Scheme.schemePointSpace A.toOver) ≠ 0 := by
  let : Nontrivial (A.variety.rationalCohomology 0) :=
    Module.nontrivial_of_finrank_pos (R := ℚ) (by rw [BettiNumbers.Constructions.ExteriorCohomology.abelian_rational_betti_number]; simp)
  obtain ⟨a, ha⟩ := exists_ne (0 : A.variety.rationalCohomology 0)
  intro h
  have hu := AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCup_cupUnit (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)) a
  change AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)) = 0 at h
  rw [h, map_zero] at hu
  exact ha hu.symm

theorem exteriorCup_zero_formula (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (x : ⋀[ℚ]^0 (A.variety.rationalCohomology 1)) :
    CupMap.Constructions.ExteriorCohomology.exteriorCup A 0 x = exteriorPower.zeroEquiv ℚ _ x •
      AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (Betti.Scheme.schemePointSpace A.toOver) := by
  have hmap : CupMap.Constructions.ExteriorCohomology.exteriorCup A 0 =
      (LinearMap.toSpanSingleton ℚ _ (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit
        (Betti.Scheme.schemePointSpace A.toOver))).comp (exteriorPower.zeroEquiv ℚ _).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, CupMap.Constructions.ExteriorCohomology.exteriorCup_wedge,
      ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.rationalH1Cup, LinearMap.comp_apply, LinearEquiv.coe_coe,
      exteriorPower.zeroEquiv_ιMulti, LinearMap.toSpanSingleton_apply, one_smul]
  exact LinearMap.congr_fun hmap x

theorem exteriorCup_zero_bijective (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    Function.Bijective (CupMap.Constructions.ExteriorCohomology.exteriorCup A 0) := by
  have hi : Function.Injective (CupMap.Constructions.ExteriorCohomology.exteriorCup A 0) := by
    intro x y h
    apply (exteriorPower.zeroEquiv ℚ _).injective
    rw [exteriorCup_zero_formula, exteriorCup_zero_formula] at h
    exact (smul_left_injective ℚ (abelian_cupUnit_ne_zero A)) h
  exact ⟨hi, (exteriorCup_injective_iff_surjective A 0).mp hi⟩

theorem exteriorCup_bijective_above_dimension (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (hn : 2 * A.variety.complexDimension < n) :
    Function.Bijective (CupMap.Constructions.ExteriorCohomology.exteriorCup A n) := by
  let : Module.Finite ℚ (A.variety.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety 1
  let : Subsingleton (⋀[ℚ]^n (A.variety.rationalCohomology 1)) :=
    CupMap.Constructions.ExteriorCohomology.exteriorPower_subsingleton_of_finrank_lt _ n (by rw [BettiNumbers.Constructions.ExteriorCohomology.abelian_h1_finrank]; exact hn)
  let : Subsingleton (A.variety.rationalCohomology n) :=
    ModuleCat.subsingleton_of_isZero (A.variety.rationalCohomology_isZero_of_dimension_lt n hn)
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end

end OAI.AlgebraicGeometry.AbelianVariety.CupDimensions.Constructions.ExteriorCohomology
