import OAI.AlgebraicGeometry.PELModuli.CMPoints.CommonHodgeMultipliers
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Additivity

/-! # Hodge Pi Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HodgePiFactorization

noncomputable section

/-! A realized finite product of weight-one Hodge structures has an
actual algebraic splitting up to one positive integer multiplication. -/

open _root_.CategoryTheory
open scoped Classical _root_.CategoryTheory.MonObj

structure ScalarFactorization {I : Type*} [Fintype I]
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (B : I → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) where
  multiplier : ℕ
  positive : 0 < multiplier
  forward : ∀ i, A.toOver ⟶ (B i).toOver
  backward : ∀ i, (B i).toOver ⟶ A.toOver
  forward_group : ∀ i, IsMonHom (forward i)
  backward_group : ∀ i, IsMonHom (backward i)
  diagonal : ∀ i, backward i ≫ forward i = AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism (B i) multiplier
  offDiagonal : ∀ i j, i ≠ j → backward i ≫ forward j = 1
  total : (∏ i, forward i ≫ backward i) = AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A multiplier

theorem exists_hodgePi_scalar_factorization
    {I V : Type*} [Fintype I] [AddCommGroup V] [Module ℚ V]
    (H : I → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (Products.hodgePi H))
    (S : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i)) :
    Nonempty (ScalarFactorization R.abelianVariety (fun i => (S i).abelianVariety)) := by
  classical
  obtain ⟨n, m, hn, hm, f, g, hf, hg, hfn, hgm⟩ := CommonHodgeMultipliers.exists_hodgePi_algebraic_factor_maps H R S
  let (i : I) : IsMonHom (f i) := hf i
  let (i : I) : IsMonHom (g i) := hg i
  refine ⟨⟨m * n, Nat.mul_pos hm hn, f, g, hf, hg, ?_, ?_, ?_⟩⟩
  · intro i
    let : IsMonHom (AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism (S i).abelianVariety (m * n)) := RealizedIsogenies.abelianPower_isMonHom _ _
    apply ArithmeticGeometry.Descent.CMVariety.Faithfulness.Abelian.IntrinsicPeriods.algebraic_group_map_eq_of_h1Pullback_eq
    rw [RealizedIsogenies.abelianH1Pullback_comp, hfn, hgm, RealizedIsogenies.abelianH1Pullback_power]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, ComplexMultiplication.CMKnownResults.CM.HodgeRealization.realizedMap,
      LinearEquiv.coe_coe, map_smul, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply, LinearMap.proj_apply, LinearMap.single_apply,
      Pi.single_eq_same, LinearMap.id_apply, Nat.cast_mul, smul_smul]
    rw [mul_comm (n : ℚ)]
  · intro i j hij
    let : IsMonHom (1 : (S i).abelianVariety.toOver ⟶ (S j).abelianVariety.toOver) :=
      Additivity.algebraic_one_isMonHom _ _
    apply ArithmeticGeometry.Descent.CMVariety.Faithfulness.Abelian.IntrinsicPeriods.algebraic_group_map_eq_of_h1Pullback_eq
    rw [RealizedIsogenies.abelianH1Pullback_comp, hfn, hgm, Additivity.abelianH1Pullback_one]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, ComplexMultiplication.CMKnownResults.CM.HodgeRealization.realizedMap,
      LinearEquiv.coe_coe, map_smul, LinearEquiv.symm_apply_apply,
      LinearMap.proj_apply, LinearMap.single_apply, Pi.single_eq_of_ne hij,
      map_zero, smul_zero, LinearMap.zero_apply]
  · let : IsMonHom (∏ i, f i ≫ g i) := Additivity.algebraic_prod_isMonHom _ _ (fun i _ => inferInstance)
    let : IsMonHom (AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism R.abelianVariety (m * n)) := RealizedIsogenies.abelianPower_isMonHom _ _
    apply ArithmeticGeometry.Descent.CMVariety.Faithfulness.Abelian.IntrinsicPeriods.algebraic_group_map_eq_of_h1Pullback_eq
    rw [Additivity.abelianH1Pullback_prod, RealizedIsogenies.abelianH1Pullback_power]
    simp_rw [RealizedIsogenies.abelianH1Pullback_comp, hfn, hgm]
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      ComplexMultiplication.CMKnownResults.CM.HodgeRealization.realizedMap, LinearEquiv.coe_coe, map_smul,
      LinearEquiv.symm_apply_apply, LinearMap.proj_apply, LinearMap.single_apply,
      LinearMap.id_apply, Nat.cast_mul, smul_smul]
    rw [← Finset.smul_sum, ← map_sum]
    have hsum : (∑ i : I, Pi.single i (R.comparison.symm x i)) = R.comparison.symm x := by
      ext i
      simp
    rw [hsum, LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HodgePiFactorization
