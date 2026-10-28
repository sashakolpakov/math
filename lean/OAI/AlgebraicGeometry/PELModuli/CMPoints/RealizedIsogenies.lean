import OAI.AlgebraicGeometry.PELModuli.CMPoints.RealizedMaps
import OAI.ArithmeticGeometry.Descent.CMVariety.Faithfulness
import OAI.AlgebraicGeometry.AbelianVariety.PowerCohomology
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Realized Isogenies -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RealizedIsogenies

noncomputable section

/-! A rational Hodge isomorphism gives actual algebraic group maps
whose two composites are the same positive integer multiplication. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.AbelianVariety.PowerCohomology.Constructions.Exterior
open scoped _root_.CategoryTheory.MonObj

theorem abelianPower_isMonHom (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    IsMonHom (AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A n) := by
  have hn : AbelianScheme.TateComparison.End.endSchemeMap A.toOver (n : AbelianScheme.TateComparison.End.IntegralEnd A.toOver) =
      AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change AbelianScheme.TateComparison.End.endSchemeMap A.toOver ((n + 1 : ℕ) : AbelianScheme.TateComparison.End.IntegralEnd A.toOver) =
        (𝟙 A.toOver) ^ (n + 1)
      rw [Nat.cast_add, Nat.cast_one, AbelianScheme.TateComparison.BaseChange.endSchemeMap_add, ih,
        AbelianScheme.TateComparison.BaseChange.endSchemeMap_one, AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism, pow_succ]
  rw [← hn]
  infer_instance

theorem abelianH1Pullback_comp {A B C : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (f : A.toOver ⟶ B.toOver) (g : B.toOver ⟶ C.toOver) :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (f ≫ g) =
      (ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback f).comp (ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g) := by
  have h := (Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).map_comp g.op f.op
  exact congrArg (fun k => k.hom) h

theorem abelianH1Pullback_power (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A n) = (n : ℚ) • LinearMap.id := by
  ext x
  simpa only [ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback,
    pow_one, LinearMap.smul_apply, LinearMap.id_apply] using AbelianVariety.PowerCohomology.Constructions.Exterior.abelianPower_rationalBetti A n 1 x

theorem exists_realized_scalar_isogenies
    {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} {J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V}
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (S : ComplexMultiplication.CMKnownResults.CM.HodgeRealization J)
    (e : U ≃ₗ[ℚ] V) (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap H J e.toLinearMap)
    (hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap J H e.symm.toLinearMap) :
    ∃ d : ℕ, 0 < d ∧
      ∃ (f : R.abelianVariety.toOver ⟶ S.abelianVariety.toOver)
        (g : S.abelianVariety.toOver ⟶ R.abelianVariety.toOver),
        IsMonHom f ∧ IsMonHom g ∧
        f ≫ g = AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism R.abelianVariety d ∧
        g ≫ f = AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism S.abelianVariety d := by
  obtain ⟨n, hn, g, hg, hgn⟩ := RealizedMaps.exists_realized_algebraic_map R S e.toLinearMap he
  obtain ⟨m, hm, f, hf, hfm⟩ := RealizedMaps.exists_realized_algebraic_map S R e.symm.toLinearMap hi
  let : IsMonHom f := hf
  let : IsMonHom g := hg
  have : IsMonHom (AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism R.abelianVariety (m * n)) :=
    abelianPower_isMonHom _ _
  have : IsMonHom (AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism S.abelianVariety (m * n)) :=
    abelianPower_isMonHom _ _
  refine ⟨m * n, Nat.mul_pos hm hn, f, g, hf, hg, ?_, ?_⟩
  · apply ArithmeticGeometry.Descent.CMVariety.Faithfulness.Abelian.IntrinsicPeriods.algebraic_group_map_eq_of_h1Pullback_eq
    rw [abelianH1Pullback_comp, hfm, hgn, abelianH1Pullback_power]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      ComplexMultiplication.CMKnownResults.CM.HodgeRealization.realizedMap, LinearEquiv.coe_coe, map_smul,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
      LinearMap.id_apply, Nat.cast_mul, smul_smul, mul_comm]
  · apply ArithmeticGeometry.Descent.CMVariety.Faithfulness.Abelian.IntrinsicPeriods.algebraic_group_map_eq_of_h1Pullback_eq
    rw [abelianH1Pullback_comp, hfm, hgn, abelianH1Pullback_power]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      ComplexMultiplication.CMKnownResults.CM.HodgeRealization.realizedMap, LinearEquiv.coe_coe, map_smul,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
      LinearMap.id_apply, Nat.cast_mul, smul_smul, mul_comm]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RealizedIsogenies
