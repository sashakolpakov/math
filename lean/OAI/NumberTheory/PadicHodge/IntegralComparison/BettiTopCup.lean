import OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup
import OAI.AlgebraicGeometry.AbelianVariety.BettiNumbers

/-! # Betti Top Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BettiTopCup

noncomputable section

/-! The genuine top Betti cup product of an abelian variety is nonzero. -/

theorem exists_nonzero (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ∃ v : Fin (2 * A.variety.complexDimension) → A.variety.complexCohomology 1,
      AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A (2 * A.variety.complexDimension) v ≠ 0 := by
  classical
  let : Module.Finite ℚ (A.variety.rationalCohomology 1) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite A.variety 1
  rw [← AlgebraicGeometry.AbelianVariety.BettiNumbers.Constructions.ExteriorCohomology.abelian_h1_finrank A]
  let n := Module.finrank ℚ (A.variety.rationalCohomology 1)
  let b := (Module.finBasis ℚ (A.variety.rationalCohomology 1)).baseChange ℂ
  let s : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp⟩
  let v : Fin n → AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1) :=
    fun i => b (Set.powersetCard.ofFinEmbEquiv.symm s i)
  have hv : exteriorPower.ιMulti ℂ n v ≠ 0 := by
    have hb := (b.exteriorPower n).ne_zero s
    simpa only [AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification, exteriorPower.basis_apply,
      exteriorPower.ιMulti_family, Function.comp_def, v] using hb
  have he : AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions.complexH1ExteriorCupEquiv A n (exteriorPower.ιMulti ℂ n v) ≠ 0 := by
    intro h
    apply hv
    apply (AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions.complexH1ExteriorCupEquiv A n).injective
    rw [h, map_zero]
  rw [AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup.Constructions.complexH1ExteriorCup_wedge] at he
  exact ⟨fun i => A.h1ScalarExtension (v i), he⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BettiTopCup
