import OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup
import OAI.AlgebraicGeometry.AbelianVariety.HodgeCharacters

/-! # Pure Monomials -/

namespace OAI.AlgebraicGeometry.AbelianVariety.PureMonomials.Constructions.ExteriorCohomology

noncomputable section

open scoped TensorProduct Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
local instance (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) : LinearOrder (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) :=
  linearOrderOfSTO WellOrderingRel

theorem hodgeBasis_h1_eigen (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hh : H.holomorphic = A.h1Holomorphic) (ha : H.antiholomorphic = A.h1Antiholomorphic)
    (i : HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) (z : ℂˣ) :
    HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A 1 z (A.h1ScalarExtension (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H i)) =
      (if HodgeBasis.Constructions.ExteriorCohomology.hodgeBasisSign H i then (z : ℂ) else star (z : ℂ)) •
        A.h1ScalarExtension (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H i) := by
  have hm := HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis_mem_signSubspace H i
  cases he : HodgeBasis.Constructions.ExteriorCohomology.hodgeBasisSign H i with
  | false =>
    have hm' : A.h1ScalarExtension (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H i) ∈ A.variety.pureBettiSubspace 0 1 := by
      change HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H i ∈ A.h1Antiholomorphic
      rw [← ha]
      simpa only [ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.signSubspace, he, Bool.false_eq_true, ite_false] using hm
    have ht := (HodgeCharacters.Constructions.ExteriorCohomology.pureBetti_iff_scalarAction A 0 1 _).mp hm' z
    simpa only [he, Bool.false_eq_true, ite_false, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul] using! ht
  | true =>
    have hm' : A.h1ScalarExtension (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H i) ∈ A.variety.pureBettiSubspace 1 0 := by
      change HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H i ∈ A.h1Holomorphic
      rw [← hh]
      simpa only [ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure.signSubspace, he, ite_true] using hm
    have ht := (HodgeCharacters.Constructions.ExteriorCohomology.pureBetti_iff_scalarAction A 1 0 _).mp hm' z
    simpa only [he, ite_true, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, mul_one] using! ht

theorem signProduct_character {n : ℕ} (ε : Fin n → Bool) (z : ℂˣ) :
    (∏ i, if ε i then (z : ℂ) else star (z : ℂ)) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (Fintype.card {i // ε i = true})
        (Fintype.card {i // ε i = false}) z := by
  classical
  simp only [Finset.prod_ite, Finset.prod_const, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Fintype.card_subtype,
    Bool.not_eq_true]

theorem hodgeExteriorBasis_cup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)) (n : ℕ)
    (t : Set.powersetCard (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) n) :
    ExteriorCohomologyComplexCup.Constructions.complexExteriorCupEquiv A n (HodgeBasis.Constructions.ExteriorCohomology.hodgeExteriorBasis H n t) =
      ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A n
        (fun i => A.h1ScalarExtension (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H (Set.powersetCard.ofFinEmbEquiv.symm t i))) := by
  change ExteriorCohomologyComplexCup.Constructions.complexH1ExteriorCupEquiv A n ((HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H).exteriorPower n t) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  exact ExteriorCohomologyComplexCup.Constructions.complexH1ExteriorCup_wedge A n _

end

end OAI.AlgebraicGeometry.AbelianVariety.PureMonomials.Constructions.ExteriorCohomology
