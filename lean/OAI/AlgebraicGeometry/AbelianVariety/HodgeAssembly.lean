import OAI.AlgebraicGeometry.AbelianVariety.PureMonomials
import OAI.AlgebraicGeometry.AbelianVariety.GeometricProduct

/-! # Hodge Assembly -/

namespace OAI.AlgebraicGeometry.AbelianVariety.HodgeAssembly.Constructions.ExteriorCohomology

noncomputable section

open scoped TensorProduct Classical

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

/-- Multiplicativity of the actual Hodge action propagates to all iterated cup products. -/
theorem complexH1Cup_scalarAction
    (hmul : ∀ (p q : ℕ) (z : ℂˣ)
      (a : A.variety.complexCohomology p) (b : A.variety.complexCohomology q),
      HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A (p + q) z (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a b) =
        AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q
          (HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A p z a) (HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A q z b))
    (n : ℕ) (v : Fin n → A.variety.complexCohomology 1) (z : ℂˣ) :
    HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A n z (ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A n v) =
      ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A n (fun i => HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A 1 z (v i)) := by
  induction n with
  | zero => exact GeometricProduct.Constructions.ExteriorCohomology.bettiScalarAction_zero A z _
  | succ n ih =>
    change HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A (n + 1) z
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) n 1
        (ExteriorCohomologyComplexCup.Constructions.complexH1CupMultilinear A n (Fin.init v)) (v (Fin.last n))) = _
    rw [hmul, ih]
    rfl

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
local instance (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) : LinearOrder (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) :=
  linearOrderOfSTO WellOrderingRel

/-- Algebraic assembly: the genuine product comparison supplies exactly the remaining Hodge data. -/
theorem comparison_of_geometric_cup
    (hcup : ∀ (p q : ℕ) (a : A.variety.complexCohomology p) (b : A.variety.complexCohomology q),
      GeometricProduct.Constructions.ExteriorCohomology.geometricBettiWedge A p q a b = AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a b)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (hh : H.holomorphic = A.h1Holomorphic) (ha : H.antiholomorphic = A.h1Antiholomorphic) :
    Nonempty (ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H) := by
  have hmul (p q : ℕ) (z : ℂˣ) (a : A.variety.complexCohomology p)
      (b : A.variety.complexCohomology q) :
      HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A (p + q) z (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a b) =
        AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q
          (HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A p z a) (HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A q z b) := by
    rw [← hcup, ← hcup]
    exact GeometricProduct.Constructions.ExteriorCohomology.bettiScalarAction_geometricWedge A p q z a b
  have hchar (n : ℕ) (t : Set.powersetCard (HodgeBasis.Constructions.ExteriorCohomology.HodgeBasisIndex H) n) (z : ℂˣ) :
      HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A n z (ExteriorCohomologyComplexCup.Constructions.complexExteriorCupEquiv A n (HodgeBasis.Constructions.ExteriorCohomology.hodgeExteriorBasis H n t)) =
        HodgeCharacters.Constructions.ExteriorCohomology.hodgeExteriorCharacter H n t z • ExteriorCohomologyComplexCup.Constructions.complexExteriorCupEquiv A n (HodgeBasis.Constructions.ExteriorCohomology.hodgeExteriorBasis H n t) := by
    rw [PureMonomials.Constructions.ExteriorCohomology.hodgeExteriorBasis_cup, complexH1Cup_scalarAction A hmul]
    have hv :
        (fun i : Fin n => HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A 1 z
          (A.h1ScalarExtension (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H (Set.powersetCard.ofFinEmbEquiv.symm t i)))) =
        (fun i : Fin n =>
          (if HodgeCharacters.Constructions.ExteriorCohomology.hodgeExteriorSigns H n t i then (z : ℂ) else star (z : ℂ)) •
            A.h1ScalarExtension (HodgeBasis.Constructions.ExteriorCohomology.hodgeBasis H (Set.powersetCard.ofFinEmbEquiv.symm t i))) := by
      funext i
      exact PureMonomials.Constructions.ExteriorCohomology.hodgeBasis_h1_eigen A H hh ha _ z
    rw [hv, MultilinearMap.map_smul_univ, PureMonomials.Constructions.ExteriorCohomology.signProduct_character]
    rfl
  refine ⟨{
    rational := CupGeneration.Constructions.ExteriorCohomology.rationalExteriorCupEquiv A
    wedge := fun n v => CupMap.Constructions.ExteriorCohomology.exteriorCup_wedge A n v
    pure := ?_ }⟩
  intro p q x
  change ExteriorCohomologyComplexCup.Constructions.complexExteriorCupEquiv A (p + q) x ∈ A.variety.pureBettiSubspace p q ↔
    x ∈ H.exteriorPureSubspace p q
  exact HodgeCharacters.Constructions.ExteriorCohomology.exteriorCup_pure_of_basis_character A H p q (hchar (p + q)) x

end

end OAI.AlgebraicGeometry.AbelianVariety.HodgeAssembly.Constructions.ExteriorCohomology
