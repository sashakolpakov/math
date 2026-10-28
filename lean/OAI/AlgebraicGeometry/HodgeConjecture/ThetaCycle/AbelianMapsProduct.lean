import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Constructions
import OAI.RepresentationTheory.Theta.Adelic.UnitaryThetaCongruence
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Structure
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph
import OAI.AlgebraicGeometry.Albanese.Construction.Mon

/-! # Abelian Maps Product -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AbelianMapsProduct

noncomputable section

/-! The original ThetaCycle statement, with all named theorem inputs supplied by
proofs. The actual ball surface, algebraic maps, nonzero integral and
arbitrarily deep principal refinements are constructed conclusions. -/
open _root_.CategoryTheory
open OAI.AlgebraicGeometry.Albanese.Construction.Mon OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight.Constructions
theorem four_abelian_maps_nonzero_product
    (K : IntermediateField ℚ ℂ)
    [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (hbalance : ∀ τ : Gal(K/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
      ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (hid : ∀ i, (v i).val 1 = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))
    (Nbase : ℕ) (hNbase : 0 < Nbase) :
    ∃ (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ)
      (S : Cm.PrincipalBallSurface K B N)
      (f : (i : Fin 4) →
        S.surface.variety.toOver ⟶ (R i).abelianVariety.toOver),
      0 < N ∧ Nbase ∣ N ∧
      S.surface.evaluate (Cm.fourClass K v R S.surface.variety f) ≠ 0 ∧
      ∀ L : ℕ, 0 < L →
        ∃ (M : ℕ) (T : Cm.PrincipalBallSurface K B M)
          (p : Cm.PrincipalRefinement K S T),
          0 < M ∧ L ∣ M ∧
          T.surface.evaluate
              (Cm.fourClass K v R T.surface.variety (fun i => p.map ≫ f i)) =
            (p.degree : ℂ) *
              S.surface.evaluate (Cm.fourClass K v R S.surface.variety f) ∧
          T.surface.evaluate
            (Cm.fourClass K v R T.surface.variety (fun i => p.map ≫ f i)) ≠ 0 := by
  have h43 : Moduli.CM.ReferenceFamilyInput := PELModuli.IntegralModel.ReferenceFamilyConstructed.provedReferenceFamilyModuliInput
  have h41 : HeckeCycles.CM.HeckeCyclesInput := by
    intro E instNumberField instGalois instCM w hw d hd Nbase hNbase X H hH Θ hsource
    exact HeckeCycles.Structure.extraction_of_prescribed_cm_hodge_structure
      E w hw d hd Nbase hNbase X H hH Θ hsource
  have h06 : DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput := ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic
  have h07 : DegreeTwo.Transport.Constructions.ConstructionInput := Albanese.Construction.Mon.exists_albanese
  exact Constructions.four_abelian_maps_nonzero_product
    h43 RepresentationTheory.Theta.Adelic.UnitaryThetaCongruence.complete_unitary_splitting_geometric_theta_and_congruence
    h41 Persistence.CM.nativePairingContinuityInput DegreeTwo.IntrinsicWeight.Constructions.weight_one_algebraicity h06 h07
    K v hbalance hid hother R Nbase hNbase

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AbelianMapsProduct
