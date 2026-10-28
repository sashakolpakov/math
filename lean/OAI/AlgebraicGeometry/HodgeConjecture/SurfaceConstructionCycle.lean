import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionNe
import OAI.AlgebraicGeometry.HodgeConjecture.Established
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AbelianMapsProduct

/-! # Surface Construction Cycle -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionCycle

noncomputable section

/-! Original SurfaceConstruction with all named theorem inputs supplied by proofs.
ProjectionFormula is used only through its proved full Chow clause and the native
Poincare construction/projection identity in SurfaceConstruction's specific degrees. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionNe.CM
theorem algebraic_cycle_realizing_switch
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Fin 4 →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hswitch : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (R : ∀ i : Fin 4,
      ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i : Fin 4, X.toOver ⟶ (R i).abelianVariety.toOver)
    (hproduct : IsLimit (Fan.mk X.toOver π)) :
    let u : Fin 4 → Gal(E/ℚ) → X.complexCohomology 1 :=
      fun i τ =>
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
          ((R i).complexComparison
            (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
              (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)))
    let c := ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
    let t : X.complexCohomology 4 :=
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
        (Betti.Scheme.schemePointSpace X.toOver) 2 2
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
          (Betti.Scheme.schemePointSpace X.toOver) 1 1 (u 0 1) (u 1 1))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
          (Betti.Scheme.schemePointSpace X.toOver) 1 1 (u 2 c) (u 3 c))
    t ≠ 0 ∧
      ∃ (n : ℕ) (a : Fin n → E)
        (Z : Fin n → CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X 2),
        (∑ j : Fin n,
          (a j : ℂ) •
            X.rationalCohomologyInclusion 4
              (X.geometricCycleClassMap 2 (Z j))) = t := by
  have h53 : Surface.CM.Construction.BallSurfaceSwitchInput E :=
    ThetaCycle.AbelianMapsProduct.four_abelian_maps_nonzero_product E
  exact SurfaceConstructionNe.CM.algebraic_cycle_realizing_switch E
    (Established.CM.SurfaceConstruction.Intrinsic.scalarTraceDescent E) Established.CM.SurfaceConstruction.Intrinsic.degreeTwoAlgebraicityInput
    Established.CM.SurfaceConstruction.Intrinsic.lefschetzOneOneInput h53 Established.CM.SurfaceConstruction.Intrinsic.properCycleClassCompatibility
    Established.CM.SurfaceConstruction.Intrinsic.intersectionCycleClassCompatibility Established.CM.SurfaceConstruction.Intrinsic.chowProjectionFormula
    v hswitch R X π hproduct

end

end OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionCycle
