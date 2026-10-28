import OAI.AlgebraicGeometry.HodgeConjecture.CycleCoefficientsCM
import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionCycle

/-! # Cycle Coefficients P -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CycleCoefficientsP

noncomputable section

/-! Full original CycleCoefficients with its sole theorem input supplied by proved SurfaceConstruction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem p54_input : CycleCoefficientsCM.CM.Construction.SurfaceConstructionInput :=
  SurfaceConstructionCycle.algebraic_cycle_realizing_switch

theorem four_factor_switch_algebraic
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Fin 4 →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    -- Chosen abelian-variety realizations of the four U(vᵢ).
    (A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : ∀ i, E ≃ₗ[ℚ] (A i).variety.rationalCohomology 1)
    (hhol : ∀ i,
      ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)).holomorphic).map
          ((e i).toLinearMap.baseChange ℂ) =
        (A i).h1Holomorphic)
    (hanti : ∀ i,
      ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)).antiholomorphic).map
          ((e i).toLinearMap.baseChange ℂ) =
        (A i).h1Antiholomorphic)
    -- The actual product, specified by its universal property.
    (P : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (π : ∀ i, P.toOver ⟶ (A i).toOver)
    (hproduct : IsLimit (Fan.mk P.toOver π)) :
    let labels : Fin 4 → Gal(E/ℚ) :=
      fun i => if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
    let x : Fin 4 → P.variety.complexCohomology 1 :=
      fun i =>
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i))
          ((A i).h1ScalarExtension
            ((e i).toLinearMap.baseChange ℂ
              (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
                (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (labels i)))))
    let ξ : P.variety.complexCohomology 4 :=
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
        (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 2 2
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
          (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1 (x 0) (x 1))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
          (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1 (x 2) (x 3))
    ξ ≠ 0 ∧
      Submodule.span ℂ ({ξ} : Set (P.variety.complexCohomology 4)) ≤
        P.variety.complexGeometricAlgebraicClasses 2 := by
  exact CycleCoefficientsCM.CM.Construction.four_factor_switch_algebraic p54_input
    E v hbalance A e hhol hanti P π hproduct

end

end OAI.AlgebraicGeometry.HodgeConjecture.CycleCoefficientsP
