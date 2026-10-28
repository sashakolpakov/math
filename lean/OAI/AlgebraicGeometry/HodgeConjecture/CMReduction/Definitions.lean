import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.ComplexMultiplication.KnownExteriorCohomology
import OAI.AlgebraicGeometry.ComplexMultiplication.KnownAlgebraicity
import OAI.AlgebraicGeometry.ComplexMultiplication.ClassDescent
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Definitions -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Definitions.CM

noncomputable section

/-! Definitions used in the CMReduction statement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The four-factor embedding tensor lies in the complex extension
of the rational cycle-class image on an actual fourfold product. -/
def FourFactorSwitchAlgebraicity
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] :
    Prop :=
  ∀ (v : Fin 4 →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)),
    (∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
      ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ)) →
    ∀ (R : ∀ i : Fin 4,
      ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i))),
    ∃ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (π : ∀ i : Fin 4, B.toOver ⟶ (R i).abelianVariety.toOver),
      Nonempty (IsLimit (Fan.mk B.toOver π)) ∧
      (let x : Fin 4 → B.variety.complexCohomology 1 :=
        fun i =>
          Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
            ((R i).abelianVariety.h1ScalarExtension
              (((R i).comparison.toLinearMap.baseChange ℂ)
                (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
                  (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
                    (if i.val < 2 then 1
                     else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))))
       AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
           (Betti.Scheme.schemePointSpace B.toOver) 2 2
           (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
             (Betti.Scheme.schemePointSpace B.toOver) 1 1 (x 0) (x 1))
           (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
             (Betti.Scheme.schemePointSpace B.toOver) 1 1 (x 2) (x 3))
         ∈ B.variety.complexGeometricAlgebraicClasses 2)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Definitions.CM
