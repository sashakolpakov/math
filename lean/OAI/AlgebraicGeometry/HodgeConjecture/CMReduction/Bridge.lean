import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Endpoints
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedRegroup
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed

/-! # Bridge -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Bridge.CM.Construction

noncomputable section

/-! The actual product and class expressions used by a local CMReduction switch. -/

open _root_.CategoryTheory CartesianMonoidalCategory

abbrev bridgeProduct (B₁ B₂ X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety :=
  Albanese.Construction.SegreClosed.abelianProduct (Albanese.Construction.SegreClosed.abelianProduct B₁ B₂) X

def bridgeBase (B₁ B₂ X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : (bridgeProduct B₁ B₂ X).variety.toOver ⟶ X.variety.toOver :=
  snd (Albanese.Construction.SegreClosed.abelianProduct B₁ B₂).variety.toOver X.variety.toOver

def bridgeMiddle (B₁ B₂ X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    (bridgeProduct B₁ B₂ X).variety.toOver ⟶ (Albanese.Construction.SegreClosed.abelianProduct B₁ B₂).variety.toOver :=
  fst (Albanese.Construction.SegreClosed.abelianProduct B₁ B₂).variety.toOver X.variety.toOver

def bridgeFirst (B₁ B₂ X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : (bridgeProduct B₁ B₂ X).variety.toOver ⟶ B₁.variety.toOver :=
  bridgeMiddle B₁ B₂ X ≫ fst B₁.variety.toOver B₂.variety.toOver

def bridgeSecond (B₁ B₂ X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : (bridgeProduct B₁ B₂ X).variety.toOver ⟶ B₂.variety.toOver :=
  bridgeMiddle B₁ B₂ X ≫ snd B₁.variety.toOver B₂.variety.toOver

def bridgeVectorFirst (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    {H₁ H₂ : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₁) (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₂)
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (τ : Gal(E/ℚ)) :
    (bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.complexCohomology 1 :=
  Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (bridgeFirst R₁.abelianVariety R₂.abelianVariety X)
    (Endpoints.CM.Construction.realizedVector E R₁ τ)

def bridgeVectorSecond (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    {H₁ H₂ : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₁) (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₂)
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (τ : Gal(E/ℚ)) :
    (bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.complexCohomology 1 :=
  Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (bridgeSecond R₁.abelianVariety R₂.abelianVariety X)
    (Endpoints.CM.Construction.realizedVector E R₂ τ)

abbrev previousPacked (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    {H₁ H₂ : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₁) (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₂)
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace X.variety.toOver)) :
    EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace (bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver) :=
  PackedRegroup.CM.Construction.evenPullback (bridgeBase R₁.abelianVariety R₂.abelianVariety X) U *
    PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace (bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver)
      (bridgeVectorFirst E R₁ R₂ X (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
      (bridgeVectorSecond E R₁ R₂ X (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))

abbrev switchPacked (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    {H₁ H₂ : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₁) (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H₂)
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (z₁ z₂ : X.variety.complexCohomology 1) :
    EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace (bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver) :=
  PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace (bridgeProduct R₁.abelianVariety R₂.abelianVariety X).variety.toOver)
    (bridgeVectorFirst E R₁ R₂ X 1)
    (bridgeVectorSecond E R₁ R₂ X 1) *
    PackedRegroup.CM.Construction.evenPullback (bridgeBase R₁.abelianVariety R₂.abelianVariety X)
      (PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace X.variety.toOver) z₁ z₂)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Bridge.CM.Construction
