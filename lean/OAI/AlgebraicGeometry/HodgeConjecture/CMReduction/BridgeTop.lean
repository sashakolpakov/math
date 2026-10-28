import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Bridge
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PackedMiddleTop
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ProductTop

/-! # Bridge Top -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTop.CM.Construction

noncomputable section

/-! The nonzero top class on the two factors of a local switch. -/

open _root_.CategoryTheory CartesianMonoidalCategory
open scoped MonoidalCategory

theorem pullback_productTopClass
    (B₁ B₂ : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {W : Over Foundations.Scheme.ProjectiveSpace.complexBase}
    (g : W ⟶ B₁.toOver ⊗ B₂.toOver)
    (b₁ : B₁.complexCohomology (B₁.complexDimension + B₁.complexDimension))
    (b₂ : B₂.complexCohomology (B₂.complexDimension + B₂.complexDimension)) :
    PackedRegroup.CM.Construction.evenPullback g
      (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety B₁ B₂).toOver)
        (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety B₁ B₂).complexDimension
        (ProductTop.CM.Construction.productTopClass B₁ B₂ b₁ b₂)) =
    PackedRegroup.CM.Construction.evenPullback (g ≫ fst B₁.toOver B₂.toOver)
      (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace B₁.toOver) B₁.complexDimension b₁) *
    PackedRegroup.CM.Construction.evenPullback (g ≫ snd B₁.toOver B₂.toOver)
      (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace B₂.toOver) B₂.complexDimension b₂) := by
  let a₁ := PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace B₁.toOver) B₁.complexDimension b₁
  let a₂ := PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace B₂.toOver) B₂.complexDimension b₂
  let f₁ := fst B₁.toOver B₂.toOver
  let f₂ := snd B₁.toOver B₂.toOver
  have hp := congrArg (fun a : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace (B₁.toOver ⊗ B₂.toOver)) =>
    PackedRegroup.CM.Construction.evenPullback g a) (ProductTop.CM.Construction.pack_productTopClass B₁ B₂ b₁ b₂)
  calc
    _ = PackedRegroup.CM.Construction.evenPullback g (PackedRegroup.CM.Construction.evenPullback f₁ a₁ * PackedRegroup.CM.Construction.evenPullback f₂ a₂) := hp
    _ = PackedRegroup.CM.Construction.evenPullback g (PackedRegroup.CM.Construction.evenPullback f₁ a₁) * PackedRegroup.CM.Construction.evenPullback g (PackedRegroup.CM.Construction.evenPullback f₂ a₂) :=
      map_mul (PackedRegroup.CM.Construction.evenPullback g) (PackedRegroup.CM.Construction.evenPullback f₁ a₁) (PackedRegroup.CM.Construction.evenPullback f₂ a₂)
    _ = _ := congrArg₂ (fun a b : EvenAlgebra.CM.Construction.EvenClass (R := ℂ) (Betti.Scheme.schemePointSpace W) => a * b)
      (PackedRegroup.CM.Construction.evenPullback_comp g f₁ a₁) (PackedRegroup.CM.Construction.evenPullback_comp g f₂ a₂)

theorem pullback_middleTopClass
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Pairing.CM.Construction.SignType E) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    {W : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : W ⟶ R.abelianVariety.toOver) :
    PackedRegroup.CM.Construction.evenPullback f (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace R.abelianVariety.toOver)
      R.abelianVariety.variety.complexDimension (MiddleTop.CM.Construction.middleTopClass E v R)) =
    PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace W)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (Endpoints.CM.Construction.realizedVector E R (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (Endpoints.CM.Construction.realizedVector E R 1)) *
    PackedRegroup.CM.Construction.evenPullback f (PackedMiddleTop.CM.Construction.packAmple R.abelianVariety.variety (R.abelianVariety.variety.complexDimension - 1)) := by
  rw [PackedMiddleTop.CM.Construction.pack_middleTopClass, map_mul, PackedRegroup.CM.Construction.evenPullback_pair]

theorem pullback_reverseMiddleTopClass
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : Pairing.CM.Construction.SignType E) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v))
    {W : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : W ⟶ R.abelianVariety.toOver) :
    PackedRegroup.CM.Construction.evenPullback f (PackedRegroup.CM.Construction.packEven (Betti.Scheme.schemePointSpace R.abelianVariety.toOver)
      R.abelianVariety.variety.complexDimension (PackedMiddleTop.CM.Construction.reverseMiddleTopClass E v R)) =
    PackedRegroup.CM.Construction.packPair (Betti.Scheme.schemePointSpace W)
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (Endpoints.CM.Construction.realizedVector E R 1))
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (Endpoints.CM.Construction.realizedVector E R (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))) *
    PackedRegroup.CM.Construction.evenPullback f (PackedMiddleTop.CM.Construction.packAmple R.abelianVariety.variety (R.abelianVariety.variety.complexDimension - 1)) := by
  rw [PackedMiddleTop.CM.Construction.pack_reverseMiddleTopClass, map_mul, PackedRegroup.CM.Construction.evenPullback_pair]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.BridgeTop.CM.Construction
