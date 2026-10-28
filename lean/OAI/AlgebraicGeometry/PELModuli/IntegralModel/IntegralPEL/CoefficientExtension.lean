import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Coefficient Extension -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Changing the coefficient ring of an actual PEL object preserves
the same geometric Lie-rank condition, through the composed ring map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E R R' : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [CommRing R'] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
    {iotaO : NumberField.RingOfIntegers E →+* R}

omit [NumberField E] [NumberField.IsCMField E] in
theorem IntegralPEL.CoefficientExtension.integralLieRanks_changeCoefficients (φ : R →+* R') (X : Over (Spec (.of R')))
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) X.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (h : PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map (Spec.map (CommRingCat.ofHom φ))).obj X) A ρ) :
    PEL.Has.HasIntegralLieRanks P R' (φ.comp iotaO) X A ρ := by
  intro k hk hclosed j p hp τ
  apply h k (j.comp φ) p
  change p ≫ (X.hom ≫ Spec.map (CommRingCat.ofHom φ)) = Spec.map (CommRingCat.ofHom (j.comp φ))
  rw [← Category.assoc, hp, ← Spec.map_comp]
  rfl

def PEL.Has.IntegralPELObject.changeCoefficients (φ : R →+* R') {X : Over (Spec (.of R'))}
    (A : PEL.Has.IntegralPELObject P R iotaO N ((Over.map (Spec.map (CommRingCat.ofHom φ))).obj X)) :
    PEL.Has.IntegralPELObject P R' (φ.comp iotaO) N X where
  data := A.data
  rosati := A.rosati
  lieRanks := IntegralPEL.CoefficientExtension.integralLieRanks_changeCoefficients φ X A.data.polarized.abelian A.data.action A.lieRanks

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
