import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LieRank
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Integral Lie Ranks Quotient -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralLieRanksQuotient

noncomputable section

/-! The actual integral Lie-signature predicate is preserved by a finite
etale equivariant isogeny, at every geometric field and embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (R : Type) [CommRing R] (iotaO : NumberField.RingOfIntegers E →+* R)
  (T : Over (Spec (.of R))) (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) [Etale f.hom.left]
  (hcomm : ∀ c, f.hom ≫ σ.map c = ρ.map c ≫ f.hom)

omit [NumberField E] [NumberField.IsCMField E] in
include f hcomm in
theorem integralLieRanks_after_quotient
    (hrank : PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO T A ρ) :
    PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO T B σ := by
  intro F _ _ j p hp τ
  exact AbelianScheme.IsogenyQuotient.LieRank.Construction.hasLieRank_after_baseChange A B f.hom ρ σ hcomm p
    (j.comp (iotaO.comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom)))
    (P.lieRank τ) (hrank F j p hp τ)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralLieRanksQuotient
