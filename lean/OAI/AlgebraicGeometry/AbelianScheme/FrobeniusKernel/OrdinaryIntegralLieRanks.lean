import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryGeometricLieRanks
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has

/-! # Ordinary Integral Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIntegralLieRanks.Construction

noncomputable section

/-! Preservation of the full integral PEL Lie predicate, including every
geometric field and the actual arithmetic residue map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k E K R : Type} [Field k] [IsAlgClosed k] [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]
  [Field K] [NumberField K] [CommRing R] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {s N M : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (iotaO : NumberField.RingOfIntegers E →+* R) (t : Spec (.of k) ⟶ Spec (.of R))
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N (Spec (.of k)))
  (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType M (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.abelian B.abelian)
  (hσ : ∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)
  (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ (3 * s))
  (n : ℕ)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.abelian.scheme), x ≫ f.hom = 1 → x ^ (q ^ n) = 1)

include hsplit hσ hordinary hf in
omit [NumberField.IsCMField E] in
theorem ordinaryIsogeny_preserves_integralLieRanks
    (hr : PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO (Over.mk t) A.abelian ρ) :
    PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO (Over.mk t) B.abelian σ := by
  intro F _ _ c p hp τ
  exact OrdinaryGeometricLieRanks.Construction.ordinaryIsogeny_preserves_geometricLieRank j iota hsplit A B ρ σ f hσ hordinary n hf
    p (c.comp (iotaO.comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom)))
    (P.lieRank τ) (hr F c p hp τ)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIntegralLieRanks.Construction
