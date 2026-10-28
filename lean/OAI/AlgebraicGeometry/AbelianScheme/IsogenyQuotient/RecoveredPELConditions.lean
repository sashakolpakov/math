import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlgebraicallyClosedRosatiDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LieRankSurjectiveDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiIsoTransport

/-! # Recovered PEL Conditions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredPELConditions.Construction

noncomputable section

/-! Full Rosati and Lie-rank conditions descend through the specified
polarized and action comparisons of a recovered PEL family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiIsoTransport

set_option backward.isDefEq.respectTransparency false in
theorem rosati_of_recovered_field_action
    (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of L)))
    (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A (B.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (h : ∀ a, ρ.map a ≫ e.abelian.hom = e.abelian.hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map (σ.map a))
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ) : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation B σ :=
  AlgebraicallyClosedRosatiDescent.Construction.rosati_of_algebraicallyClosed_field_pullback k L B σ
    (PELModuli.IntegralModel.RosatiIsoTransport.rosati_of_polarized_iso e ρ (σ.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))))
      (fun a => (h a).symm) hρ)

set_option backward.isDefEq.respectTransparency false in
theorem integralLieRanks_of_recovered_surjective_action
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R)
    {M T : Over (Spec (.of R))} [IsLocallyNoetherian M.left]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) M.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (q : T ⟶ M) [Surjective q.left]
    (e : A.scheme ≅ (B.pullback q.left).scheme) [IsMonHom e.hom]
    (h : ∀ a, ρ.map a ≫ e.hom = e.hom ≫ (Over.pullback q.left).map (σ.map a))
    (hρ : PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO T A ρ) : PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO M B σ :=
  LieRankSurjectiveDescent.Construction.integralLieRanks_of_surjective_pullback P iotaO B σ q
    ((PELModuli.IntegralModel.Integral.LieRankRestriction.integralLieRanks_iff_of_iso P iotaO T ρ (σ.pullback q.left) e h).mp hρ)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RecoveredPELConditions.Construction
