import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankPullbackComposition
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionScheme

/-! # Lie Rank Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction

noncomputable section

/-! The literal integral Lie-rank condition is invariant under actual
action-intertwining group isomorphisms and the canonical restriction
comparison. This includes every positive-characteristic geometric test. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R)

omit [NumberField E] [NumberField.IsCMField E] in
theorem integralLieRanks_iff_of_iso (T : Over (Spec (.of R)))
    {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) T.left}
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (h : ∀ a, ρ.map a ≫ e.hom = e.hom ≫ σ.map a) :
    PEL.Has.HasIntegralLieRanks P R iotaO T A ρ ↔ PEL.Has.HasIntegralLieRanks P R iotaO T B σ := by
  have hf (k : Type) [Field k] (p : Spec (.of k) ⟶ T.left)
      (τ : NumberField.RingOfIntegers E →+* k) (r : ℕ) :
      AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback p) (ρ.pullback p) τ r ↔
        AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (B.pullback p) (σ.pullback p) τ r := by
    let : GrpObj ((Over.pullback p).obj A.scheme) := Functor.grpObjObj
    let : GrpObj ((Over.pullback p).obj B.scheme) := Functor.grpObjObj
    have : IsMonHom ((Over.pullback p).mapIso e).hom :=
      inferInstanceAs (IsMonHom ((Over.pullback p).map e.hom))
    apply LieRankPullbackComposition.hasLieRank_iff_of_iso (ρ.pullback p) (σ.pullback p) τ ((Over.pullback p).mapIso e)
    intro a
    change (Over.pullback p).map (ρ.map a) ≫ (Over.pullback p).map e.hom =
      (Over.pullback p).map e.hom ≫ (Over.pullback p).map (σ.map a)
    rw [← (Over.pullback p).map_comp, ← (Over.pullback p).map_comp, h a]
  constructor
  · intro hρ k hk ha j p hp τ
    exact (hf k p _ _).mp (hρ k j p hp τ)
  · intro hσ k hk ha j p hp τ
    exact (hf k p _ _).mpr (hσ k j p hp τ)

omit [NumberField E] [NumberField.IsCMField E] in
theorem integralLieRanks_restrict_iff (M : Over (Spec (.of R)))
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) M.left) {T U : Over M.left}
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback U.hom)) (f : T ⟶ U) :
    PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) (A.pullback T.hom)
      (ActionScheme.restrictIntegralAction A ρ f) ↔
    PEL.Has.HasIntegralLieRanks P R iotaO ((Over.map M.hom).obj T) ((A.pullback U.hom).pullback f.left)
      (ρ.pullback f.left) := by
  apply (integralLieRanks_iff_of_iso P iotaO ((Over.map M.hom).obj T)
    (ρ.pullback f.left) (ActionScheme.restrictIntegralAction A ρ f) (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f) ?_).symm
  intro a
  change (Over.pullback f.left).map (ρ.map a) ≫ (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).hom =
    (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).hom ≫
      ((EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).inv ≫
        (Over.pullback f.left).map (ρ.map a) ≫ (EndomorphismFamiliesId.EndomorphismFamilies.restrictionIso A f).hom)
  rw [Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction
