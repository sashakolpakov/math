import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.LieRankLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction

/-! # Lie Rank Surjective Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LieRankSurjectiveDescent.Construction

noncomputable section

/-! Prescribed Lie ranks on a Noetherian characteristic-zero base
descend through any surjective base change. The actual clopen Lie-rank
locus must be the whole base once the covering map factors through it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.LieRankLocus OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankRestriction

set_option backward.isDefEq.respectTransparency false in
theorem integralLieRanks_of_surjective_pullback
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R)
    {M T : Over (Spec (.of R))} [IsLocallyNoetherian M.left]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) M.left) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (x : T ⟶ M) [Surjective x.left]
    (hx : PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO T (A.pullback x.left) (ρ.pullback x.left)) :
    PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO M A ρ := by
  obtain ⟨L, j, hj, _, hc⟩ := AbelianModuli.ReferenceFamily.Integral.LieRankLocus.exists_integral_lie_rank_locus P iotaO M A ρ
  have : IsOpenImmersion j.left := hj
  obtain ⟨q, hq, _⟩ := (hc T x).mp hx
  have : Surjective j.left := ⟨fun m => by
    obtain ⟨t, ht⟩ := x.left.surjective m
    exact ⟨q.left t, (congrArg (fun f : T ⟶ M => f.left t) hq).trans ht⟩⟩
  have : IsIso j.left := (isIso_iff_isOpenImmersion_and_surjective j.left).mpr ⟨hj, inferInstance⟩
  have : IsIso ((Over.forget (Spec (.of R))).map j) := inferInstanceAs (IsIso j.left)
  have : IsIso j := isIso_of_reflects_iso j (Over.forget (Spec (.of R)))
  have hbase := (hc M (𝟙 M)).mpr
    (show ∃! f : M ⟶ L, f ≫ j = 𝟙 M from
      ⟨inv j, IsIso.inv_hom_id j, fun f hf => (cancel_mono j).mp (hf.trans (IsIso.inv_hom_id j).symm)⟩)
  apply (PELModuli.IntegralModel.Integral.LieRankRestriction.integralLieRanks_iff_of_iso P iotaO M (ρ.pullback (𝟙 M.left)) ρ A.pullbackIdIso ?_).mp hbase
  intro a
  change (Over.pullback (𝟙 M.left)).map (ρ.map a) ≫ A.pullbackIdIso.hom =
    A.pullbackIdIso.hom ≫ ρ.map a
  rw [A.pullbackIdIso_hom]
  exact Over.pullbackId.hom.naturality (ρ.map a)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LieRankSurjectiveDescent.Construction
