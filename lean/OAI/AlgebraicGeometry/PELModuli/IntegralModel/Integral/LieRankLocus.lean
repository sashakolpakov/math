import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SimultaneousCharacterLieLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieCharacterComparison

/-! # Lie Rank Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankLocus

noncomputable section

/-! The exact integral PEL Lie-rank condition has an actual bounded
locally closed representing locus on every reduced test scheme.
No Lie-locus existence, local freeness, or chart data are assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_reduced_integral_lie_rank_locus
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    [IsNoetherian M.left] (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) M.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) :
    ∃ (L : Over (Spec (.of R))) (j : L ⟶ M),
      IsReduced L.left ∧ IsImmersion j.left ∧ QuasiCompact j.left ∧
      ∀ (T : Over (Spec (.of R))) [IsReduced T.left] (x : T ⟶ M),
        PEL.Has.HasIntegralLieRanks P R iotaO T (A.pullback x.left) (ρ.pullback x.left) ↔
          ∃! f : T ⟶ L, f ≫ j = x := by
  obtain ⟨L, a, hL, ha, hqc, hc⟩ := SimultaneousCharacterLieLocus.exists_simultaneous_character_lie_locus A ρ
    (LieCharacters.integralLieCharacter M iotaO) P.lieRank
  let L' : Over (Spec (.of R)) := Over.mk (a ≫ M.hom)
  let j : L' ⟶ M := Over.homMk a rfl
  refine ⟨L', j, hL, ha, hqc, ?_⟩
  intro T hT x
  exact (LieCharacterComparison.integralLieRanks_iff_character_conditions P iotaO A ρ x).trans
    ((hc T.left x.left).trans (OverLocusClassification.over_existsUnique_lift_iff j x).symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieRankLocus
