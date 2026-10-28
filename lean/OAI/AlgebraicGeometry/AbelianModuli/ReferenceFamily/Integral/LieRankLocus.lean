import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SimultaneousCharacterLieLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieCharacterComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverLocusClassification

/-! # Lie Rank Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.LieRankLocus

noncomputable section

/-! The original integral PEL Lie-rank condition is represented by a
constructed clopen subscheme in characteristic zero. Its classifier
ranges over every test scheme and the original pulled-back family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_integral_lie_rank_locus
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] [Algebra ℚ R] {s : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) (M : Over (Spec (.of R)))
    [IsLocallyNoetherian M.left] (A : HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) M.left)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A) :
    ∃ (L : Over (Spec (.of R))) (j : L ⟶ M),
      IsOpenImmersion j.left ∧ IsClosedImmersion j.left ∧
      ∀ (T : Over (Spec (.of R))) (x : T ⟶ M),
        PELModuli.IntegralModel.PEL.Has.HasIntegralLieRanks P R iotaO T (A.pullback x.left) (ρ.pullback x.left) ↔
          ∃! f : T ⟶ L, f ≫ j = x := by
  let : Algebra ℚ Γ(M.left, ⊤) :=
    ((M.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom).comp (algebraMap ℚ R)).toAlgebra
  obtain ⟨U, hU, hc⟩ := SimultaneousCharacterLieLocus.exists_simultaneous_character_lie_rank_open A ρ
    (PELModuli.IntegralModel.Integral.LieCharacters.integralLieCharacter M iotaO) P.lieRank
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by
    rw [Scheme.Opens.range_ι]
    exact hU)
  let L : Over (Spec (.of R)) := Over.mk (U.ι ≫ M.hom)
  let j : L ⟶ M := Over.homMk U.ι rfl
  refine ⟨L, j, inferInstanceAs (IsOpenImmersion U.ι), inferInstanceAs (IsClosedImmersion U.ι), ?_⟩
  intro T x
  exact (PELModuli.IntegralModel.Integral.LieCharacterComparison.integralLieRanks_iff_character_conditions P iotaO A ρ x).trans
    ((hc T.left x.left).trans (PELModuli.IntegralModel.OverLocusClassification.over_existsUnique_lift_iff j x).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.LieRankLocus
