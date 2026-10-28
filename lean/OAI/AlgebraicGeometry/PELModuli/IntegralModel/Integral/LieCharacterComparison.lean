import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieCharacters
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLiePredicate
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankPullbackComposition

/-! # Lie Character Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieCharacterComparison

noncomputable section

/-! The simultaneous character condition equals IntegralModel's literal
HasIntegralLieRanks on the actual pulled-back family over every test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem characterLieRank_arithmetic_iff
    {R B k : Type} [CommRing R] [CommRing B] [Field k] {g : ℕ}
    (M : Over (Spec (.of R))) (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g M.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction B A) (c : B →+* R) (r : ℕ)
    (p : Spec (.of k) ⟶ M.left) (j : R →+* k)
    (hp : p ≫ M.hom = Spec.map (CommRingCat.ofHom j)) :
    LieRankCharacter.CharacterLieRank A ρ (LieCharacters.arithmeticSectionCharacter M c) r p ↔
      AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback p) (ρ.pullback p) (j.comp c) r := by
  unfold LieRankCharacter.CharacterLieRank
  rw [LieCharacters.arithmeticSectionCharacter_value M c p j hp]

theorem integralLieRanks_iff_character_conditions
    {E R : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [CommRing R] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* R) {M T : Over (Spec (.of R))}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) M.left)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (x : T ⟶ M) :
    PEL.Has.HasIntegralLieRanks P R iotaO T (A.pullback x.left) (ρ.pullback x.left) ↔
      ∀ τ : E ≃ₐ[ℚ] E,
        SchemeCharacterLiePredicate.HasCharacterLieRankOnSchemeMap A ρ (LieCharacters.integralLieCharacter M iotaO τ) (P.lieRank τ) x.left := by
  have hcomp (k : Type) [Field k] (p : Spec (.of k) ⟶ T.left) (j : R →+* k)
      (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom j)) :
      (p ≫ x.left) ≫ M.hom = Spec.map (CommRingCat.ofHom j) :=
    (Category.assoc _ _ _).trans ((congrArg (p ≫ ·) x.w).trans hp)
  constructor
  · intro h τ k hk ha p
    let j := (Spec.preimage (p ≫ T.hom)).hom
    have hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom j) := (Spec.map_preimage _).symm
    apply (characterLieRank_arithmetic_iff M A ρ
      (iotaO.comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom)) (P.lieRank τ)
      (p ≫ x.left) j (hcomp k p j hp)).mpr
    exact (LieRankPullbackComposition.hasLieRank_pullbackComp_iff A ρ x.left p _ _).mpr (h k j p hp τ)
  · intro h k hk ha j p hp τ
    apply (LieRankPullbackComposition.hasLieRank_pullbackComp_iff A ρ x.left p _ _).mp
    exact (characterLieRank_arithmetic_iff M A ρ
      (iotaO.comp (NumberField.RingOfIntegers.mapRingHom τ.toRingHom)) (P.lieRank τ)
      (p ≫ x.left) j (hcomp k p j hp)).mp (h τ k p)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.LieCharacterComparison
