import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalCharacterLieLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLiePredicate
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverLocusClassification

/-! # Scheme Character Lie Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLieLocus

noncomputable section

/-! The constructed chart Lie-rank locus gives the exact local range
criterion required for the proved global reduced-locus construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem exists_local_scheme_character_lie_locus
    {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} [IsLocallyNoetherian S]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (χ : NumberField.RingOfIntegers E →+* Γ(S, ⊤)) (r : ℕ)
    (C : Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left
      (fun i => (ρ.map (Finite.Actions.integralActionBasis E i)).left)) :
    ∃ (Z : Scheme.{0}) (j : Z ⟶ C.V.toScheme),
      IsReduced Z ∧ IsImmersion j ∧ QuasiCompact j ∧
      ∀ (T : Scheme.{0}) [IsReduced T] (x : T ⟶ C.V.toScheme),
        x ≫ C.V.ι ∈ (SchemeCharacterLiePredicate.schemeCharacterLieRankSubfunctor A ρ χ r).obj (.op T) ↔
          Set.range x ⊆ Set.range j := by
  obtain ⟨Z, j, hred, hj, hqc, hclass⟩ := LocalCharacterLieLocus.exists_reduced_local_character_lie_locus A ρ χ r C
  let := hj
  refine ⟨Z.left, j.left, hred, hj, hqc, ?_⟩
  intro T hT x
  let Tx : Over S := Over.mk (x ≫ C.V.ι)
  let : IsReduced Tx.left := hT
  let fx : Tx ⟶ Over.mk C.V.ι := Over.homMk x rfl
  have h := (hclass Tx fx).trans ((OverLocusClassification.over_existsUnique_lift_iff j fx).trans
    (Reduced.ImmersionFactorization.reduced_immersion_lift_iff_range j.left x))
  refine Iff.trans ?_ h
  constructor
  · intro hx k hk ha p
    exact (LieRankCharacter.characterLieRank_congr A ρ χ r (Category.assoc p x C.V.ι)).mpr (hx k p)
  · intro hx k hk ha p
    exact (LieRankCharacter.characterLieRank_congr A ρ χ r (Category.assoc p x C.V.ι)).mp (hx k p)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLieLocus
