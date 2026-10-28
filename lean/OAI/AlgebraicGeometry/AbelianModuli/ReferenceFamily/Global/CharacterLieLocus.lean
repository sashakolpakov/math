import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CharacterLieLocus
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClopenLocusGluing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLiePredicate

/-! # Character Lie Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.CharacterLieLocus

noncomputable section

/-! The literal character Lie-rank condition for the original abelian
family is represented by a clopen subscheme on all test schemes. The
local charts and their projective character quotients are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLiePredicate

theorem exists_global_character_lie_rank_open
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {S : Scheme.{0}} [IsLocallyNoetherian S] [Algebra ℚ Γ(S, ⊤)]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (χ : NumberField.RingOfIntegers E →+* Γ(S, ⊤)) (r : ℕ) :
    ∃ L : S.Opens, IsClosed (L : Set S) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S),
        PELModuli.IntegralModel.SchemeCharacterLiePredicate.HasCharacterLieRankOnSchemeMap A ρ χ r x ↔ ∃! f : T ⟶ L.toScheme, f ≫ L.ι = x := by
  choose C hC using fun x : S => PELModuli.IntegralModel.AbelianConormalCharts.exists_abelian_conormal_chart A ρ (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E) x
  let U : S → S.Opens := fun x => (C x).V
  have hU : IsOpenCover U := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hC x⟩
  have hlocal (x : S) :
      ∃ (Z : Scheme.{0}) (j : Z ⟶ (U x).toScheme), IsOpenImmersion j ∧ IsClosedImmersion j ∧
        ∀ (T : Scheme.{0}) (f : T ⟶ (U x).toScheme),
          f ≫ (U x).ι ∈ (PELModuli.IntegralModel.SchemeCharacterLiePredicate.schemeCharacterLieRankSubfunctor A ρ χ r).obj (.op T) ↔
            ∃! q : T ⟶ Z, q ≫ j = f := by
    let : Algebra ℚ Γ((C x).V.toScheme, ⊤) :=
      ((C x).V.ι.appTop.hom.comp (algebraMap ℚ Γ(S, ⊤))).toAlgebra
    obtain ⟨Z, j, hj, hcj, hclass⟩ := Local.CharacterLieLocus.exists_local_character_lie_locus A ρ χ r (C x)
    refine ⟨Z, j, hj, hcj, ?_⟩
    intro T f
    refine Iff.trans ?_ (hclass T f)
    constructor
    · intro hf k hk ha p
      exact (PELModuli.IntegralModel.LieRankCharacter.characterLieRank_congr A ρ χ r (Category.assoc p f (U x).ι)).mpr (hf k p)
    · intro hf k hk ha p
      exact (PELModuli.IntegralModel.LieRankCharacter.characterLieRank_congr A ρ χ r (Category.assoc p f (U x).ι)).mp (hf k p)
  choose Z j hj hcj hclass using hlocal
  exact ClopenLocusGluing.exists_global_clopen_locus_of_local_classifiers
    (PELModuli.IntegralModel.SchemeCharacterLiePredicate.schemeCharacterLieRankSubfunctor A ρ χ r) U hU Z j hj hcj hclass
    (PELModuli.IntegralModel.SchemeCharacterLiePredicate.schemeCharacterLieRank_geometric_detection A ρ χ r)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.CharacterLieLocus
