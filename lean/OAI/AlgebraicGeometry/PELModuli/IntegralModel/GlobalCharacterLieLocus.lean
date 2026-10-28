import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SchemeCharacterLieLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.LocusGluing

/-! # Global Character Lie Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalCharacterLieLocus

noncomputable section

/-! The original character Lie-rank condition is represented on all
reduced tests by an actual reduced quasi-compact locally closed immersion.
The chart cover and every local quotient are constructed from the family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

theorem exists_global_character_lie_locus
    {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} [IsNoetherian S]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (χ : NumberField.RingOfIntegers E →+* Γ(S, ⊤)) (r : ℕ) :
    ∃ (L : Scheme.{0}) (j : L ⟶ S),
      IsReduced L ∧ IsImmersion j ∧ QuasiCompact j ∧
      ∀ (T : Scheme.{0}) [IsReduced T] (x : T ⟶ S),
        SchemeCharacterLiePredicate.HasCharacterLieRankOnSchemeMap A ρ χ r x ↔ ∃! f : T ⟶ L, f ≫ j = x := by
  choose C hC using fun x : S => AbelianConormalCharts.exists_abelian_conormal_chart A ρ (Finite.Actions.integralActionBasis E) x
  let U : S → S.Opens := fun x => (C x).V
  have hU : IsOpenCover U := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hC x⟩
  choose Z j hred hj hqc hclass using
    fun x : S => SchemeCharacterLieLocus.exists_local_scheme_character_lie_locus A ρ χ r (C x)
  exact Reduced.LocusGluing.exists_global_reduced_locus_of_local_classifiers
    (SchemeCharacterLiePredicate.schemeCharacterLieRankSubfunctor A ρ χ r) U hU Z j hj hclass
    (fun T _ x => SchemeCharacterLiePredicate.schemeCharacterLieRank_geometric_detection A ρ χ r T x)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalCharacterLieLocus
