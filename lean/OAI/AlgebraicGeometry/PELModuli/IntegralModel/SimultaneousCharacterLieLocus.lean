import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalCharacterLieLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ReducedLocusIntersection

/-! # Simultaneous Character Lie Locus -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SimultaneousCharacterLieLocus

noncomputable section

/-! All finitely many prescribed integral characters are imposed on the
actual family by a constructed reduced locally closed intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_simultaneous_character_lie_locus
    {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} [IsNoetherian S]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    {I : Type} [Finite I] (χ : I → (NumberField.RingOfIntegers E →+* Γ(S, ⊤))) (r : I → ℕ) :
    ∃ (L : Scheme.{0}) (j : L ⟶ S),
      IsReduced L ∧ IsImmersion j ∧ QuasiCompact j ∧
      ∀ (T : Scheme.{0}) [IsReduced T] (x : T ⟶ S),
        (∀ i, SchemeCharacterLiePredicate.HasCharacterLieRankOnSchemeMap A ρ (χ i) (r i) x) ↔
          ∃! f : T ⟶ L, f ≫ j = x := by
  choose Z j hred hj hqc hclass using fun i => GlobalCharacterLieLocus.exists_global_character_lie_locus A ρ (χ i) (r i)
  obtain ⟨L, a, hL, ha, hqa, hc⟩ := IntegralModel.Finite.ReducedLocusIntersection.exists_finite_reduced_locus_intersection Z j hj
  refine ⟨L, a, hL, ha, hqa, ?_⟩
  intro T hT x
  exact (forall_congr' (fun i => hclass i T x)).trans (hc T x)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SimultaneousCharacterLieLocus
