import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.CharacterLieLocus
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.ClopenLocusIntersection

/-! # Simultaneous Character Lie Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SimultaneousCharacterLieLocus

noncomputable section

/-! Finitely many prescribed character Lie ranks are imposed by their
actual clopen intersection, on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_simultaneous_character_lie_rank_open
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {S : Scheme.{0}} [IsLocallyNoetherian S] [Algebra ℚ Γ(S, ⊤)]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    {I : Type} [Finite I] (χ : I → (NumberField.RingOfIntegers E →+* Γ(S, ⊤))) (r : I → ℕ) :
    ∃ L : S.Opens, IsClosed (L : Set S) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S),
        (∀ i, PELModuli.IntegralModel.SchemeCharacterLiePredicate.HasCharacterLieRankOnSchemeMap A ρ (χ i) (r i) x) ↔
          ∃! f : T ⟶ L.toScheme, f ≫ L.ι = x := by
  choose L hL hclass using fun i => Global.CharacterLieLocus.exists_global_character_lie_rank_open A ρ (χ i) (r i)
  obtain ⟨U, hU, hc⟩ := ReferenceFamily.Finite.ClopenLocusIntersection.finiteClopenLocusIntersection L hL
  refine ⟨U, hU, ?_⟩
  intro T x
  exact (forall_congr' (fun i => hclass i T x)).trans (hc T x)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SimultaneousCharacterLieLocus
