import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EtaleCancellationOf
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Quasi
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Finite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Finite.FiniteQuotientGeometry

/-! Finiteness of the constructed quotient over its original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem separated_of_finite_cover
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [IsFinite q] [Surjective q] [IsSeparated (q ≫ b)] [Etale b] : IsSeparated b := by
  let p := pullback.map (q ≫ b) (q ≫ b) b b q q (𝟙 S)
    (Category.comp_id _) (Category.comp_id _)
  have hp : IsFinite p :=
    MorphismProperty.pullbackMap (P := @IsFinite) (inferInstance : IsFinite q)
      (inferInstance : IsFinite q) rfl rfl
  have hp₁ : p ≫ pullback.fst b b = pullback.fst (q ≫ b) (q ≫ b) ≫ q :=
    pullback.lift_fst _ _ _
  have hp₂ : p ≫ pullback.snd b b = pullback.snd (q ≫ b) (q ≫ b) ≫ q :=
    pullback.lift_snd _ _ _
  have he : q ≫ pullback.diagonal b = pullback.diagonal (q ≫ b) ≫ p := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hp₁, pullback.diagonal_fst,
        pullback.diagonal_fst_assoc, Category.comp_id]
    · simp only [Category.assoc, hp₂, pullback.diagonal_snd,
        pullback.diagonal_snd_assoc, Category.comp_id]
  have : IsFinite (q ≫ pullback.diagonal b) := by
    rw [he]
    infer_instance
  have : UniversallyClosed (pullback.diagonal b) :=
    UniversallyClosed.of_comp_surjective q (pullback.diagonal b)
  have hc : IsClosed (Set.range (pullback.diagonal b)) :=
    (pullback.diagonal b).isClosedMap.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hc⟩

theorem finite_etale_of_finite_flat_cover
    {X Q S : Scheme.{u}} (q : X ⟶ Q) (b : Q ⟶ S)
    [IsFinite q] [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    [IsFinite (q ≫ b)] [Etale (q ≫ b)] : IsFinite b ∧ Etale b := by
  have : Etale b := EtaleCancellationOf.EtaleCancellation.etale_of_finite_flat_cover q b
  have : IsSeparated b := separated_of_finite_cover q b
  have : UniversallyClosed b := UniversallyClosed.of_comp_surjective q b
  have : IsProper b := ⟨⟩
  have : LocallyQuasiFinite b := Quasi.TorsionGeometry.locallyQuasiFinite_of_formallyUnramified b
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite b, inferInstance⟩

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Finite.FiniteQuotientGeometry
