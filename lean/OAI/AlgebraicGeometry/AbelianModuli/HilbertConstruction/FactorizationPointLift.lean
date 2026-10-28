import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.CompositionMorphism

/-! # Factorization Point Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationPointLift

noncomputable section

/-! A point of the closed factorization parameter recovers the unique factorization over its composite map to the original parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z : Over M.left}
variable [IsProper X.hom] [Flat X.hom] (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P)
variable {T : Over S} (c : T ⟶ Proper.FactorizationParameter.properFactorizationParameter M j i)

def factorizationPointLift :
    (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj X ⟶
      (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj Z :=
  Pullback.CompositionMorphism.overPullbackCompositionMorphism c.left (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left
    (Proper.UniversalFactorization.properUniversalFactorization M j i)

theorem factorizationPointLift_fac :
    factorizationPointLift M j i c ≫
      (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j =
        (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).map i :=
  Pullback.CompositionMorphism.overPullbackCompositionMorphism_factorization c.left (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left
    (Proper.UniversalFactorization.properUniversalFactorization M j i) j i (Proper.UniversalFactorization.properUniversalFactorization_fac M j i)

theorem factorizationPointLift_unique
    (h : (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj X ⟶
      (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).obj Z)
    (hh : h ≫ (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j =
      (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).map i) :
    h = factorizationPointLift M j i c := by
  have : IsClosedImmersion
      ((Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j).left :=
    Projective.PresentationBaseChange.overPullback_map_closed j _
  have : Mono ((Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).map j) :=
    Over.mono_of_mono_left _
  exact (cancel_mono _).mp (hh.trans (factorizationPointLift_fac M j i c).symm)

theorem factorizationPointLift_projection_isIso_iff {A : Over M.left} (p : Z ⟶ A) :
    IsIso (factorizationPointLift M j i c ≫
      (Over.pullback (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left).map p) ↔
        IsIso ((Over.pullback c.left).map (FactorizationProjection.factorizationProjection M j i p)) := by
  change IsIso (Pullback.CompositionMorphism.overPullbackCompositionMorphism c.left (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left
      (Proper.UniversalFactorization.properUniversalFactorization M j i) ≫
        (Over.pullback (c.left ≫ (Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left)).map p) ↔ _
  rw [Pullback.CompositionMorphism.overPullbackCompositionMorphism_comp, Pullback.CompositionMorphism.overPullbackCompositionMorphism_isIso_iff]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationPointLift
