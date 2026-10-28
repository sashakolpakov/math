import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationPointLift

/-! # Factorization Point Condition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationPointCondition

noncomputable section

/-! The projection-isomorphism test over the closed parameter is exactly the existence of a factorization with invertible projection over the original test map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def HasIsomorphicFactorization {R T : Scheme.{u}} {X P Z A : Over R}
    (j : Z ⟶ P) (i : X ⟶ P) (p : Z ⟶ A) (c : T ⟶ R) : Prop :=
  ∃ h : (Over.pullback c).obj X ⟶ (Over.pullback c).obj Z,
    h ≫ (Over.pullback c).map j = (Over.pullback c).map i ∧
      IsIso (h ≫ (Over.pullback c).map p)

theorem HasIsomorphicFactorization.existsUnique {R T : Scheme.{u}} {X P Z A : Over R}
    {j : Z ⟶ P} [IsClosedImmersion j.left] {i : X ⟶ P} {p : Z ⟶ A} {c : T ⟶ R}
    (hc : HasIsomorphicFactorization j i p c) :
    ∃! h : (Over.pullback c).obj X ⟶ (Over.pullback c).obj Z,
      h ≫ (Over.pullback c).map j = (Over.pullback c).map i := by
  obtain ⟨h, hh, _⟩ := hc
  have : IsClosedImmersion ((Over.pullback c).map j).left := Projective.PresentationBaseChange.overPullback_map_closed j c
  have : Mono ((Over.pullback c).map j) := Over.mono_of_mono_left _
  exact ⟨h, hh, fun k hk => (cancel_mono _).mp (hk.trans hh.symm)⟩

theorem factorizationPointLift_condition_iff
    {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z A : Over M.left}
    [IsProper X.hom] [Flat X.hom] (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P)
    (p : Z ⟶ A) {T : Over S} (c : T ⟶ Proper.FactorizationParameter.properFactorizationParameter M j i) :
    HasIsomorphicFactorization j i p (c ≫ Proper.FactorizationParameter.properFactorizationParameterInclusion M j i).left ↔
      IsIso ((Over.pullback c.left).map (FactorizationProjection.factorizationProjection M j i p)) := by
  constructor
  · rintro ⟨h, hh, hi⟩
    have he := FactorizationPointLift.factorizationPointLift_unique M j i c h hh
    rw [he] at hi
    exact (FactorizationPointLift.factorizationPointLift_projection_isIso_iff M j i c p).mp hi
  · intro hi
    exact ⟨FactorizationPointLift.factorizationPointLift M j i c, FactorizationPointLift.factorizationPointLift_fac M j i c,
      (FactorizationPointLift.factorizationPointLift_projection_isIso_iff M j i c p).mpr hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationPointCondition
