import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Closed Rational Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedRationalPoints

noncomputable section

/-! A nonempty scheme locally of finite type over an algebraically closed field has a rational point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem nonempty_locallyFiniteType_exists_section {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] [Nonempty X] :
    ∃ s : Spec (.of K) ⟶ X, s ≫ p = 𝟙 _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set X).Nonempty from ⟨Nonempty.some inferInstance, trivial⟩)
    isOpen_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint p x hx, pointOfClosedPoint_comp p x hx⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedRationalPoints
