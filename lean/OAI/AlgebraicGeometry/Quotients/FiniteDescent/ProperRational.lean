import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Proper Rational -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperRational

noncomputable section

/-! A rational point lifts through a proper surjection over an
algebraically closed field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.ProperRationalLift

theorem exists_lift {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (q : X ⟶ Y) [IsProper q] [Surjective q] (p : Spec (.of K) ⟶ Y) :
    ∃ s : Spec (.of K) ⟶ X, s ≫ q = p := by
  let f := pullback.snd q p
  have : IsProper f := inferInstanceAs (IsProper (pullback.snd q p))
  have : Surjective f := inferInstanceAs (Surjective (pullback.snd q p))
  have : Nonempty (pullback q p : Scheme.{u}) := by
    obtain ⟨z, _⟩ := f.surjective (IsLocalRing.closedPoint K)
    exact ⟨z⟩
  have : JacobsonSpace (pullback q p : Scheme.{u}) := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set (pullback q p : Scheme.{u})).Nonempty) isOpen_univ.isLocallyClosed
  let s := pointOfClosedPoint f z hz
  refine ⟨s ≫ pullback.fst q p, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end Construction.ProperRationalLift

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperRational
