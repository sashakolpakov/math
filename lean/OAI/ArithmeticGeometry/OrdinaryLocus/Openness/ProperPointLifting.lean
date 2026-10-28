import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Group.Abelian

/-! # Proper Point Lifting -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProperPointLifting.Construction

noncomputable section

/-! Rational points lift through proper surjective morphisms over an algebraically closed field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CartesianMonoidalCategory MonoidalCategory

universe u

theorem exists_point_lift_of_proper_surjective
    {K : Type u} [Field K] [IsAlgClosed K] {A G : Over (Spec (.of K))}
    (q : A ⟶ G) [IsProper q.left] [Surjective q.left]
    (s : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    ∃ a : 𝟙_ (Over (Spec (.of K))) ⟶ A, a ≫ q = s := by
  let Y := pullback q.left s.left
  let ρ : Y ⟶ Spec (.of K) := pullback.snd q.left s.left
  have : IsProper ρ := inferInstanceAs (IsProper (pullback.snd q.left s.left))
  have : Surjective ρ := inferInstanceAs (Surjective (pullback.snd q.left s.left))
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace ρ
  have : Nonempty Y := ⟨(ρ.surjective (IsLocalRing.closedPoint K)).choose⟩
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints (Set.univ_nonempty : (Set.univ : Set Y).Nonempty)
    isOpen_univ.isLocallyClosed
  let r := pointOfClosedPoint ρ y hy
  have hr : r ≫ ρ = 𝟙 _ := pointOfClosedPoint_comp ρ y hy
  let a₀ : Spec (.of K) ⟶ A.left := r ≫ pullback.fst q.left s.left
  have ha₀ : a₀ ≫ q.left = s.left := by
    change (r ≫ pullback.fst q.left s.left) ≫ q.left = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hr, Category.id_comp]
  let a : 𝟙_ (Over (Spec (.of K))) ⟶ A := Over.homMk a₀ (by
    rw [← Over.w q, ← Category.assoc, ha₀]
    exact Over.w s)
  exact ⟨a, Over.OverMorphism.ext ha₀⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProperPointLifting.Construction
