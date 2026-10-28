import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Rational Point Lift -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalPointLift.Construction

noncomputable section

/-! A surjective morphism locally of finite type lifts rational points over an
algebraically closed field, by choosing a closed point in the actual fiber. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}

theorem exists_rationalPoint_lift (f : X ⟶ Y) [Surjective f] [LocallyOfFiniteType f]
    (s : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ t : Spec (CommRingCat.of K) ⟶ X, t ≫ f = s := by
  let F := pullback f s
  let p : F ⟶ Spec (CommRingCat.of K) := pullback.snd f s
  have : Surjective p := inferInstanceAs (Surjective (pullback.snd f s))
  have : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (pullback.snd f s))
  have : JacobsonSpace F := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, _⟩ := p.surjective (IsLocalRing.closedPoint K)
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set F).Nonempty from ⟨x, trivial⟩) isOpen_univ.isLocallyClosed
  let t := pointOfClosedPoint p z hz
  refine ⟨t ≫ pullback.fst f s, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (t ≫ p) ≫ s = s
  rw [show t ≫ p = 𝟙 _ from pointOfClosedPoint_comp p z hz, Category.id_comp]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalPointLift.Construction
