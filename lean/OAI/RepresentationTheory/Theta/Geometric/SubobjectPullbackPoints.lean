import OAI.RepresentationTheory.Theta.Geometric.Affine.TestMonomorphisms

/-! # Subobject Pullback Points -/

namespace OAI.RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints

noncomputable section

/-! An actual base change of a scheme subobject classifies the same
lifts after composing the test map with the base map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

def subobjectPullback {B S : Scheme.{u}} (M : Over B) (a : S ⟶ B) : Over S :=
  Over.mk (pullback.snd M.hom a)

instance subobjectPullback_mono {B S : Scheme.{u}} (M : Over B) [Mono M.hom] (a : S ⟶ B) :
    Mono (subobjectPullback M a).hom := inferInstanceAs (Mono (pullback.snd M.hom a))

theorem subobjectPullback_hasLift_iff {B S : Scheme.{u}} (M : Over B) (a : S ⟶ B) (T : Over S) :
    Nonempty (T ⟶ subobjectPullback M a) ↔ Nonempty (Over.mk (T.hom ≫ a) ⟶ M) := by
  constructor
  · rintro ⟨p⟩
    refine ⟨Over.homMk (p.left ≫ pullback.fst M.hom a) ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun f => f ≫ a) p.w
  · rintro ⟨p⟩
    exact ⟨Over.homMk (pullback.lift p.left T.hom p.w) (pullback.lift_snd _ _ _)⟩

end

end OAI.RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints
