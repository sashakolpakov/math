import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Closed Lift -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ClosedLift

noncomputable section

/-! A reduced source lifts across a surjective closed immersion. The
actual lift preserves open and closed immersions by its pullback square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y Z : Scheme.{0}} [IsReduced X] (i : Z ⟶ Y) [IsClosedImmersion i] [Surjective i]
    (f : X ⟶ Y)

def reducedClosedLift : X ⟶ Z :=
  let _ : IsIso (pullback.fst f i) := isIso_of_isClosedImmersion_of_surjective (pullback.fst f i)
  inv (pullback.fst f i) ≫ pullback.snd f i

theorem reducedClosedLift_comp : reducedClosedLift i f ≫ i = f := by
  have : IsIso (pullback.fst f i) := isIso_of_isClosedImmersion_of_surjective (pullback.fst f i)
  change (inv (pullback.fst f i) ≫ pullback.snd f i) ≫ i = f
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem reducedClosedLift_open [IsOpenImmersion f] : IsOpenImmersion (reducedClosedLift i f) := by
  have : IsIso (pullback.fst f i) := isIso_of_isClosedImmersion_of_surjective (pullback.fst f i)
  change IsOpenImmersion (inv (pullback.fst f i) ≫ pullback.snd f i)
  infer_instance

theorem reducedClosedLift_closed [IsClosedImmersion f] : IsClosedImmersion (reducedClosedLift i f) := by
  have : IsIso (pullback.fst f i) := isIso_of_isClosedImmersion_of_surjective (pullback.fst f i)
  change IsClosedImmersion (inv (pullback.fst f i) ≫ pullback.snd f i)
  infer_instance

variable {B : Scheme.{0}} {V W T : Over B}

def reducedClosedOverLift (j : W ⟶ T) [IsClosedImmersion j.left] [Surjective j.left]
    (g : V ⟶ T) [IsReduced V.left] : V ⟶ W :=
  Over.homMk (reducedClosedLift j.left g.left) (by
    rw [← j.w, ← Category.assoc, reducedClosedLift_comp, g.w])

theorem reducedClosedOverLift_comp (j : W ⟶ T) [IsClosedImmersion j.left] [Surjective j.left]
    (g : V ⟶ T) [IsReduced V.left] : reducedClosedOverLift j g ≫ j = g :=
  Over.OverMorphism.ext (reducedClosedLift_comp j.left g.left)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ClosedLift
