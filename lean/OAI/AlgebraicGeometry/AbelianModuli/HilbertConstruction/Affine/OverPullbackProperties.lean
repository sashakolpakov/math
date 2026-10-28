import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Over Pullback Properties -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverPullbackProperties

noncomputable section

/-! Pulling an affine smooth chart back along an ambient affine open immersion preserves its properties. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {C : Type u} [CommRing C] {B X Y : Over (Spec (.of C))}
variable (b : B ⟶ Y) (g : X ⟶ Y)

theorem affineOverPullback_isPullback :
    IsPullback (pullback.fst b g).left (pullback.snd b g).left b.left g.left :=
  (IsPullback.of_hasPullback b g).map (Over.forget _)

theorem affineOverPullback_affine [IsAffine B.left] [IsAffine X.left] [IsAffine Y.left] :
    IsAffine (pullback b g).left := by
  have : IsAffine (pullback b.left g.left) := inferInstance
  exact IsAffine.of_isIso (affineOverPullback_isPullback b g).isoPullback.hom

theorem affineOverPullback_smooth [Smooth B.hom] [IsOpenImmersion g.left] :
    Smooth (pullback b g).hom := by
  have : IsOpenImmersion (pullback.fst b g).left :=
    MorphismProperty.of_isPullback (affineOverPullback_isPullback b g).flip inferInstance
  have hs : Smooth ((pullback.fst b g).left ≫ B.hom) := inferInstance
  exact (congrArg Smooth (pullback.fst b g).w).mp hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverPullbackProperties
