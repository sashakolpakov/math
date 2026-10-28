import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackCongrPaths
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

/-! # Canonical Gluing Standard -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluingStandard

noncomputable section

/-!
# The canonical affine comparison uses standard geometric Čech gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (i j : S ⟶ T) (h : f ≫ i = f ≫ j)

include h in
/-- The scheme projection equation arising from equal affine coordinate maps. -/
theorem projection_eq : Spec.map i ≫ Spec.map f = Spec.map j ≫ Spec.map f :=
  (Spec.map_comp f i).symm.trans ((congrArg Spec.map h).trans (Spec.map_comp f j))

/-- Coordinate-normalized affine gluing is the standard geometric pullback-composition gluing. -/
theorem geometricTransition_eq_standard :
    CanonicalGluing.geometricTransition f i j h = Cech.MateNormalization.standardGluing
      (Spec.map f) (Spec.map i) (Spec.map j) (projection_eq f i j h) := by
  have ht := PullbackCongrPaths.normalize (Spec.map_comp f i).symm (congrArg Spec.map h)
    (Spec.map_comp f j).symm (Scheme.Modules.pullbackComp (Spec.map i) (Spec.map f))
    (Scheme.Modules.pullbackComp (Spec.map j) (Spec.map f))
  exact (CanonicalGluing.geometricTransition_eq f i j h).trans ht

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluingStandard
