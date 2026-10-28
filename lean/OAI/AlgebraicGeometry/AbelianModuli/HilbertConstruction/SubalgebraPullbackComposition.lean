import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraInclusionComposition
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Subalgebra Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraPullbackComposition

noncomputable section

/-! Base change through an intermediate coefficient subalgebra agrees with direct final base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def subalgebraPullbackCompIso
    {R A : Type u} [CommRing R] [CommRing A] [Algebra A R]
    (C B : Subalgebra ℤ R) (hCB : C ≤ B) (D : Subalgebra A R) (hBD : B ≤ D.restrictScalars ℤ)
    (X : Over (Spec (.of C))) :
    (Over.pullback (SubalgebraBaseInclusion.subalgebraBaseInclusionSpec B D hBD)).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCB).toRingHom))).obj X) ≅
      (Over.pullback (SubalgebraBaseInclusion.subalgebraBaseInclusionSpec C D (hCB.trans hBD))).obj X := by
  let c := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCB).toRingHom)
  let d := SubalgebraBaseInclusion.subalgebraBaseInclusionSpec B D hBD
  exact (Over.pullbackComp d c).symm.app X ≪≫
    eqToIso (congrArg (fun f => (Over.pullback f).obj X)
      (SubalgebraInclusionComposition.subalgebraBaseInclusionSpec_trans C B hCB D hBD))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraPullbackComposition
