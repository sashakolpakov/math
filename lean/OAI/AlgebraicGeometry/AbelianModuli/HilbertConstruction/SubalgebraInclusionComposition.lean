import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraBaseInclusion

/-! # Subalgebra Inclusion Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraInclusionComposition

noncomputable section

/-! Successive inclusions of coefficient subalgebras compose to the direct final inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem subalgebraBaseInclusionSpec_trans
    {R A : Type u} [CommRing R] [CommRing A] [Algebra A R]
    (C B : Subalgebra ℤ R) (hCB : C ≤ B) (D : Subalgebra A R) (hBD : B ≤ D.restrictScalars ℤ) :
    SubalgebraBaseInclusion.subalgebraBaseInclusionSpec B D hBD ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCB).toRingHom) =
      SubalgebraBaseInclusion.subalgebraBaseInclusionSpec C D (hCB.trans hBD) := by
  change Spec.map (CommRingCat.ofHom (SubalgebraBaseInclusion.subalgebraBaseInclusion B D hBD)) ≫
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCB).toRingHom) =
      Spec.map (CommRingCat.ofHom (SubalgebraBaseInclusion.subalgebraBaseInclusion C D (hCB.trans hBD)))
  rw [← Spec.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubalgebraInclusionComposition
