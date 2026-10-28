import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FunctionGluing
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover

/-! # Regular Ratios -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularRatios

noncomputable section

/-! Actual regular homogeneous-coordinate ratios in the original projective scheme structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The native regular function `Xⱼ / Xᵢ` on any open contained in the `i`-th coordinate patch. -/
def projectiveRegularRatio (n : ℕ) (i j : Fin (n + 1))
    (W : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens) (hWi : W ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    Γ(Foundations.Scheme.ProjectiveSpace.projectiveSpace n, W) :=
  ⟨fun x => HomogeneousLocalization.mk
      ⟨1, ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X ℂ j⟩,
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩,
        (Foundations.Scheme.ProjectiveCoordinateCover.mem_projectiveCoordinateOpen n i x.val).mp (hWi x.property)⟩,
    fun x => ⟨W, x.property, 𝟙 W, 1,
      ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X ℂ j⟩,
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩,
      fun y => (Foundations.Scheme.ProjectiveCoordinateCover.mem_projectiveCoordinateOpen n i y.val).mp (hWi y.property), fun _ => rfl⟩⟩

@[simp] theorem projectiveRegularRatio_restrict (n : ℕ) (i j : Fin (n + 1))
    (U W : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens) (hWU : W ≤ U) (hUi : U ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    Regular.FunctionGluing.regularRestriction hWU (projectiveRegularRatio n i j U hUi) =
      projectiveRegularRatio n i j W (hWU.trans hUi) := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularRatios
