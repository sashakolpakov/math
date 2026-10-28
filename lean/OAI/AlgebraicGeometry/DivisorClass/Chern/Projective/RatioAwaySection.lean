import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularRatios
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveChartToPolynomial

/-! # Ratio Away Section -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RatioAwaySection

noncomputable section

/-! The constructed regular ratio is the actual homogeneous-localization coordinate section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def projectiveRatioAwayElement (n : ℕ) (i j : Fin (n + 1)) : Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartRing n i :=
  HomogeneousLocalization.Away.mk (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n i)
    1 (MvPolynomial.X j) (by simpa only [one_smul] using Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous n j)

theorem projectiveRegularRatio_eq_awayToSection (n : ℕ) (i j : Fin (n + 1)) :
    RegularRatios.projectiveRegularRatio n i j (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) le_rfl =
      Proj.awayToSection (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (MvPolynomial.X i) (projectiveRatioAwayElement n i j) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective _
  have h := ProjectiveSpectrum.Proj.awayToSection_apply (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    (MvPolynomial.X i) (projectiveRatioAwayElement n i j) x
  refine Eq.trans ?_ h.symm
  simp only [RegularRatios.projectiveRegularRatio, HomogeneousLocalization.val_mk,
    projectiveRatioAwayElement, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk', RingHom.id_apply, pow_one]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RatioAwaySection
