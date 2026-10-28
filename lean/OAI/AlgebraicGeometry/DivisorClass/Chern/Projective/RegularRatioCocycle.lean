import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularRatios

/-! # Regular Ratio Cocycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularRatioCocycle

noncomputable section

/-! The actual projective coordinate ratios obey their regular-function cocycle identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectiveRegularRatio_self (n : ℕ) (i : Fin (n + 1))
    (W : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens) (hWi : W ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :
    RegularRatios.projectiveRegularRatio n i i W hWi = 1 := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective _
  simp only [Proj.one_apply, RegularRatios.projectiveRegularRatio, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_one]
  let di : x.val.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨MvPolynomial.X i, (Foundations.Scheme.ProjectiveCoordinateCover.mem_projectiveCoordinateOpen n i x.val).mp (hWi x.property)⟩
  exact Localization.mk_self di

theorem projectiveRegularRatio_mul (n : ℕ) (i j k : Fin (n + 1))
    (W : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens)
    (hWi : W ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (hWj : W ≤ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n j) :
    RegularRatios.projectiveRegularRatio n i j W hWi * RegularRatios.projectiveRegularRatio n j k W hWj =
      RegularRatios.projectiveRegularRatio n i k W hWi := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective _
  rw [Proj.mul_apply (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (RegularRatios.projectiveRegularRatio n i j W hWi)
    (RegularRatios.projectiveRegularRatio n j k W hWj) x, HomogeneousLocalization.val_mul]
  simp only [RegularRatios.projectiveRegularRatio, HomogeneousLocalization.val_mk]
  let di : x.val.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨MvPolynomial.X i, (Foundations.Scheme.ProjectiveCoordinateCover.mem_projectiveCoordinateOpen n i x.val).mp (hWi x.property)⟩
  let dj : x.val.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨MvPolynomial.X j, (Foundations.Scheme.ProjectiveCoordinateCover.mem_projectiveCoordinateOpen n j x.val).mp (hWj x.property)⟩
  change Localization.mk (MvPolynomial.X j) di * Localization.mk (MvPolynomial.X k) dj =
    Localization.mk (MvPolynomial.X k) di
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, di, dj]
  ac_rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.RegularRatioCocycle
