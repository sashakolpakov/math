import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapFunctionField

/-! # Function Field Injectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FunctionFieldInjectivity

noncomputable section

/-! The chart and overlap maps to the fraction field are injective;
rational-function identities therefore detect actual regular sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

theorem localizationFunctionFieldMap_injective (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0) :
    Function.Injective (ChartFunctionField.localizationFunctionFieldMap K f hf) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f)
    (ChartFunctionField.localizationFunctionFieldMap K f hf)).mpr
  intro x y
  constructor
  · exact congrArg (ChartFunctionField.localizationFunctionFieldMap K f hf)
  · intro h
    rw [ChartFunctionField.localizationFunctionFieldMap_algebraMap, ChartFunctionField.localizationFunctionFieldMap_algebraMap] at h
    exact congrArg (algebraMap _ (Localization.Away f)) ((IsFractionRing.injective _ _) h)

theorem homogeneousChartFunctionFieldMap_injective (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0) :
    Function.Injective (ChartFunctionField.homogeneousChartFunctionFieldMap K f hf) :=
  (localizationFunctionFieldMap_injective K f hf).comp (HomogeneousLocalization.val_injective _)

theorem projectiveOverlapFunctionFieldMap_injective (i j : Fin (n + 1)) :
    Function.Injective (Projective.OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j) :=
  (homogeneousChartFunctionFieldMap_injective K (X i * X j)
    (mul_ne_zero (X_ne_zero i) (X_ne_zero j))).comp
      (ConcreteCategory.bijective_of_isIso (Projective.OverlapSectionUnits.projectiveDoubleSectionIso K i j).inv).injective

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FunctionFieldInjectivity
