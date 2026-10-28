import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct

/-! # Point Pair Continuity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PointPairContinuity.BundleCycles

noncomputable section

/-! Continuous parameterized pairing of genuine complex scheme points. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory

theorem schemePointPair_continuous_comp (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) {T : Type} [TopologicalSpace T]
    (f : T → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (g : T → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (show T → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ Y) from fun t =>
      (CycleClass.Thom.Scheme.PointProduct.Constructions.schemePointProductHomeomorph X Y).symm (f t, g t)) := by
  let k : C(T, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) := ⟨fun t => (f t, g t), hf.prodMk hg⟩
  let h : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ Y)) :=
    ⟨(CycleClass.Thom.Scheme.PointProduct.Constructions.schemePointProductHomeomorph X Y).symm,
      (CycleClass.Thom.Scheme.PointProduct.Constructions.schemePointProductHomeomorph X Y).symm.continuous⟩
  exact (h.comp k).continuous

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PointPairContinuity.BundleCycles
