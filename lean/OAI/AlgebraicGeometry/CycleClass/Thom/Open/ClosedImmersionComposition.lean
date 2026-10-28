import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion

/-! # Closed Immersion Composition -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold

/-! Actual open submanifolds and the actual source of a closed complex
immersion, with their original inherited analytic structures. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions

abbrev openManifold (V : Closed.ComplexImmersion.Constructions.ComplexManifold) (U : Opens V.analyticSpace) : Closed.ComplexImmersion.Constructions.ComplexManifold where
  complexDimension := V.complexDimension
  analyticSpace := TopCat.of U
  chartedSpace := inferInstance
  manifold := inferInstance
  metrizable := U.isOpenEmbedding'.isEmbedding.metrizableSpace

abbrev sourceManifold {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p) :
    Closed.ComplexImmersion.Constructions.ComplexManifold where
  complexDimension := Z.regularComplexDimension
  analyticSpace := Z.regularAnalyticSpace
  chartedSpace := inferInstance
  manifold := inferInstance
  metrizable := inferInstance

end AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold

namespace AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions

/-! The actual composite of two closed complex immersions has the
sum codimension and the composite native differential. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold

set_option backward.isDefEq.respectTransparency false

def compose {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p q : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
    (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (ComplexManifold.sourceManifold Z) q) : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V (p + q) where
  regularComplexDimension := C.regularComplexDimension
  regularAnalyticSpace := C.regularAnalyticSpace
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := C.regularComplementTopCatMap ≫ Z.regularComplementTopCatMap
  holomorphic := Z.holomorphic.comp C.holomorphic
  differential_injective := fun x => by
    change Function.Injective (mfderiv 𝓘(ℂ, C.regularAnalyticModel) 𝓘(ℂ, V.analyticModel)
      (Z.regularComplementInclusion ∘ C.regularComplementInclusion) x)
    rw [mfderiv_comp x ((Z.holomorphic _).mdifferentiableAt (by simp))
      ((C.holomorphic x).mdifferentiableAt (by simp))]
    exact (Z.differential_injective _).comp (C.differential_injective x)
  closed := Z.closed.comp C.closed
  regularComplexDimension_add_codimension := by
    have hZ := Z.regularComplexDimension_add_codimension
    have hC := C.regularComplexDimension_add_codimension
    change C.regularComplexDimension + q = Z.regularComplexDimension at hC
    omega

end AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions

end

end OAI
