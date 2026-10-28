import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition

/-! # Regular Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularImmersion.Constructions

noncomputable section

/-! The original smooth stratum of any projective cycle support is
the actual closed complex immersion on its regular ambient open. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

abbrev regularCycleImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (SmoothImmersion.Constructions.projectiveManifold V) D.regularAmbientOpen) p where
  regularComplexDimension := D.regularComplexDimension
  regularAnalyticSpace := TopCat.of D.regularAnalyticSpace
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := TopCat.ofHom
    ⟨D.regularComplementInclusion, D.isClosedEmbedding_regularComplementInclusion.continuous⟩
  holomorphic := D.contMDiff_regularComplementInclusion ω
  differential_injective := D.mfderiv_regularComplementInclusion_injective
  closed := D.isClosedEmbedding_regularComplementInclusion
  regularComplexDimension_add_codimension := D.regularComplexDimension_add_codimension

theorem regularCycleImmersion_Thom : (regularCycleImmersion D).regularThomClass = D.regularThomClass := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularImmersion.Constructions
