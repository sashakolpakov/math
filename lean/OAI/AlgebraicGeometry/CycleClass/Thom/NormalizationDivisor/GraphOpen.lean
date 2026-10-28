import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Boundary
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.DenseOpenImage

/-! # Graph Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions

noncomputable section

/-! The constructed normalization prime-divisor covers retain their actual image cycle and codimension on the complement of their omitted boundaries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Regular
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Boundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Image.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.DenseOpenImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})

def goodAmbient : Opens V.analyticSpace := ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (Boundary.Constructions.omittedBoundary V W z)

theorem targetGoodOpen_smooth : Boundary.Constructions.targetGoodOpen V W z ≤ (Image.Constructions.imageCycleSupport V W z).structureMap.smoothLocus := by
  let j : Open.Constructions.Etale.targetOpen V W z ⟶ (Image.Constructions.imageCycleSupport V W z).toOver := Open.Constructions.Regular.targetToSupport V W z
  have hj : j.left ≫ (Image.Constructions.imageCycleSupport V W z).structureMap = (Open.Constructions.Etale.targetOpen V W z).hom := j.w
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (Open.Constructions.Regular.targetToSupport V W z).left)
  let : Smooth (j.left ≫ (Image.Constructions.imageCycleSupport V W z).structureMap) := by rw [hj]; infer_instance
  exact Product.SupportTo.Constructions.SmoothOpen.openImmersion_range_subset_smoothLocus j.left (Image.Constructions.imageCycleSupport V W z).structureMap

theorem goodAmbient_regular :
    (goodAmbient V W z : Set V.analyticSpace) ⊆ (Image.Constructions.imageCycleSupport V W z).regularAmbientOpen :=
  ProperImage.Open.Constructions.Construction.boundaryComplement_subset_regularAmbient (Image.Constructions.imageCycleSupport V W z) (Boundary.Constructions.targetGoodOpen V W z)
    (targetGoodOpen_smooth V W z)

theorem targetAmbientMap_range (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ goodAmbient V W z) :
    ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Analytic.Constructions.targetAmbientMap V W z))) =
      Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion (Image.Constructions.imageCycleSupport V W z) U (hU.trans (goodAmbient_regular V W z))) :=
  Cycle.DenseOpenImage.Constructions.supportOpenImmersion_regularImage (Image.Constructions.imageCycleSupport V W z) (Open.Constructions.Regular.targetToSupport V W z) U hU
    (hU.trans (goodAmbient_regular V W z))

theorem sourceGraph_codimension (d : ℕ) :
    Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension
      (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.sourceOpen V W z).hom) → ℂ)
      (V.analyticModel × (Fin d → ℂ)) = (Geometric.DimensionCycles.dimensionCodimension V W + 1) + d := by
  change Module.finrank ℂ (V.analyticModel × (Fin d → ℂ)) -
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Open.Constructions.Etale.sourceOpen V W z).hom) → ℂ) = _
  simp only [Module.finrank_prod, Module.finrank_fin_fun]
  rw [Analytic.Constructions.cover_dimensions_eq, Analytic.Constructions.targetOpen_dimension]
  have hd := (Image.Constructions.imageCycleSupport V W z).regularComplexDimension_add_codimension
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions
