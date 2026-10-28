import OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialGraphDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport

/-! # Graph Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphDimension.Constructions

noncomputable section

/-! The actual affine normalization graph and each of its prime-divisor graphs have the codimensions required by the source Gysin formula and supported projection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialGraphDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

include a in
theorem sourceDimension_add_codimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom +
    Geometric.DimensionCycles.dimensionCodimension V W = Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom := by
  let D : Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V W) := ⟨W, rfl⟩
  have h := Normalization.GenericFibers.Constructions.Open.openSource_dimension D a
  exact (congrArg (fun n => n + Geometric.DimensionCycles.dimensionCodimension V W) h).trans D.regularComplexDimension_add_codimension

variable (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom]
  (j : Y ⟶ V.toOver) [IsOpenImmersion j.left] (d : ℕ)

include a j in
theorem parentGraph_dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom +
    (Geometric.DimensionCycles.dimensionCodimension V W + d) = Betti.AffineDimension.Realization.functionFieldDifferentialDimension (SchemeDivisor.GraphImage.Constructions.graphTarget Y d).hom := by
  have hs := sourceDimension_add_codimension V W a
  have ht := PolynomialGraphDimension.Constructions.graphTarget_ambient_dimension Y d j
  omega

variable (z : {x : X.left // Order.coheight x = 1})

include a j in
theorem affinePrimeGraph_codimension : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Scheme.RegularSupport.Constructions.regularOver X (SchemeDivisor.Purity.Constructions.primeSupport X z)).hom) → ℂ)
    (V.analyticModel × (Fin d → ℂ)) = (Geometric.DimensionCycles.dimensionCodimension V W + d) + 1 :=
  PolynomialGraphDimension.Constructions.primeGraph_codimension Y d j z (Geometric.DimensionCycles.dimensionCodimension V W + d) (parentGraph_dimension V W a Y j d)

omit [IsIntegral X.left] [Smooth X.hom] in
theorem coverPrimeGraph_codimension : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (NormalizationDivisor.Open.Constructions.Etale.sourceOpen V W (Open.PrimeSupport.Constructions.ambientPrime a z)).hom) → ℂ)
    (V.analyticModel × (Fin d → ℂ)) = (Geometric.DimensionCycles.dimensionCodimension V W + d) + 1 :=
  (NormalizationDivisor.GraphOpen.Constructions.sourceGraph_codimension V W (Open.PrimeSupport.Constructions.ambientPrime a z) d).trans (by omega)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.GraphDimension.Constructions
