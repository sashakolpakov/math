import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphRange
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates

/-! # Affine Graph Closed -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphClosed.Constructions

noncomputable section

/-! The lifted normalization divisor graph is closed because its actual image is the closed polynomial graph of the full divisor support in the affine source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphRange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions.GraphEmbedding OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (z : {x : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).left // Order.coheight x = 1})
  {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

omit [IsOpenImmersion a.left] [IsIntegral X.left] [Smooth X.hom] in
theorem affinePrimeSet_closed : IsClosed (AffineGraphRange.Constructions.affinePrimeSet V W z a) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    (Scheme.RegularSupport.Constructions.supportToAmbient (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) (SchemeDivisor.Purity.Constructions.primeSupport (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) z))).isClosed_range.preimage
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map a)

variable [IsAffine X.left] {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

omit [IsOpenImmersion a.left] [IsIntegral X.left] [Smooth X.hom] in
theorem affineFullGraph_closedEmbedding (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (AffineGraphRange.Constructions.affineFullGraph V W a f) :=
  Closed.GraphEmbedding.Constructions.graph_closedEmbedding (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)
    ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W)).comp (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map a))
    (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf)

variable (U : Opens V.analyticSpace)

omit [IsOpenImmersion a.left] [IsIntegral X.left] [Smooth X.hom] in
theorem affinePrimeGraphImage_closed (hf : Function.Surjective f) :
    IsClosed (AffineGraphRange.Constructions.affinePrimeGraphImage V W z a f U) :=
  ((affineFullGraph_closedEmbedding V W a f hf).isClosedMap _ (affinePrimeSet_closed V W z a)).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem coverAffineGraph_closedEmbedding
    (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))
    (hU : (U : Set V.analyticSpace) ⊆ GraphOpen.Constructions.goodAmbient V W z) (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (EtaleLocalGraph.Constructions.localGraph (Open.Constructions.Etale.coverMap V W z) (Analytic.Constructions.targetAmbientMap V W z) U
      (AffineCoordinates.Constructions.coverAffineCoordinates V W z U a hcover f)) := by
  refine ⟨AffineCoordinates.Constructions.GraphEmbedding.coverAffineGraph_isEmbedding V W z U a hcover f hf, ?_⟩
  rw [AffineGraphRange.Constructions.coverAffineGraph_range V W z a f U hcover hU]
  exact affinePrimeGraphImage_closed V W z a f U hf

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphClosed.Constructions
