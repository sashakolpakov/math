import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorRegularImage
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeGraphRange
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage

/-! # Divisor Graph Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGraphImage.Constructions

noncomputable section

/-! The actual divisor immersion used by the affine-source Gysin formula has exactly the constructed normalization divisor cover graph as its image in the product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.PrimeSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.GraphOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorRegularImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeGraphRange.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.GraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.OpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineGraphRange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.AffineCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Open.Constructions.Etale OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationDivisor.Analytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleLocalGraph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : Smooth (Normalization.AmbientMap.Constructions.smoothNormalizationOver V W).hom := Normalization.AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ Normalization.AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left] [QuasiCompact a.left]
  (g : X ⟶ Y) (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (hs : a ≫ Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  [IsClosedImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (SchemeDivisor.GraphImage.Constructions.graphTarget Y d))]
  (z : {x : X.left // Order.coheight x = 1}) (q : ℕ)
  (hq : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + q =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (SchemeDivisor.GraphImage.Constructions.graphTarget Y d).hom)
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ NormalizationDivisor.GraphOpen.Constructions.goodAmbient V W (Open.PrimeSupport.Constructions.ambientPrime a z))
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

theorem affineDivisorImmersion_eq_coverGraph_image :
    Set.range (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ ∘
      (SchemeDivisor.OpenImmersion.Constructions.divisorOpenImmersion (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) z q hq (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)
        (DivisorRegularImage.Constructions.affineDivisorGraph_regularImage V W a g j hs d f z U hU)).regularComplementInclusion) =
      Set.range (EtaleLocalGraph.Constructions.localGraph (NormalizationDivisor.Open.Constructions.Etale.coverMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) (NormalizationDivisor.Analytic.Constructions.targetAmbientMap V W (Open.PrimeSupport.Constructions.ambientPrime a z)) U
        (NormalizationDivisor.AffineCoordinates.Constructions.coverAffineCoordinates V W (Open.PrimeSupport.Constructions.ambientPrime a z) U a hcover f)) :=
  (SchemeDivisor.GraphImage.Constructions.divisorOpenImmersion_fullGraphImage j d g f z q hq U hUJ
    (DivisorRegularImage.Constructions.affineDivisorGraph_regularImage V W a g j hs d f z U hU)).trans
      ((PrimeGraphRange.Constructions.affinePrimeGraphImage_eq_fullSupportGraph V W a g j hs z f U).symm.trans
        (NormalizationDivisor.AffineGraphRange.Constructions.coverAffineGraph_range V W (Open.PrimeSupport.Constructions.ambientPrime a z) a f U hcover hU).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.DivisorGraphImage.Constructions
