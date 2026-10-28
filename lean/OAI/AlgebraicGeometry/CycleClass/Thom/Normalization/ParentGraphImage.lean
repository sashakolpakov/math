import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeGraphRange

/-! # Parent Graph Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions

noncomputable section

/-! The actual parent closed-immersion graph has the same image in the product coordinates as the polynomial normalization graph whose supported projection was computed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.PrimeGraphRange.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev supportCycle (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier) :
    Geometric.DimensionCycles.DimensionCycleSupport V (Geometric.DimensionCycles.dimensionCodimension V W) := ⟨W, rfl⟩

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V W) [IsOpenImmersion a.left]
  (g : X ⟶ Y) (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (hs : a ≫ PrincipalBoundary.Constructions.fullAmbientMap V W = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  (U : Opens V.analyticSpace) (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

include hs in
omit [IsOpenImmersion a.left] in
theorem parentGraph_image :
    Set.range (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ ∘
      GraphOpenImmersion.Constructions.restrictedBase (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f))
        (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ω) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)) =
      Set.range (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph (supportCycle V W) a U f) := by
  have hi := IntrinsicGraphImageRestriction.Constructions.Intrinsic.restrictedGraphImage_range j d U hUJ g f (id : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have hb : IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphBase j g (id : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) = GenericFibers.Constructions.Open.openBase (supportCycle V W) a := by
    funext x
    exact (NormalizationAffine.PrimeGraphRange.Constructions.normalization_square_point V W a g j hs x).symm
  exact hi.trans (congrArg (fun b : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → V.analyticSpace =>
    Set.range (GraphBaseRestriction.Constructions.restrictedGraph b (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (U : Set V.analyticSpace))) hb)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions
