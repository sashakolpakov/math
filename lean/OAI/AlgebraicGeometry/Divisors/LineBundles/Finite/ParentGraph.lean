import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.GraphDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.PrimeGraphRange
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphSmallerFibers
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction

/-! # Parent Graph -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraph.BundleCycles

noncomputable section

section

/-! The actual polynomial graph of a smooth finite source in product coordinates, together with its dimension and closed embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.GraphEmbedding.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialGraphDimension.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphSmallerFibers.Constructions

variable {S N X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] [IsIntegral X.left] [Smooth X.hom]
  (k : S ⟶ N) (a : X ⟶ S)

def finiteParentGraphBase : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a

theorem finiteParentGraphBase_analytic :
    ContMDiff 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) ω (finiteParentGraphBase k a) :=
  (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map k ω).comp (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ω)

variable [IsAffine X.left] (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) {d : ℕ}
  (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

local instance (priority := low) finiteParentGraphCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)

abbrev finiteParentGraph := CycleClass.Thom.RestrictedGraphSmallerFibers.Constructions.firstGraph (finiteParentGraphBase k a) (finiteParentGraphBase_analytic k a)
  (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) U

theorem finiteParentGraph_analytic :
    ContMDiff 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (finiteParentGraph k a U f) :=
  CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedGraph_analytic (finiteParentGraphBase k a) (finiteParentGraphBase_analytic k a) U
    (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f)

theorem finiteParentGraph_differential_injective (hf : Function.Surjective f)
    (x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (finiteParentGraphBase k a) (finiteParentGraphBase_analytic k a) U) :
    Function.Injective (mfderiv 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ))
      (finiteParentGraph k a U f) x) :=
  CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (finiteParentGraphBase k a) (finiteParentGraphBase_analytic k a) U
    (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf) x

theorem finiteParentGraph_closed [T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding (finiteParentGraph k a U f) :=
  CycleClass.Thom.GraphBaseRestriction.Constructions.restrictedGraph_closedEmbedding (finiteParentGraphBase k a) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) U
    (CycleClass.Thom.Closed.GraphEmbedding.Constructions.graph_closedEmbedding (finiteParentGraphBase k a) (finiteParentGraphBase_analytic k a).continuous
      (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_closedEmbedding f hf))

variable [IsOpenImmersion a.left] (p : ℕ)
  (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p = Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

include a hp in
omit [Smooth N.hom] [IsAffine X.left] in
theorem finiteParentGraph_modelDimension :
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) + (p + d) =
      Module.finrank ℂ ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) := by
  simp only [Module.finrank_prod, Module.finrank_fin_fun]
  have hs := CycleClass.Thom.PolynomialGraphDimension.Constructions.openMap_nativeDimension X a
  omega

include a hp in
omit [Smooth N.hom] [IsAffine X.left] in
theorem finiteParentGraph_codimension : CycleClass.Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension
    (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) = p + d := by
  have h := finiteParentGraph_modelDimension a (d := d) p hp
  change Module.finrank ℂ ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) -
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) = p + d
  omega

end

/-! The actual parent closed graph has the same image in product coordinates as the finite parent polynomial graph. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ S) [IsOpenImmersion a.left]
  (g : X ⟶ Y) (j : Y ⟶ N) [IsOpenImmersion j.left]
  (hs : a ≫ k = g ≫ j)
  (d : ℕ) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

include hs in
omit [IsOpenImmersion a.left] in
omit [IsFinite (Over.Hom.left k)] in
theorem finiteParentGraph_image :
    Set.range (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ ∘
      CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f))
        (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (CycleClass.Thom.Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) ω) (CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U)) =
      Set.range (finiteParentGraph k a U f) := by
  have hi := CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic.restrictedGraphImage_range j d U hUJ g f (id : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  have hb : CycleClass.Thom.IntrinsicGraphImageRestriction.Constructions.Intrinsic.graphBase j g (id : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) = finiteParentGraphBase k a := by
    funext x
    exact (FiniteAffine.PrimeGraphRange.BundleCycles.finiteAffine_square_point k a g j hs x).symm
  exact hi.trans (congrArg (fun b : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) =>
    Set.range (CycleClass.Thom.GraphBaseRestriction.Constructions.restrictedGraph b (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)))) hb)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraph.BundleCycles
