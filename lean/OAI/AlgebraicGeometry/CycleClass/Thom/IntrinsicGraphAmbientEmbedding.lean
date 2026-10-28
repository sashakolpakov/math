import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.OpenEmbedding
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Intrinsic Graph Ambient Embedding -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic

noncomputable section

/-! The genuine polynomial graph ambient of an affine open subscheme embeds holomorphically as the corresponding open part of the original ambient product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
open scoped TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.OpenEmbedding.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine Y.left] [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left] (d : ℕ)

local notation "MY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ
local notation "MN" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ

local instance (priority := low) : ChartedSpace (MY × (Fin d → ℂ)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y × (Fin d → ℂ)) :=
  prodChartedSpace MY (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (Fin d → ℂ) (Fin d → ℂ)
local instance (priority := low) : ChartedSpace (MN × (Fin d → ℂ)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N × (Fin d → ℂ)) :=
  prodChartedSpace MN (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) (Fin d → ℂ) (Fin d → ℂ)

def graphAmbientMap :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin d) ℂ)) →
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N × (Fin d → ℂ) :=
  Prod.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) id ∘ Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d

omit [IsOpenImmersion j.left] in
theorem graphAmbientMap_analytic :
    ContMDiff 𝓘(ℂ, Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphModel Y d) 𝓘(ℂ, MN × (Fin d → ℂ)) ω (graphAmbientMap j d) :=
  (Product.OpenEmbedding.Constructions.productMap_analytic (F := Fin d → ℂ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω)).comp
    (Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph_analytic Y d)

omit [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral N.left] [Smooth N.hom] in
theorem graphAmbientMap_openEmbedding : Topology.IsOpenEmbedding (graphAmbientMap j d) :=
  ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j).prodMap Topology.IsOpenEmbedding.id).comp
    (Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d).isOpenEmbedding

theorem graphAmbientMap_mfderiv_bijective
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin d) ℂ))) :
    Function.Bijective (mfderiv 𝓘(ℂ, Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphModel Y d) 𝓘(ℂ, MN × (Fin d → ℂ)) (graphAmbientMap j d) x) := by
  have hp := Product.OpenEmbedding.Constructions.productMap_analytic (F := Fin d → ℂ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω)
  have hd := mfderiv_comp x (hp.mdifferentiableAt (by simp))
    ((Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph_analytic Y d).mdifferentiableAt (by simp))
  exact (congrArg (fun L : Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphModel Y d →L[ℂ] (MN × (Fin d → ℂ)) => Function.Bijective L) hd).mpr
    ((Product.OpenEmbedding.Constructions.productMap_mfderiv_bijective (F := Fin d → ℂ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
      (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω) (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective j) _).comp
        (HolomorphicHomeomorph.Constructions.homeomorph_mfderiv_bijective (Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d)
          ((Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph_analytic Y d).mdifferentiable (by simp))
          ((Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph_symm_analytic Y d).mdifferentiable (by simp)) x))

omit [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral N.left] [Smooth N.hom] [IsOpenImmersion j.left] in
theorem graphAmbientMap_graph {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    (g : X ⟶ Y) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    graphAmbientMap j d (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x) =
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x), Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x) := by
  change Prod.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) id
    (Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x)) = _
  rw [Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph_graph]
  rfl

omit [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral N.left] [Smooth N.hom] [IsOpenImmersion j.left] in
theorem graphAmbientMap_range : Set.range (graphAmbientMap j d) =
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) ×ˢ Set.univ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨(Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d x).1, rfl⟩, Set.mem_univ _⟩
  · rintro ⟨⟨y, hy⟩, _⟩
    refine ⟨(Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d).symm (y, z.2), ?_⟩
    change Prod.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) id
      (Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d ((Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d).symm (y, z.2))) = z
    rw [Homeomorph.apply_symm_apply]
    exact Prod.ext hy rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic
