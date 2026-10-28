import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement

/-! # Intrinsic Graph Base Projection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic

noncomputable section

/-! The first-coordinate projection of the actual polynomial graph ambient
commutes with the actual product coordinates on an ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine Y.left] (d : ℕ)

def graphBaseProjection : TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
    (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (Γ(Y.left, ⊤) ⊗[ℂ] MvPolynomial (Fin d) ℂ))) ⟶ TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
  TopCat.ofHom ⟨fun x => (Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d x).1,
    continuous_fst.comp (Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph Y d).continuous⟩

theorem graphBaseProjection_graph {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left]
    (g : X ⟶ Y) (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤)) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    graphBaseProjection Y d (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Affine.SchemeGraph.Constructions.globalGraphSchemeMap g f) x) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x :=
  congrArg (Prod.fst : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y × (Fin d → ℂ) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (Affine.SchemeGraphAnalytic.Constructions.IntrinsicAmbient.nativeGraphHomeomorph_graph Y d g f x)

variable {Y} [IsIntegral Y.left] [Smooth Y.hom]
  {N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral N.left] [Smooth N.hom]
  (j : Y ⟶ N) [IsOpenImmersion j.left] (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

def baseOpenLift : TopCat.of U ⟶ TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
  TopCat.ofHom ⟨fun x => ((Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j) U hU).symm x).val,
    continuous_subtype_val.comp (Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
      (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j) U hU).symm.continuous⟩

omit [IsAffine Y.left] in
theorem baseOpenLift_commutes (x : U) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (baseOpenLift j U hU x) = x.val := by
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j
    (((Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j) U hU).symm x).val) = x.val
  have h := Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph_val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j) U hU
    ((Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j) U hU).symm x)
  simpa only [Homeomorph.apply_symm_apply] using h.symm

theorem graphBaseProjection_coordinate_square :
    Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU) ≫ graphBaseProjection Y d =
      (TopCat.prodFst (X := TopCat.of U) (Y := TopCat.of (Fin d → ℂ))) ≫ baseOpenLift j U hU := by
  ext x : 1
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j).injective
  change (IntrinsicGraphAmbientEmbedding.Constructions.Intrinsic.graphAmbientMap j d (Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU) x)).1 =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (baseOpenLift j U hU x.1)
  have h := IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph_base j d U hU ((IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hU).symm x)
  simp only [Homeomorph.apply_symm_apply] at h
  exact h.symm.trans (baseOpenLift_commutes j U hU x.1).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
