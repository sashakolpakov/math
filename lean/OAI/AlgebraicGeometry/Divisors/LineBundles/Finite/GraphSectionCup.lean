import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionImageIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedImageSupportChange

/-! # Graph Section Cup -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GraphSectionCup.BundleCycles

noncomputable section

/-! Intersecting the actual parent graph with a base regular section projects to the canonical image class times the section class, with the original generic residue degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionImageIntersection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedImageSupportChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ S) [IsOpenImmersion a.left]
  (j : Y ⟶ N) [IsOpenImmersion j.left]
  (hUJ : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (s : Γ(Y.left, ⊤)) {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  (K : Set (Fin d → ℂ)) (hb : ∀ x, ParentGraph.BundleCycles.finiteParentGraphBase k a x ∈ U → CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K)

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ)
local notation "πU" => TopCat.prodFst (X := TopCat.of U) (Y := TopCat.of (Fin d → ℂ))
local notation "uG" => OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraph.BundleCycles.finiteParentGraph k a U f
local notation "vOld" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage F (OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s)
local notation "vBase" => OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionSupport.BundleCycles.finiteBaseSectionImage j U hUJ s
local notation "vNew" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage πU vBase
local notation "T" => Set.range (OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BaseImageClass.BundleCycles.finiteBaseImage k U) ∩ Set.range vBase

omit [IsOpenImmersion a.left] in
include hb in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteGraphSection_bound_baseImage : Set.range uG ∩ Set.range vOld ⊆ T ×ˢ K := by
  rw [BaseImageClass.BundleCycles.finiteBaseImage_range]
  exact SectionSupport.BundleCycles.finiteSectionGraph_intersection_bound k a j U hUJ s f K hb

local instance finiteGraphSectionCupMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteGraphSectionCupCharted : ChartedSpace ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteGraphSectionCupManifold : IsManifold 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

theorem finiteGraphSectionCup_project (hf : Function.Surjective f) (hK : IsCompact K)
    (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) T K hK (Set.range uG ∩ Set.range vOld)
      (finiteGraphSection_bound_baseImage k U a j hUJ s f K hb) (2 * (p + 1)) (2 * ((p + d) + 1)) (by omega)
      (CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup uG vOld
        (ParentGraph.BundleCycles.finiteParentGraph_closed k a U f hf).isClosed_range.isOpen_compl
        (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement F (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s) (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage_openComplement Y d s))
        (p + d) 1 (ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U) (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.graphSectionClass j d U hUJ s)) =
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (BaseImageClass.BundleCycles.finiteBaseImage k U) vBase (BaseImageClass.BundleCycles.finiteBaseImage_openComplement k U)
      (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s))
      p 1 ((k.left.residueDegree (genericPoint S.left) : ℚ) • BaseImageClass.BundleCycles.finiteBaseImageCycleClass k p hp U) (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) := by
  have hnew := CycleClass.Thom.Supported.ProjectionImageIntersection.Constructions.imageIntersectionBound (TopCat.of U) uG (BaseImageClass.BundleCycles.finiteBaseImage k U) vBase K (BaseImageClass.BundleCycles.finiteGraph_bound_baseImage k U a f K hb)
  have hz := CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s)
  have hi := CycleClass.Thom.ProjectedImageSupportChange.Constructions.projectAt_secondImage_change d (TopCat.of U) uG vOld vNew
    (CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic.graphEquationSupport_range j d U hUJ (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s))
    (ParentGraph.BundleCycles.finiteParentGraph_closed k a U f hf).isClosed_range.isOpen_compl
    (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement F (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s) (CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage_openComplement Y d s))
    (CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement πU vBase hz) T K hK
    (finiteGraphSection_bound_baseImage k U a j hUJ s f K hb) hnew (p + d) 1 (2 * (p + 1)) (by omega)
    (ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U) (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.graphSectionClass j d U hUJ s)
  rw [CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.graphSectionClass_productPullback] at hi
  have hproj := CycleClass.Thom.Supported.ProjectionImageIntersection.Constructions.projectAt_imageIntersectionCup d (TopCat.of U) uG (BaseImageClass.BundleCycles.finiteBaseImage k U) vBase
    (ParentGraph.BundleCycles.finiteParentGraph_closed k a U f hf).isClosed_range.isOpen_compl (BaseImageClass.BundleCycles.finiteBaseImage_openComplement k U) hz
    K hK (BaseImageClass.BundleCycles.finiteGraph_bound_baseImage k U a f K hb) p 1 (ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U) (CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s)
  have hc := BaseImageClass.BundleCycles.finitePolynomialGraph_project_baseImage k p hp U a f K hb hf hK hcover
  change CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (BaseImageClass.BundleCycles.finiteBaseImage k U)) K hK (Set.range uG)
    (BaseImageClass.BundleCycles.finiteGraph_bound_baseImage k U a f K hb) (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
    (ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U) = (k.left.residueDegree (genericPoint S.left) : ℚ) • BaseImageClass.BundleCycles.finiteBaseImageCycleClass k p hp U at hc
  rw [hc] at hproj
  exact hi.trans hproj

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GraphSectionCup.BundleCycles
