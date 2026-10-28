import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionImageIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedImageSupportChange

/-! # Graph Section Cup -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions

noncomputable section

/-! The actual normalization graph intersected with an actual affine
regular section projects to cup multiplication by the original parent
cycle class in the original cycle-section intersection support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.OpenGraph.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphEquationSupport.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionImageIntersection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProjectedImageSupportChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Opens V.analyticSpace)

theorem baseImage_openComplement : IsOpen (Set.range (BaseImage.Constructions.Class.baseImage D U))ᶜ := by
  rw [BaseImage.Constructions.Class.baseImage_range]
  exact (D.isClosedEmbedding_analyticInclusion.isClosed_range.preimage continuous_subtype_val).isOpen_compl

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  [IsIntegral Y.left] [Smooth Y.hom] [IsAffine Y.left]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V D.val) [IsOpenImmersion a.left]
  (j : Y ⟶ V.toOver) [IsOpenImmersion j.left]
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
  (s : Γ(Y.left, ⊤)) {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  (K : Set (Fin d → ℂ)) (hb : ∀ x, GenericFibers.Constructions.Open.openBase D a x ∈ U → Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K)

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientOpen j d U) (OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphAmbientOpen.Constructions.Intrinsic.graphAmbientHomeomorph j d U hUJ)
local notation "πU" => TopCat.prodFst (X := TopCat.of U) (Y := TopCat.of (Fin d → ℂ))
local notation "uG" => OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph D a U f
local notation "vOld" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage F (OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s)
local notation "vBase" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hUJ s
local notation "vNew" => OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage πU vBase
local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage D U) ∩ Set.range vBase

omit [IsOpenImmersion a.left] in
include hb in
theorem graphSection_bound_baseImage : Set.range uG ∩ Set.range vOld ⊆ S ×ˢ K := by
  rw [BaseImage.Constructions.Class.baseImage_range]
  exact NormalizationAffine.SectionSupport.Constructions.sectionGraph_intersection_bound D a j U hUJ s f K hb

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) : ChartedSpace (V.analyticModel × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace V.analyticModel U (Fin d → ℂ) (Fin d → ℂ)
local instance : IsManifold 𝓘(ℂ, V.analyticModel × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  Product.Immersion.Constructions.productModel_isManifold

def normalizationGraphThom (hf : Function.Surjective f) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (U × (Fin d → ℂ))) (Set.range uG)ᶜ (2 * (p + d)) :=
  Degree.Constructions.ThomClass.complexThomClassInDegree uG
    (OpenGraph.Constructions.Class.normalizationOpenGraph_analytic D a U (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f))
    (GraphOpenImmersion.Constructions.restrictedGraph_differential_injective (GenericFibers.Constructions.Open.openBase D a) (GenericFibers.Constructions.Open.openBase_analytic D a) U
      (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) (Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_differential_injective f hf))
    (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed D a U f hf) (p + d) (GenericFibers.Constructions.Open.openGraph_codimension D a d)

theorem graphSectionCup_project (hf : Function.Surjective f) (hK : IsCompact K)
    (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ⁻¹' (U : Set V.analyticSpace) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)) :
    Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) S K hK (Set.range uG ∩ Set.range vOld)
      (graphSection_bound_baseImage D U a j hUJ s f K hb) (2 * (p + 1)) (2 * ((p + d) + 1)) (by omega)
      (ImageIntersectionCup.Constructions.imageIntersectionCup uG vOld
        (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed D a U f hf).isClosed_range.isOpen_compl
        (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement F (Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s) (Affine.GraphSectionEquation.Constructions.graphSectionZeroImage_openComplement Y d s))
        (p + d) 1 (normalizationGraphThom D U a f hf) (IntrinsicGraphSection.Constructions.IntrinsicClass.graphSectionClass j d U hUJ s)) =
    ImageIntersectionCup.Constructions.imageIntersectionCup (BaseImage.Constructions.Class.baseImage D U) vBase (baseImage_openComplement D U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s))
      p 1 (BaseImage.Constructions.Class.baseImageCycleClass D U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s) := by
  have hnew := Supported.ProjectionImageIntersection.Constructions.imageIntersectionBound (TopCat.of U) uG (BaseImage.Constructions.Class.baseImage D U) vBase K (BaseImage.Constructions.Class.graph_bound_baseImage D U a f K hb)
  have hz := ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hUJ) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s)
  have hi := ProjectedImageSupportChange.Constructions.projectAt_secondImage_change d (TopCat.of U) uG vOld vNew
    (IntrinsicGraphEquationSupport.Constructions.Intrinsic.graphEquationSupport_range j d U hUJ (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s))
    (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed D a U f hf).isClosed_range.isOpen_compl
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement F (Affine.GraphSectionEquation.Constructions.graphSectionZeroImage Y d s) (Affine.GraphSectionEquation.Constructions.graphSectionZeroImage_openComplement Y d s))
    (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement πU vBase hz) S K hK
    (graphSection_bound_baseImage D U a j hUJ s f K hb) hnew (p + d) 1 (2 * (p + 1)) (by omega)
    (normalizationGraphThom D U a f hf) (IntrinsicGraphSection.Constructions.IntrinsicClass.graphSectionClass j d U hUJ s)
  rw [IntrinsicGraphSection.Constructions.IntrinsicClass.graphSectionClass_productPullback] at hi
  have hp := Supported.ProjectionImageIntersection.Constructions.projectAt_imageIntersectionCup d (TopCat.of U) uG (BaseImage.Constructions.Class.baseImage D U) vBase
    (PolynomialNormalizationGraph.Constructions.Class.polynomialNormalizationGraph_closed D a U f hf).isClosed_range.isOpen_compl (baseImage_openComplement D U) hz
    K hK (BaseImage.Constructions.Class.graph_bound_baseImage D U a f K hb) p 1 (normalizationGraphThom D U a f hf) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hUJ s)
  have hc := BaseImage.Constructions.Class.polynomialGraph_project_baseImage D U a f K hb hf hK hcover
  change Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (BaseImage.Constructions.Class.baseImage D U)) K hK (Set.range uG)
    (BaseImage.Constructions.Class.graph_bound_baseImage D U a f K hb) (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
    (normalizationGraphThom D U a f hf) = BaseImage.Constructions.Class.baseImageCycleClass D U at hc
  rw [hc] at hp
  exact hi.trans hp

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions
