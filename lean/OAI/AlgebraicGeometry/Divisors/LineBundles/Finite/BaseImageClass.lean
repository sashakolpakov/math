import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraphProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport

/-! # Base Image Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BaseImageClass.BundleCycles

noncomputable section

/-! The canonical finite parent image class on an ambient open, with a literal image-support presentation for supported intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Projection.TargetSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))

def finiteParentBaseSupport : Set U :=
  (Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)))

def finiteBaseImage : finiteParentBaseSupport k U → U := Subtype.val

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] [IsFinite (Over.Hom.left k)] in
theorem finiteBaseImage_range : Set.range (finiteBaseImage k U) = finiteParentBaseSupport k U := Subtype.range_coe

def finiteBaseImageCycleClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (Set.range (finiteBaseImage k U))ᶜ (2 * p) :=
  CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport (TopCat.of U) (congrArg Set.compl (finiteBaseImage_range k U).symm) rfl
    (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))))ᶜ U (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) p (ParentGraphProjection.BundleCycles.finiteWholeImage_codimension k p hp)))

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] [IsFinite (Over.Hom.left k)] in
theorem finiteBaseImage_openComplement : IsOpen (Set.range (finiteBaseImage k U))ᶜ := by
  rw [finiteBaseImage_range]
  exact ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)))).isClosed_range.preimage continuous_subtype_val).isOpen_compl

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  (a : X ⟶ S) [IsOpenImmersion a.left] {d : ℕ}
  (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))
  (K : Set (Fin d → ℂ)) (hb : ∀ x, ParentGraph.BundleCycles.finiteParentGraphBase k a x ∈ U → CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K)

include hb in
omit [IsOpenImmersion (Over.Hom.left a)] in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteGraph_bound_baseImage : Set.range (ParentGraph.BundleCycles.finiteParentGraph k a U f) ⊆ Set.range (finiteBaseImage k U) ×ˢ K := by
  rw [finiteBaseImage_range]
  exact ParentGraphProjection.BundleCycles.finiteParentGraph_bound k a U f K hb

local instance finiteBaseImageMetrizable : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteBaseImageCharted : ChartedSpace
    ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (U × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) U (Fin d → ℂ) (Fin d → ℂ)
local instance finiteBaseImageManifold : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (U × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

theorem finitePolynomialGraph_project_baseImage (hf : Function.Surjective f) (hK : IsCompact K)
    (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a)) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U) (Set.range (finiteBaseImage k U)) K hK
      (Set.range (ParentGraph.BundleCycles.finiteParentGraph k a U f)) (finiteGraph_bound_baseImage k U a f K hb)
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U) =
      (k.left.residueDegree (genericPoint S.left) : ℚ) • finiteBaseImageCycleClass k p hp U := by
  have h := ParentGraphProjection.BundleCycles.finiteParentGraph_project_cycleClass k p hp a U hcover f hf K hK hb
  have ht := CycleClass.Thom.Projection.TargetSupport.Constructions.projectAt_targetCast d (TopCat.of U) (finiteParentBaseSupport k U) (Set.range (finiteBaseImage k U))
    (finiteBaseImage_range k U).symm K hK (Set.range (ParentGraph.BundleCycles.finiteParentGraph k a U f))
    (ParentGraphProjection.BundleCycles.finiteParentGraph_bound k a U f K hb) (finiteGraph_bound_baseImage k U a f K hb)
    (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm (ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U)
  have hh := congrArg (eqToHom (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Aᶜ (2 * p)) (finiteBaseImage_range k U).symm)) h
  exact ht.symm.trans (hh.trans (map_smul _ _ _))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.BaseImageClass.BundleCycles
