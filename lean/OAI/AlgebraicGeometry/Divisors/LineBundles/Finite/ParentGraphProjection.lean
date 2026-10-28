import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentOpenFibers
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentThomCoordinates
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GraphGenericProjection
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.IntrinsicFiniteSurjective

/-! # Parent Graph Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraphProjection.BundleCycles

noncomputable section

/-! A genuine finite parent polynomial graph projects to the canonical supported image class, with its actual generic residue degree, across the singular boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphBaseRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.RestrictedGraphSmallerFibers.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectionDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass
open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.IntrinsicFiniteSurjective.Constructions.Intrinsic

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] [AlgebraicGeometry.IsNoetherian N.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] (k : S ⟶ N) [IsFinite k.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

include hp in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteWholeImage_codimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) N.hom + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom := by
  rw [WholeSupport.BundleCycles.finiteWholeImage_dimension k, Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
  exact hp

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteWholeMap_residueDegree_pos : 0 < k.left.residueDegree (genericPoint S.left) := by
  have h := CycleClass.Thom.Integral.IntrinsicFiniteSurjective.Constructions.Intrinsic.genericResidueDegree_pos (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (WholeSupport.BundleCycles.wholeSchemeSupport S))
    (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap_genericPoint k (WholeSupport.BundleCycles.wholeSchemeSupport S))
  simpa only [FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap_residueDegree, WholeSupport.BundleCycles.wholeSchemeSupport, OrderIso.apply_symm_apply] using h

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom] [IsAffine X.left]
  (a : X ⟶ S) [IsOpenImmersion a.left] (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))
  {d : ℕ} (f : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, ⊤))

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

local instance finiteParentGraphProjectionMetrizable (A : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) : MetrizableSpace A :=
  A.isOpenEmbedding'.isEmbedding.metrizableSpace
local instance (priority := low) finiteParentGraphProjectionCharted (A : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) :
    ChartedSpace ((Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) (A × (Fin d → ℂ)) :=
  prodChartedSpace (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) A (Fin d → ℂ) (Fin d → ℂ)
local instance finiteParentGraphProjectionManifold (A : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) : IsManifold
    𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) × (Fin d → ℂ)) ω (A × (Fin d → ℂ)) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModel_isManifold

abbrev finiteRetainedParentSource := Scheme.GraphGenericProjection.BundleCycles.schemeGraphRetainedSource N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U
  (ParentGraph.BundleCycles.finiteParentGraph k a U f) (ParentGraph.BundleCycles.finiteParentGraph_analytic k a U f)

omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteParentGraph_generic_differential_injective
    (x : finiteRetainedParentSource k a U f) :
    Function.Injective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ))
      (Prod.fst ∘ Scheme.GraphGenericProjection.BundleCycles.schemeGraphRetainedGraph N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U (ParentGraph.BundleCycles.finiteParentGraph k a U f)
        (ParentGraph.BundleCycles.finiteParentGraph_analytic k a U f)) x) := by
  have hd := CycleClass.Thom.RestrictedGraphSmallerFibers.Constructions.doubleGraph_projected_mfderiv (ParentGraph.BundleCycles.finiteParentGraphBase k a) (ParentGraph.BundleCycles.finiteParentGraphBase_analytic k a) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) U
    (Scheme.SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U) inf_le_left x
  exact (congrArg (fun L : MX →L[ℂ] (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) => Function.Injective L) hd).mpr
    (ParentOpenFibers.BundleCycles.finiteParentGraphBase_good_differential_injective k a x.val.val x.property.2)

include hcover in
theorem finiteParentGraph_genericFiber_card
    (x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) ω)
      (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (Scheme.SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U))) :
    Nat.card {y : finiteRetainedParentSource k a U f |
      (Scheme.GraphGenericProjection.BundleCycles.schemeGraphRetainedGraph N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U (ParentGraph.BundleCycles.finiteParentGraph k a U f)
        (ParentGraph.BundleCycles.finiteParentGraph_analytic k a U f) y).1 =
          SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (Scheme.SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U)
            (Scheme.GraphGenericProjection.BundleCycles.schemeGraphRetained_regular N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetOpen_smoothLocus k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U) x} = k.left.residueDegree (genericPoint S.left) := by
  let P := Scheme.SupportGoodOpenMap.BundleCycles.schemeSupportGoodNeighborhood N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U
  let u : P := SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) P
    (Scheme.GraphGenericProjection.BundleCycles.schemeGraphRetained_regular N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetOpen_smoothLocus k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U) x
  have hu : u.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S))) := by
    have hr : u ∈ Set.range (SchemeCycle.RegularOpen.BundleCycles.schemeCycleRegularOpenImmersion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) P
        (Scheme.GraphGenericProjection.BundleCycles.schemeGraphRetained_regular N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetOpen_smoothLocus k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U)) := ⟨x, rfl⟩
    rw [← FiniteSupport.GraphProjection.BundleCycles.finiteSupportTargetAmbientMap_regular_range k (WholeSupport.BundleCycles.wholeSchemeSupport S) P (fun _ hx => hx.2)] at hr
    exact hr
  have hd := CycleClass.Thom.RestrictedGraphSmallerFibers.Constructions.doubleGraph_fiber_card (ParentGraph.BundleCycles.finiteParentGraphBase k a) (ParentGraph.BundleCycles.finiteParentGraphBase_analytic k a) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f) (CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates_analytic f) U P inf_le_left u
  exact hd.trans (ParentOpenFibers.BundleCycles.finiteParentGraphBase_genericFiber_card k a U hcover ⟨u.val, u.property.1⟩ hu)

omit [IsOpenImmersion a.left] in
omit [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteParentGraph_bound (K : Set (Fin d → ℂ))
    (hb : ∀ x, ParentGraph.BundleCycles.finiteParentGraphBase k a x ∈ U → CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K) :
    Set.range (ParentGraph.BundleCycles.finiteParentGraph k a U f) ⊆
      ((Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)))) ×ˢ K := by
  rintro _ ⟨x, rfl⟩
  exact ⟨ParentOpenFibers.BundleCycles.finiteParentGraphBase_mem_support k a x.val, hb x.val x.property⟩

include hcover in
theorem finiteParentGraph_project_cycleClass (hf : Function.Surjective f)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K)
    (hb : ∀ x, ParentGraph.BundleCycles.finiteParentGraphBase k a x ∈ U → CycleClass.Thom.Affine.SchemeGraphAnalytic.Constructions.globalGraphCoordinates f x ∈ K) :
    CycleClass.Thom.Supported.ProjectionDegree.Constructions.projectAt d (TopCat.of U)
      ((Subtype.val : U → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))))
      K hK (Set.range (ParentGraph.BundleCycles.finiteParentGraph k a U f)) (finiteParentGraph_bound k a U f K hb)
      (2 * p) (2 * (p + d)) (Nat.mul_add 2 p d).symm
      (ParentThomCoordinates.BundleCycles.finiteParentGraphThomClass k p hp a d f hf U) =
    (k.left.residueDegree (genericPoint S.left) : ℚ) •
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))))ᶜ U (2 * p)
        (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) p (finiteWholeImage_codimension k p hp)) := by
  have hdeg := finiteParentGraph_genericFiber_card k a U hcover f
  have hfin := fun x => Nat.finite_of_card_ne_zero
    (show Nat.card _ ≠ 0 from (hdeg x).trans_ne (Nat.ne_of_gt (finiteWholeMap_residueDegree_pos k)))
  exact Scheme.GraphGenericProjection.BundleCycles.schemeGraphThom_project_genericCycleClass N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) p
    (finiteWholeImage_codimension k p hp) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S))
    (FiniteSupport.Cover.BundleCycles.finiteSupportTargetOpen_smoothLocus k (WholeSupport.BundleCycles.wholeSchemeSupport S)) U
    (ParentGraph.BundleCycles.finiteParentGraph k a U f) (ParentGraph.BundleCycles.finiteParentGraph_analytic k a U f)
    (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen_spec k (WholeSupport.BundleCycles.wholeSchemeSupport S)).1
    (ParentGraph.BundleCycles.finiteParentGraph_differential_injective k a U f hf) (ParentGraph.BundleCycles.finiteParentGraph_closed k a U f hf)
    (ParentGraph.BundleCycles.finiteParentGraph_codimension a (d := d) p hp) K hK (finiteParentGraph_bound k a U f K hb)
    (finiteParentGraph_generic_differential_injective k a U f) hfin
    (k.left.residueDegree (genericPoint S.left)) hdeg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraphProjection.BundleCycles
