import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.WholeFibers
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraph

/-! # Parent Open Fibers -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentOpenFibers.BundleCycles

noncomputable section

/-! The actual affine open source contains every retained finite fiber, so its parent graph has the original generic residue degree and injective projected differential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] in
theorem finiteWholeMap_range_subset_support :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k) ⊆ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, hx⟩ := Set.range_eq_univ.mp (WholeSupport.BundleCycles.wholeSupport_analytic_range (S := S)) y
  refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) x, ?_⟩
  have h := congrArg (fun m => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map m x) (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap_inclusion k (WholeSupport.BundleCycles.wholeSchemeSupport S))
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageOverMap k (WholeSupport.BundleCycles.wholeSchemeSupport S))
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))) x).symm.trans
    (h.trans ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient S (WholeSupport.BundleCycles.wholeSchemeSupport S)) k x).trans
      (congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k) hx)))

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ S) [IsOpenImmersion a.left]

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "MS" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ

theorem finiteParentGraphBase_good_differential_injective (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hx : ParentGraph.BundleCycles.finiteParentGraphBase k a x ∈ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) :
    Function.Injective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ)) (ParentGraph.BundleCycles.finiteParentGraphBase k a) x) := by
  have hd := mfderiv_comp x
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (k) ω).mdifferentiableAt (by simp))
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ω).mdifferentiableAt (by simp))
  exact (congrArg (fun L : MX →L[ℂ] (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ) => Function.Injective L) hd).mpr
    ((WholeFibers.BundleCycles.finiteWholeMap_good_differential_injective k (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) hx).comp
      (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective a x).injective)

omit [IsOpenImmersion a.left] [IsIntegral X.left] [Smooth X.hom] in
omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] in
theorem finiteParentGraphBase_mem_support (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : ParentGraph.BundleCycles.finiteParentGraphBase k a x ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S))) :=
  finiteWholeMap_range_subset_support k ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x, rfl⟩

variable (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) ⁻¹' (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

def finiteParentGraphBase_fiberEquiv (u : U) :
    {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X | ParentGraph.BundleCycles.finiteParentGraphBase k a y = u.val} ≃
      {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (S) |
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) y = u.val} := by
  apply CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction.fiberEquiv_of_commuting_square (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) id (ParentGraph.BundleCycles.finiteParentGraphBase k a) (fun _ => rfl)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion a).injective Function.injective_id u.val
  intro y hy
  apply hcover
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) y ∈ U
  rw [show ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) y = u.val from hy]
  exact u.property

include hcover in
omit [IsIntegral X.left] [Smooth X.hom] in
omit [AlgebraicGeometry.IsIntegral N.left] in
theorem finiteParentGraphBase_genericFiber_card (u : U) (hu : u.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)))) :
    Nat.card {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X | ParentGraph.BundleCycles.finiteParentGraphBase k a y = u.val} = k.left.residueDegree (genericPoint S.left) := by
  obtain ⟨x, hx⟩ := hu
  have h := WholeFibers.BundleCycles.finiteWholeMap_genericFiber_card k x
  rw [hx] at h
  exact (Nat.card_congr (finiteParentGraphBase_fiberEquiv k a U hcover u)).trans h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentOpenFibers.BundleCycles
