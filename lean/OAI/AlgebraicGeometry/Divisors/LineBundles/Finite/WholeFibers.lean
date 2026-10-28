import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.WholeSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.OpenChart

/-! # Whole Fibers -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.WholeFibers.BundleCycles

noncomputable section

/-! The actual whole-source finite cover computes every generic analytic fiber and the injective projected differential of the original finite map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension
  (Over.hom (FiniteSupport.Cover.BundleCycles.finiteSupportSourceOver k (WholeSupport.BundleCycles.wholeSchemeSupport S)))) → ℂ
local notation "MS" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ

omit [AlgebraicGeometry.IsIntegral N.left] in
theorem finiteWholeSource_analytic_square :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) =
      CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) :=
  FiniteAffine.OpenChart.BundleCycles.finiteSupportCover_liftBase_eq k (WholeSupport.BundleCycles.wholeSchemeSupport S)

theorem finiteWholeMap_good_differential_injective
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) x ∈ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (WholeSupport.BundleCycles.wholeSchemeSupport S)) :
    Function.Injective (mfderiv 𝓘(ℂ, MS) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k)) x) := by
  have hr : x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S))) := by
    exact WholeSupport.BundleCycles.finiteWholeSourceAmbient_covers k x hx
  obtain ⟨y, rfl⟩ := hr
  have ha := ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) y
  have hf := CycleClass.Thom.EtaleGraphOpenImmersion.Constructions.etaleBase_differential_injective (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) y
  rw [← finiteWholeSource_analytic_square k] at hf
  rw [mfderiv_comp y
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (k) ω).mdifferentiableAt (by simp))
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) ω).mdifferentiableAt (by simp))] at hf
  intro v w hvw
  obtain ⟨a, ha'⟩ := ha.surjective v
  obtain ⟨b, hb'⟩ := ha.surjective w
  have hab : a = b := hf
    ((congrArg (mfderiv 𝓘(ℂ, MS) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) y))
      ha').trans (hvw.trans
        (congrArg (mfderiv 𝓘(ℂ, MS) 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ))
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) y))
          hb').symm))
  exact ha'.symm.trans ((congrArg (mfderiv 𝓘(ℂ, ML) 𝓘(ℂ, MS)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S))) y) hab).trans hb')

def finiteWholeMap_coverFiberEquiv (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (FiniteSupport.Cover.BundleCycles.finiteSupportTargetOver k (WholeSupport.BundleCycles.wholeSchemeSupport S))) :
    {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (FiniteSupport.Cover.BundleCycles.finiteSupportSourceOver k (WholeSupport.BundleCycles.wholeSchemeSupport S)) | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) y = x} ≃
      {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S |
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) y = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) x} := by
  apply CycleClass.Thom.ProperImage.IntrinsicFiberDegree.Constructions.Construction.fiberEquiv_of_commuting_square (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S))) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportCoverMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)))
    (congrFun (finiteWholeSource_analytic_square k))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S))).injective
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S))).injective x
  intro y hy
  apply WholeSupport.BundleCycles.finiteWholeSourceAmbient_covers k y
  rw [show ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) y =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) x from hy]
  exact WholeSupport.BundleCycles.finiteSupportTargetAmbientMap_mem_retained k (WholeSupport.BundleCycles.wholeSchemeSupport S) x

omit [AlgebraicGeometry.IsIntegral N.left] in
theorem finiteWholeMap_genericFiber_card (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (FiniteSupport.Cover.BundleCycles.finiteSupportTargetOver k (WholeSupport.BundleCycles.wholeSchemeSupport S))) :
    Nat.card {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S |
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (k) y = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k (WholeSupport.BundleCycles.wholeSchemeSupport S)) x} = k.left.residueDegree (genericPoint S.left) := by
  have h := (Nat.card_congr (finiteWholeMap_coverFiberEquiv k x).symm).trans
    (FiniteSupport.Cover.BundleCycles.finiteSupportCover_fiber_degree k (WholeSupport.BundleCycles.wholeSchemeSupport S) x)
  simpa only [WholeSupport.BundleCycles.wholeSchemeSupport, OrderIso.apply_symm_apply] using h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.WholeFibers.BundleCycles
