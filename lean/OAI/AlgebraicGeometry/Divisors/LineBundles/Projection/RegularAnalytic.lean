import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularInv
import OAI.AlgebraicGeometry.Divisors.LineBundles.ThomProjection

/-! # Regular Analytic -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularAnalytic.BundleCycles

noncomputable section

/-! The exact regular ambient product identification is holomorphic in
both directions for the native complex manifold structures. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductMaps.Constructions
open scoped _root_.Manifold ContDiff

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] (B : IrreducibleCloseds Y.left)
    (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom]
    (πX : Z ⟶ X) (πY : Z ⟶ Y) (hprod : IsLimit (BinaryFan.mk πX πY))

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Z C
local notation "H" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B
local notation "F" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ
local notation "K" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Z.hom) → ℂ
local notation "e" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularInv.BundleCycles.projectionRegularAmbientHomeomorph X Y B Z πX πY hprod

local instance (priority := low) : ChartedSpace (F × E) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × H) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModelCharted _ _ _ _
local instance (priority := low) : ChartedSpace (F × E) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
  CycleClass.Thom.Product.Immersion.Constructions.productModelCharted _ _ _ _

theorem projectionRegularAmbientHomeomorph_contMDiff (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, K) (𝓘(ℂ, F).prod 𝓘(ℂ, E)) r e := by
  apply ContMDiff.prodMk
  · exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map πX r).comp (contMDiff_subtype_val («U» := G) (n := r))
  · apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff H _ r).mp
    exact (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map πY r).comp (contMDiff_subtype_val («U» := G) (n := r))

theorem projectionRegularAmbientHomeomorph_symm_contMDiff (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, F).prod 𝓘(ℂ, E)) 𝓘(ℂ, K) r (e).symm := by
  rw [← modelWithCornersSelf_prod]
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff G (e).symm r).mp
  rw [modelWithCornersSelf_prod]
  exact (CycleClass.Thom.AnalyticProductMaps.Constructions.productPresentationPointsHomeomorph_symm_contMDiff πX πY hprod r).comp
    ((contMDiff_id (I := 𝓘(ℂ, F))).prodMap (contMDiff_subtype_val («U» := H) (n := r)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularAnalytic.BundleCycles
