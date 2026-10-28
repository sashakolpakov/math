import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductProjections
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Stratum Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.StratumIso.BundleCycles

noncomputable section

/-! The native smooth stratum of a smooth complex scheme is the whole
scheme, through an actual isomorphism and its holomorphic point map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom]

theorem smoothStratumInclusion_isIso : IsIso (CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom) := by
  apply (isIso_iff_isOpenImmersion_and_surjective (CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom)).mpr
  refine ⟨inferInstance, (surjective_iff (CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom)).mpr ?_⟩
  intro x
  change x ∈ Set.range (CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom)
  rw [CycleClass.Geometric.SmoothStratum.range_smoothStratumι, Scheme.Hom.smoothLocus_eq_top]
  trivial

def smoothStratumOverIso : CycleClass.Thom.Regular.ProductOver.Constructions.regularOver X ≅ X := by
  letI : IsIso (CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom) := smoothStratumInclusion_isIso X
  let e : CycleClass.Geometric.SmoothStratum.smoothStratum X.hom ≅ X.left := asIso (CycleClass.Geometric.SmoothStratum.smoothStratumι X.hom)
  exact Over.isoMk e rfl

def smoothStratumPointsHomeomorph : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Regular.ProductOver.Constructions.regularOver X) ≃ₜ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (smoothStratumOverIso X)

theorem smoothStratumPointsHomeomorph_apply (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Regular.ProductOver.Constructions.regularOver X)) :
    smoothStratumPointsHomeomorph X x = x ≫ CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion X := rfl

variable [IsIntegral X.left]

theorem smoothStratumPointsHomeomorph_contMDiff (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Regular.ProductOver.Constructions.regularOver X).hom) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) r
      (smoothStratumPointsHomeomorph X) :=
  ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (smoothStratumOverIso X).hom r

theorem smoothStratumPointsHomeomorph_symm_contMDiff (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
      𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (CycleClass.Thom.Regular.ProductOver.Constructions.regularOver X).hom) → ℂ) r
      (smoothStratumPointsHomeomorph X).symm :=
  ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (smoothStratumOverIso X).inv r

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.StratumIso.BundleCycles
