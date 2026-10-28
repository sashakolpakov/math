import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomNormalOpen
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactTopOpenGeneration
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FixedNormalSmoothness

/-! # Compact Thom Top Intrinsic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomTopIntrinsic.Constructions

noncomputable section

/-! The global compact Thom pushforward in source top degree equals the independently defined native Gysin map with the proved local product coefficient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceCompactThomPushforward_top_eq_native :
    CompactThomZero.Constructions.regularSourceCompactThomPushforward Z a ha (2*Z.regularComplexDimension) =
      ModuleCat.ofHom (RegularCompactGysin.Constructions.regularCompactGysin V Z (2*Z.regularComplexDimension) 0 rfl) := by
  apply CompactTopOpenGeneration.Constructions.compactTop_hom_ext_openCover (d := Z.regularComplexDimension) (M := Z.regularAnalyticSpace)
    (fun x => RegularNormalThomStage.Constructions.regularNormalSourceOpen Z x (Z.regularFixedNormalPair x))
    (fun x => ⟨x, (Z.regularFixedNormalPair x).point_mem_neighborhood⟩)
  intro x
  rw [CompactThomNormalOpen.Constructions.regularSourceCompactThomPushforward_normal_open Z a ha x (Z.regularFixedNormalPair x)
    (Z.regularFixedNormalPair_ambientChart_mdifferentiable x)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact (RegularCompactGysin.Constructions.regularCompactGysin_local V Z x (Z.regularFixedNormalPair x)
    (FixedNormalSmoothness.Constructions.regularFixedNormalPair_contMDiffOn Z x) (FixedNormalSmoothness.Constructions.regularFixedNormalPair_symm_contMDiffOn Z x)
    (2*Z.regularComplexDimension) 0 rfl b).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomTopIntrinsic.Constructions
