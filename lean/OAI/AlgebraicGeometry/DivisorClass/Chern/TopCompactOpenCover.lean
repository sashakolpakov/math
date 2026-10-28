import OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroHomologyOpenCover
import OAI.AlgebraicTopology.Duality.Poincare.Manifold

/-! # Top Compact Open Cover -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TopCompactOpenCover

noncomputable section

/-! Genuine open extensions from any open cover determine a linear map on top compact cohomology. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.Manifold
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem topCompactCohomology_openCover_hom_ext {I : Type*} (U : I → Opens M)
    (hU : ∀ x : M, ∃ i, x ∈ U i) {N : ModuleCat.{0} ℚ}
    {f g : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2*d) ⟶ N}
    (h : ∀ i, AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) (U i) (2*d) ≫ f =
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) (U i) (2*d) ≫ g) : f = g := by
  let e := AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := M) (2*d) 0 rfl
  apply (cancel_epi e.inv).1
  apply ZeroHomologyOpenCover.rationalH0_openCover_hom_ext (TopCat.of M) U hU
  intro i
  let eU := AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := U i) (2*d) 0 rfl
  apply (cancel_epi eU.hom).1
  have hc := AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality.complexManifoldCompactSupportCap_open d (U i) (2*d) 0 rfl
  change AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) (U i) (2*d) ≫ e.hom =
    eU.hom ≫ AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U i : Set M)) 0 at hc
  rw [← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id_assoc,
    ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id_assoc]
  exact h i

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TopCompactOpenCover
