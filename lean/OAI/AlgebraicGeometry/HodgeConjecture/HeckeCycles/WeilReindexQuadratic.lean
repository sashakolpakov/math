import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMatrix

/-! # Weil Reindex Quadratic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexQuadratic.CM

noncomputable section

/-! Exact transport of the rational quadratic multiplier. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM.Product
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : I ≃ J) {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData J MpR MpF MpA)

theorem quadratic_matrix (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (B : Matrix I I ℚ)
    (hγ : γ.val = Matrix.fromBlocks 1 B 0 1) :
    (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e γ).val = Matrix.fromBlocks 1 (ReindexMatrix.CM.matrix e B) 0 1 := by
  change Matrix.reindex (e.sumCongr e) (e.sumCongr e) γ.val = _
  rw [hγ, ReindexMatrix.CM.fromBlocks, ReindexMatrix.CM.one, ReindexMatrix.CM.zero]

theorem rational_quadratic (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (B : Matrix I I ℚ)
    (hB : B.IsSymm) (hγ : γ.val = Matrix.fromBlocks 1 B 0 1)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    ((WeilReindexCovers.CM.adelic e W).action (WeilReindexCovers.CM.Product.rationalSplit e W γ) F).val x =
      W.character (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ (1 / 2) * (x ⬝ᵥ (B.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) *ᵥ x))) * F.val x := by
  rw [WeilReindexCovers.CM.adelic_action, Adelic.TestReindex.CM.tests_symm_apply]
  change (W.adelic.action (W.rationalSplit (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e γ)) (Adelic.TestReindex.CM.tests e F)).val
    (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x) = _
  rw [W.rational_quadratic _ _ (ReindexMatrix.CM.isSymm e B hB) (quadratic_matrix e γ B hγ),
    ← ReindexMatrix.CM.map, ReindexMatrix.CM.mulVec, RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex_dot]
  have hx : (Adelic.TestReindex.CM.tests e F).val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x) = F.val x := by
    change F.val (fun i => x (e.symm (e i))) = F.val x
    simp only [e.symm_apply_apply]
  rw [hx]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexQuadratic.CM
