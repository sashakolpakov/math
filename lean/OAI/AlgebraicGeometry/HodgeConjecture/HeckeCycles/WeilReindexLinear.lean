import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMatrix

/-! # Weil Reindex Linear -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexLinear.CM

noncomputable section

/-! Exact transport of rational linear substitutions, including inverse blocks. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM.Product
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : I ≃ J) {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData J MpR MpF MpA)

def unit (A : (Matrix I I ℚ)ˣ) : (Matrix J J ℚ)ˣ := MatrixUnitsMap.CM.map e (RingHom.id ℚ) A

theorem linear_matrix (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (A : (Matrix I I ℚ)ˣ)
    (hγ : γ.val = Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose) :
    (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e γ).val = Matrix.fromBlocks (unit e A).val 0 0 ((unit e A)⁻¹).val.transpose := by
  change Matrix.reindex (e.sumCongr e) (e.sumCongr e) γ.val = _
  rw [hγ, ReindexMatrix.CM.fromBlocks, ReindexMatrix.CM.zero]
  change Matrix.fromBlocks _ 0 0 _ = Matrix.fromBlocks
    (MatrixUnitsMap.CM.map e (RingHom.id ℚ) A).val 0 0
    ((MatrixUnitsMap.CM.map e (RingHom.id ℚ) A)⁻¹).val.transpose
  rw [ReindexMatrix.CM.unit_val, ReindexMatrix.CM.unit_inv_val, ReindexMatrix.CM.transpose]

theorem rational_linear (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (A : (Matrix I I ℚ)ˣ)
    (hγ : γ.val = Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    ((WeilReindexCovers.CM.adelic e W).action (WeilReindexCovers.CM.Product.rationalSplit e W γ) F).val x =
      F.val ((A.val.transpose.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ)) *ᵥ x) := by
  rw [WeilReindexCovers.CM.adelic_action, Adelic.TestReindex.CM.tests_symm_apply]
  change (W.adelic.action (W.rationalSplit (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e γ)) (Adelic.TestReindex.CM.tests e F)).val
    (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x) = _
  rw [W.rational_linear _ _ (linear_matrix e γ A hγ)]
  have hA : (unit e A).val = ReindexMatrix.CM.matrix e A.val := rfl
  rw [hA, ← ReindexMatrix.CM.transpose, ← ReindexMatrix.CM.map, ReindexMatrix.CM.mulVec,
    Adelic.TestReindex.CM.tests_apply]
  have hx : ∀ y : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ, RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e.symm (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e y) = y := by
    intro y
    funext i
    exact congrArg y (e.symm_apply_apply i)
  rw [hx]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexLinear.CM
