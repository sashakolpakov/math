import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FourierReindex

/-! # Weil Reindex Fourier -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexFourier.CM

noncomputable section

/-! The transported rational splitting has the exact Fourier normalization. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM.Product
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : I ≃ J) {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData J MpR MpF MpA)

theorem fourier_matrix (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (hγ : γ.val = Matrix.fromBlocks 0 (-1) 1 0) :
    (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e γ).val = Matrix.fromBlocks 0 (-1) 1 0 := by
  apply Matrix.ext
  intro i j
  change γ.val ((e.sumCongr e).symm i) ((e.sumCongr e).symm j) = _
  rw [hγ]
  cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem rational_fourier (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (hγ : γ.val = Matrix.fromBlocks 0 (-1) 1 0)
    (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    ((WeilReindexCovers.CM.adelic e W).action (WeilReindexCovers.CM.Product.rationalSplit e W γ) F).val x =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier W.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (ReindexMeasure.CM.finiteMeasure e W.finiteMeasure)) F.val x := by
  let := W.finiteMeasure_haar
  rw [WeilReindexCovers.CM.adelic_action, Adelic.TestReindex.CM.tests_symm_apply]
  change (W.adelic.action (W.rationalSplit (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e γ)) (Adelic.TestReindex.CM.tests e F)).val
    (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x) = _
  rw [W.rational_fourier _ (fourier_matrix e γ hγ), ReindexMeasure.CM.adelic_map,
    FourierReindex.CM.transform]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexFourier.CM
