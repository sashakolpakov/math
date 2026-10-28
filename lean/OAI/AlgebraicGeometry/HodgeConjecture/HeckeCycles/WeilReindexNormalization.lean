import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReindexMatrix

/-! # Weil Reindex Normalization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexNormalization.CM

noncomputable section

/-! The actual Gaussian and its determinant normalization survive coordinate relabeling. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexCovers.CM
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : I ≃ J)

theorem basePeriod_matrix : ReindexMatrix.CM.matrix e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod I).val = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod J).val := by
  apply Matrix.ext
  intro i j
  change Matrix.diagonal (fun _ : I => Complex.I) (e.symm i) (e.symm j) =
    Matrix.diagonal (fun _ : J => Complex.I) i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
  · have he : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    simp only [Matrix.diagonal_apply_ne _ he, Matrix.diagonal_apply_ne _ hij]

theorem denominator_matrix (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℝ) :
    ReindexMatrix.CM.matrix e ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g).complexify.denominator (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod I).val) =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e g)).complexify.denominator (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod J).val := by
  change ReindexMatrix.CM.matrix e
    (g.val.toBlocks₂₁.map (algebraMap ℝ ℂ) * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod I).val + g.val.toBlocks₂₂.map (algebraMap ℝ ℂ)) = _
  rw [ReindexMatrix.CM.add, ReindexMatrix.CM.mul, basePeriod_matrix]
  rfl

theorem denominator_det (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℝ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex e g)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod J) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks g) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod I) := by
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet
  rw [← denominator_matrix]
  exact Matrix.det_reindex_self e _

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData J MpR MpF MpA)

def vacuum : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I := (HeckeCycles.Real.TestReindex.CM.tests e).symm W.vacuum

omit [DecidableEq I] in
theorem vacuum_eq (x : I → ℝ) : (CM.vacuum e W).val x =
    Complex.exp (-((Real.pi : ℂ) * ∑ i, (x i : ℂ) ^ 2)) := by
  change W.vacuum.val (RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x) = _
  rw [W.vacuum_eq]
  have hs : (∑ j : J, ((RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.positionReindex e x j : ℝ) : ℂ) ^ 2) = ∑ i : I, (x i : ℂ) ^ 2 :=
    e.symm.sum_comp (fun i => (x i : ℂ) ^ 2)
  rw [hs]

theorem real_normalization (r : MpR) :
    (((WeilReindexCovers.CM.real e W).action r (CM.vacuum e W)).val 0) ^ 2 =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks ((WeilReindexCovers.CM.real e W).project r)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.basePeriod I))⁻¹ := by
  rw [WeilReindexCovers.CM.real_action]
  change (((HeckeCycles.Real.TestReindex.CM.tests e).symm
    (W.real.action r (HeckeCycles.Real.TestReindex.CM.tests e ((HeckeCycles.Real.TestReindex.CM.tests e).symm W.vacuum)))).val 0) ^ 2 = _
  rw [LinearEquiv.apply_symm_apply, HeckeCycles.Real.TestReindex.CM.tests_symm_apply]
  change ((W.real.action r W.vacuum).val 0) ^ 2 = _
  rw [W.real_normalization, WeilReindexCovers.CM.real_projection, denominator_det]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.WeilReindexNormalization.CM
