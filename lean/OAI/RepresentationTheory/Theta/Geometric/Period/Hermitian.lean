import OAI.RepresentationTheory.Theta.Geometric.Period.Lattice
import OAI.RepresentationTheory.Theta.Geometric.Reference.Action

/-! # Hermitian -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Positive Hermitian forms on the explicit period quotients, retaining
exactly the given reference trace polarization. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.periodHermitian (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →ₗ⋆[ℂ] Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →ₗ[ℂ] ℂ :=
  let F := D.referenceAnalyticFiber hg x
  let e := (F.periodComparison D hg).toLinearMap
  (F.form.comp e).compl₂ e

def Data.ActiveHeckeThetaData.periodImaginaryForm (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →ₗ[ℝ] Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →ₗ[ℝ] ℝ :=
  let F := D.referenceAnalyticFiber hg x
  let e := (F.periodComparison D hg).toLinearMap.restrictScalars ℝ
  (F.imaginaryForm D).compl₁₂ e e

theorem Data.ActiveHeckeThetaData.periodImaginaryForm_apply (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (u v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.periodImaginaryForm hg x u v = (D.periodHermitian hg x u v).im := rfl

theorem Data.ActiveHeckeThetaData.periodHermitian_reference (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (u v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    (D.periodHermitian hg x (D.periodReferenceEmbedding x.val u)
      (D.periodReferenceEmbedding x.val v)).im = (D.pel.reference.traceForm u v : ℝ) := by
  let F := D.referenceAnalyticFiber hg x
  change (F.form
    (F.periodComparison D hg (D.periodProjection x.val (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings u)))
    (F.periodComparison D hg (D.periodProjection x.val (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates D.pel.reference.embeddings v)))).im = _
  rw [F.periodComparison_projection, F.periodComparison_projection]
  exact F.polarization u v

theorem Data.ActiveHeckeThetaData.periodHermitian_hermitian (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (u v : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) :
    D.periodHermitian hg x v u = star (D.periodHermitian hg x u v) :=
  (D.referenceAnalyticFiber hg x).hermitian _ _

theorem Data.ActiveHeckeThetaData.periodHermitian_positive (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (u : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s)) (hu : u ≠ 0) :
    0 < (D.periodHermitian hg x u u).re := by
  let F := D.referenceAnalyticFiber hg x
  apply F.positive
  intro hz
  exact hu ((F.periodComparison D hg).injective (hz.trans (map_zero (F.periodComparison D hg)).symm))

end

end OAI.RepresentationTheory.Theta.Geometric
