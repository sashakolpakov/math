import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ArchUnitaryCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryFrameAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryCrossMatrix
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain
import OAI.RepresentationTheory.Theta.Geometric.Period.Ne

/-! # Arch Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ArchFrame

noncomputable section

/-! Identify the actual native unitary matrices and period map with the
weighted rank-three line-annihilator calculation. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain.Multiplicity OAI.RepresentationTheory.Theta.Geometric.Period.Ne
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def archUnitaryBlock (τ : Fin s) : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b →*
    Matrix.SpecialLinearGroup (Fin 3) ℂ :=
  (Matrix.SpecialLinearGroup.map (P.embeddings τ).toRingHom).comp
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (NumberField.IsCMField.complexConj E).toRingHom P.b).subtype

def archConjugateUnitaryBlock (τ : Fin s) : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b →*
    Matrix.SpecialLinearGroup (Fin 3) ℂ :=
  (Matrix.SpecialLinearGroup.map (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings τ)).toRingHom).comp
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.unitarySubgroup (NumberField.IsCMField.complexConj E).toRingHom P.b).subtype

omit [NumberField E] [NumberField.IsCMField E] in
theorem native_arch_diagonal (τ : Fin s) :
    (Multiplicity.nativeMatrix E P).map (P.embeddings τ) = UnitaryFrameAction.diagonalForm (P.embeddings τ P.b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Multiplicity.nativeMatrix, UnitaryFrameAction.diagonalForm]

theorem arch_unitary_cross (τ : Fin s) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    (archUnitaryBlock E P τ g).val.transpose * UnitaryFrameAction.diagonalForm (P.embeddings τ P.b) *
      (archConjugateUnitaryBlock E P τ g).val = UnitaryFrameAction.diagonalForm (P.embeddings τ P.b) := by
  have hc : RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E ℂ (P.embeddings τ) = ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings τ) := by
    ext x
    rw [RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.conjugateSplitEmbedding_apply]
    exact NumberField.IsCMField.complexEmbedding_complexConj E (P.embeddings τ).toRingHom x
  have h := UnitaryCrossMatrix.Intrinsic.unitary_cross_matrix E P ℂ (P.embeddings τ) g
  rw [native_arch_diagonal, hc] at h
  exact h

omit [NumberField E] [NumberField.IsCMField E] in
theorem native_localFrame_weighted (τ : Fin s) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (u : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.localFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) τ) z u =
      UnitaryFrameAction.weightedFrame (P.embeddings τ P.b) z u := by
  have hB : Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) τ =
      Matrix.toBilin' (UnitaryFrameAction.diagonalForm (P.embeddings τ P.b)) := by
    exact congrArg Matrix.toBilin' (native_arch_diagonal E P τ)
  rw [hB]
  ext i <;> fin_cases i <;>
    simp [Geometry.ComplexBall.PrescribedSignsB.localFrame, Geometry.ComplexBall.PrescribedSignsB.axis, Geometry.ComplexBall.PrescribedSignsB.lineVector, Matrix.toBilin'_apply, UnitaryFrameAction.diagonalForm,
      UnitaryFrameAction.weightedFrame, UnitaryFrameAction.weightedAnnihilator,
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, Fin.sum_univ_succ]
  ring

theorem native_chartImage_eq_periodMap (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage (archUnitaryBlock E P P.distinguished g) z =
      RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g z := by
  have hz' : z ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) := by
    change z ∈ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) : Set Geometry.ComplexBall.PrescribedSignsB.BallChart)
    rwa [← PeriodDomain.Multiplicity.native_domain_eq_ball E P]
  rw [RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_eq_fractional P.b P.μ g z hz']
  funext i
  simp only [RepresentationTheory.Theta.Geometric.Period.Ne.fractionalPeriodMap, RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_eq_mulVec]
  rfl

theorem native_arch_denominator_ne_zero (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator (archUnitaryBlock E P P.distinguished g) z ≠ 0 := by
  have hz' : z ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) := by
    change z ∈ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) : Set Geometry.ComplexBall.PrescribedSignsB.BallChart)
    rwa [← PeriodDomain.Multiplicity.native_domain_eq_ball E P]
  have h := RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_last_ne_zero P.b P.μ g ⟨z, hz'⟩
  rw [RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_eq_mulVec] at h
  exact h

def nativeActiveFrameMatrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  UnitaryFrameAction.activeFrameMatrix (P.μ P.b) (archUnitaryBlock E P P.distinguished g)
    (archConjugateUnitaryBlock E P P.distinguished g) z

theorem nativeActiveFrameMatrix_det (hP : P.IsAdmissible)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    (nativeActiveFrameMatrix E P g z).det =
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator (archUnitaryBlock E P P.distinguished g) z ^ 2 :=
  UnitaryFrameAction.activeFrameMatrix_det _ ((map_ne_zero P.μ).mpr hP.2.2.1) _ _
    (arch_unitary_cross E P P.distinguished g) z

theorem native_active_frame_transform (hP : P.IsAdmissible)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) (u : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    ((archUnitaryBlock E P P.distinguished g).val.mulVec
        (Geometry.ComplexBall.PrescribedSignsB.localFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) P.distinguished) z u).1,
      (archConjugateUnitaryBlock E P P.distinguished g).val.mulVec
        (Geometry.ComplexBall.PrescribedSignsB.localFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) P.distinguished) z u).2) =
      Geometry.ComplexBall.PrescribedSignsB.localFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P) P.distinguished)
        (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g z) ((nativeActiveFrameMatrix E P g z).mulVec u) := by
  rw [native_localFrame_weighted, native_localFrame_weighted]
  have h := UnitaryFrameAction.weightedFrame_transform (P.embeddings P.distinguished P.b)
    ((map_ne_zero P.μ).mpr hP.2.2.1) _ _ (arch_unitary_cross E P P.distinguished g)
    z (native_arch_denominator_ne_zero E P g z hz) u
  rw [native_chartImage_eq_periodMap E P g z hz] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ArchFrame
