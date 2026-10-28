import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeCoordinateOpen

/-! # Ball Reflection Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallReflectionLifts

noncomputable section

section

/-! The existing special-unitary ball section gives actual vector
representatives of every native ball point, all with the same Hermitian
norm. Their original affine coordinates are proved directly.
-/

theorem diagonalHermitianForm_eq_unitaryForm (b : ℂ) (x y : Fin 3 → ℂ) :
    ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, b]) x y =
      Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd ℂ) b x y := by
  rw [OrthogonalHermitianCoordinates.complexHermitianMatrixForm_diagonal]
  simp [Geometry.ComplexBall.ArithmeticQuotientEquationsData.form, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient, Fin.sum_univ_succ, add_assoc]

def nativeBallReflectionLift (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0)
    (z : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b) : Fin 3 → ℂ :=
  Matrix.SpecialLinearGroup.toLin' (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballBoost b hbim hb z).val (Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftVector 0)

theorem nativeBallReflectionLift_norm (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0)
    (z : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b) :
    ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, b])
      (nativeBallReflectionLift b hbim hb z) (nativeBallReflectionLift b hbim hb z) = b := by
  rw [diagonalHermitianForm_eq_unitaryForm]
  change Geometry.ComplexBall.ArithmeticQuotientEquationsData.form (starRingEnd ℂ) b
    (Matrix.SpecialLinearGroup.toLin' (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballBoost b hbim hb z).val (Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftVector 0))
    (Matrix.SpecialLinearGroup.toLin' (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballBoost b hbim hb z).val (Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftVector 0)) = b
  rw [(Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballBoost b hbim hb z).property]
  simp [Geometry.ComplexBall.ArithmeticQuotientEquationsData.form, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient, Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftVector, Fin.sum_univ_succ]

theorem nativeBallReflectionLift_last_ne_zero
    (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0) (z : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b) :
    nativeBallReflectionLift b hbim hb z 2 ≠ 0 := by
  apply NegativeLine.negativeDiagonal_last_ne_zero b
  rw [nativeBallReflectionLift_norm]
  exact hb

theorem nativeBallReflectionLift_coordinate
    (b : ℂ) (hbim : b.im = 0) (hb : b.re < 0) (z : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball b) :
    NegativeLine.negativeLineCoordinate (nativeBallReflectionLift b hbim hb z) = z.val := by
  exact congrArg Subtype.val (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballBoost_origin b hbim hb z)

end

/-! Any two negative lines for the fixed diagonal Hermitian form are
carried to each other by an actual complex linear isometry. -/

theorem diagonalLineNegative_iff_mem_ballOpen (β : ℂ) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β])
      (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0 ↔ z ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen β := by
  rw [diagonalHermitianForm_eq_unitaryForm, Geometry.ComplexBall.ArithmeticQuotientBoostBall.form_star_eq_complex,
    Geometry.ComplexBall.Fields.ArithmeticQuotient.complexHermitian_self_re]
  change Complex.normSq (z 0) + Complex.normSq (z 1) +
    β.re * Complex.normSq (1 : ℂ) < 0 ↔
      Complex.normSq (z 0) + Complex.normSq (z 1) < -β.re
  rw [Complex.normSq_one, mul_one]
  constructor <;> intro h <;> linarith

theorem exists_diagonalIsometry_line_transport
    (β : ℂ) (hβ : β.im = 0) (hneg : β.re < 0) (z w : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz : (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β])
      (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)).re < 0)
    (hw : (ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β])
      (Geometry.ComplexBall.PrescribedSignsB.lineVector w) (Geometry.ComplexBall.PrescribedSignsB.lineVector w)).re < 0) :
    ∃ r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec,
      (∀ x y, ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) (r x) (r y) =
        ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x y) ∧
      (Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}).map r.toLinearMap =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w} := by
  let z' : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball β := ⟨z, (diagonalLineNegative_iff_mem_ballOpen β z).mp hz⟩
  let w' : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball β := ⟨w, (diagonalLineNegative_iff_mem_ballOpen β w).mp hw⟩
  let : MulAction.IsPretransitive (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) β) (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball β) :=
    Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballAction_pretransitive β hβ hneg
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Geometry.ComplexBall.ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) β) z' w'
  let r : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec := Matrix.SpecialLinearGroup.toLin' g.val
  have hr (x y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
      ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) (r x) (r y) =
        ReferenceFamily.Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, β]) x y := by
    simpa only [diagonalHermitianForm_eq_unitaryForm] using g.property x y
  refine ⟨r, hr, ?_⟩
  rw [NegativeLine.map_lineVector_span r.toLinearMap z (NegativeLine.diagonalIsometry_last_ne_zero β r hr z hz)]
  have hcoord : NegativeLine.negativeLineCoordinate (r (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) = w := congrArg Subtype.val hg
  exact congrArg (fun t => Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector t}) hcoord

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallReflectionLifts
