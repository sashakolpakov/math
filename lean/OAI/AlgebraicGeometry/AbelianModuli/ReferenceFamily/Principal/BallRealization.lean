import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.MatrixRealization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallAction
import OAI.NumberTheory.ArithmeticGroups.Diagonal
import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

/-! # Ball Realization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original prescribed ball is the actual negative-line ball of
the distinguished SU group, with identical affine coordinates and action. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.domain_eq_arithmeticBall : P.domain = (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) := by
  ext z
  change (Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]) P.distinguished
    (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (star (Geometry.ComplexBall.PrescribedSignsB.lineVector z))).re < 0 ↔ _
  rw [NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.localB_diagonal_real]
  change Complex.normSq (z 0) + Complex.normSq (z 1) + (P.μ P.b).re * Complex.normSq 1 < 0 ↔
    Complex.normSq (z 0) + Complex.normSq (z 1) < -(P.μ P.b).re
  rw [Complex.normSq_one, mul_one]
  constructor <;> intro h <;> linarith

def Datum.RankThreePELDatum.arithmeticBallEquiv : P.Domain ≃ₜ Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b) := Homeomorph.setCongr P.domain_eq_arithmeticBall

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.arithmeticBallEquiv_val (z : P.Domain) : (P.arithmeticBallEquiv z).val = z.val := rfl

theorem Datum.RankThreePELDatum.arithmeticBallEquiv_action (N : ℕ) (g : Groups.principalSpecialUnitary P.b P.lattice N) (z : P.Domain) :
    P.arithmeticBallEquiv (g • z) = P.principalArchimedeanMap N g • P.arithmeticBallEquiv z := by
  apply Subtype.ext
  rfl

include P in
theorem Datum.RankThreePELDatum.domain_connected (hP : P.IsAdmissible) : ConnectedSpace P.Domain := by
  let : ConnectedSpace (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (P.μ P.b)) := Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_connected _ hP.2.2.2.1
  exact P.arithmeticBallEquiv.symm.surjective.connectedSpace P.arithmeticBallEquiv.symm.continuous

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
