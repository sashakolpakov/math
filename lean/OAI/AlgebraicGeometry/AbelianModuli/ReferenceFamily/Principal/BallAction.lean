import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.IsometryEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FiberBallPoint

/-! # Ball Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

section

/-! The literal principal SU group in ReferenceFamily acts on its actual negative
ball domain by the stated affine projective formula. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

omit [Algebra ℚ E] in
theorem Principal.BallAction.matrixHermitian_diagonal (b : E) (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Datum.RankThreePELDatum.matrixHermitian (Matrix.diagonal ![1, 1, b]) x y = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y := by
  simp [Datum.RankThreePELDatum.matrixHermitian, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, Fin.sum_univ_succ, Matrix.diagonal,
    mul_comm, mul_left_comm, mul_assoc]

variable {s : ℕ} (P : Datum.RankThreePELDatum E s)

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.lineAction_eq_negativeCoordinate (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    P.lineAction g z = NegativeLine.negativeLineCoordinate (EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings P.distinguished) (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) := rfl

theorem Datum.RankThreePELDatum.lineAction_embedded_isometry (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)) :
    ∀ x y, Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b])
      (EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings P.distinguished) x)
      (EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings P.distinguished) y) =
        Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) x y := by
  let H : Matrix (Fin 3) (Fin 3) E := Matrix.diagonal ![1, 1, P.b]
  have hh (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) : Datum.RankThreePELDatum.matrixHermitian H (g x) (g y) = Datum.RankThreePELDatum.matrixHermitian H x y :=
    (Principal.BallAction.matrixHermitian_diagonal P.b (g x) (g y)).trans ((hg x y).trans (Principal.BallAction.matrixHermitian_diagonal P.b x y).symm)
  have hf (x y : Fin 3 → ℂ) : Complex.HermitianMatrixForm.complexHermitianMatrixForm (H.map (P.embeddings P.distinguished)) x y =
      Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) x y :=
    (Complex.HermitianMatrixForm.complexHermitianMatrixForm_apply _ x y).trans (Normalized.HodgeLine.complexMatrixHermitian_diagonal P.μ P.b x y)
  intro x y
  exact (hf _ _).symm.trans
    ((Hermitian.IsometryEmbedding.hermitianIsometry_embedding H H g.toLinearMap hh (P.embeddings P.distinguished) x y).trans (hf x y))

theorem Datum.RankThreePELDatum.lineAction_last_ne_zero (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) :
    EmbeddedLinearGroup.embeddedLinearIso g (P.embeddings P.distinguished) (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0 :=
  NegativeLine.diagonalIsometry_last_ne_zero (P.μ P.b) _ (P.lineAction_embedded_isometry g hg) z
    ((P.mem_domain_iff_diagonal z).mp hz)

theorem Datum.RankThreePELDatum.lineAction_mem (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) : P.lineAction g z ∈ P.domain := by
  apply (P.mem_domain_iff_diagonal _).mpr
  rw [P.lineAction_eq_negativeCoordinate]
  apply NegativeLine.negativeLineCoordinate_negative
  rw [P.lineAction_embedded_isometry g hg]
  exact (P.mem_domain_iff_diagonal z).mp hz

omit [NumberField E] [NumberField.IsCMField E] in
theorem Datum.RankThreePELDatum.lineAction_one (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) : P.lineAction 1 z = z := by
  rw [P.lineAction_eq_negativeCoordinate, EmbeddedLinearGroup.embeddedLinearIso_one]
  exact NegativeLine.negativeLineCoordinate_lineVector z

theorem Datum.RankThreePELDatum.lineAction_mul (g h : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hh : h ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) : P.lineAction (g * h) z = P.lineAction g (P.lineAction h z) := by
  simp only [P.lineAction_eq_negativeCoordinate, EmbeddedLinearGroup.embeddedLinearIso_mul]
  exact (NegativeLine.negativeLineCoordinate_comp _ _ z (P.lineAction_last_ne_zero h hh z hz)).symm

@[instance_reducible]
def Datum.RankThreePELDatum.ballAction (Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΓ : Γ ≤ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)) : MulAction Γ P.Domain where
  smul g z := ⟨P.lineAction g.val z.val, P.lineAction_mem g.val (hΓ g.property) z.val z.property⟩
  one_smul z := Subtype.ext (P.lineAction_one z.val)
  mul_smul g h z := Subtype.ext (P.lineAction_mul g.val h.val (hΓ h.property) z.val z.property)

instance Datum.RankThreePELDatum.principalBallAction (N : ℕ) : MulAction (Groups.principalSpecialUnitary P.b P.lattice N) P.Domain :=
  P.ballAction (Groups.principalSpecialUnitary P.b P.lattice N) (fun _ h => h.2.1)

theorem Datum.RankThreePELDatum.principalBallAction_val (N : ℕ) (g : Groups.principalSpecialUnitary P.b P.lattice N) (z : P.Domain) :
    (g • z).val = P.lineAction g.val z.val := rfl

end

/-! The arithmetic ball action is holomorphic in the stated affine
coordinates, because its actual projective denominator never vanishes. -/

theorem Principal.BallAction.lineVector_differentiable : Differentiable ℂ Geometry.ComplexBall.PrescribedSignsB.lineVector := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · change Differentiable ℂ (fun x : Geometry.ComplexBall.PrescribedSignsB.BallChart => x 0)
    fun_prop
  · change Differentiable ℂ (fun x : Geometry.ComplexBall.PrescribedSignsB.BallChart => x 1)
    fun_prop
  · change Differentiable ℂ (fun _ : Geometry.ComplexBall.PrescribedSignsB.BallChart => (1 : ℂ))
    fun_prop

theorem Principal.BallAction.matrixLine_differentiable (m : Matrix (Fin 3) (Fin 3) ℂ) :
    Differentiable ℂ (fun z : Geometry.ComplexBall.PrescribedSignsB.BallChart => m.mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector z)) :=
  (Matrix.toLin' m).toContinuousLinearMap.differentiable.comp Principal.BallAction.lineVector_differentiable

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem Datum.RankThreePELDatum.lineAction_differentiableAt (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain) : DifferentiableAt ℂ (P.lineAction g) z := by
  apply differentiableAt_pi.mpr
  intro i
  let m := (LinearMap.toMatrix' g.toLinearMap).map P.μ
  have hd := Principal.BallAction.matrixLine_differentiable m
  change DifferentiableAt ℂ (fun w : Geometry.ComplexBall.PrescribedSignsB.BallChart => m.mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector w) i.castSucc / m.mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector w) 2) z
  have hn : m.mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector z) 2 ≠ 0 := P.lineAction_last_ne_zero g hg z hz
  simp only [div_eq_mul_inv]
  exact ((differentiable_pi.mp hd i.castSucc) z).mul (((differentiable_pi.mp hd 2) z).inv hn)

theorem Datum.RankThreePELDatum.lineAction_differentiableOn (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b)) :
    DifferentiableOn ℂ (P.lineAction g) P.domain :=
  fun z hz => (P.lineAction_differentiableAt g hg z hz).differentiableWithinAt

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
