import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ArchimedeanModel
import OAI.RepresentationTheory.Theta.Adelic.BallGroupComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallRealization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DefiniteUnitaryCompactness

/-! # Ball Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.BallAction.HermitianBall

noncomputable section

/-! An arbitrary normalized Hermitian form acts on the prescribed ball.
The group map is injective and its projective action is exactly the
`lineActionVia` formula in the ReferenceFamily statement. -/

open scoped Classical
open _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGroupComparison OAI.RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology

theorem formValue_complexMatrixHermitian
    {E : Type} [Field E] (μ : E →+* ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (x y : Fin 3 → ℂ) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (H.transpose.map μ) x y = Datum.RankThreePELDatum.complexMatrixHermitian μ H y x := by
  simp only [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.transpose_apply, Datum.RankThreePELDatum.complexMatrixHermitian, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def normalizerMatrix (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) :
    (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)

theorem normalizerMatrix_action (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ)) (x : Fin 3 → ℂ) :
    (normalizerMatrix e).val.mulVec x = e x :=
  LinearMap.congr_fun (Matrix.toLin'_toMatrix' e.toLinearMap) x

theorem normalizerMatrix_inverse_action (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (x : Fin 3 → ℂ) : (normalizerMatrix e).inv.mulVec x = e.symm x :=
  LinearMap.congr_fun (Matrix.toLin'_toMatrix' e.symm.toLinearMap) x

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)
    (H : Matrix (Fin 3) (Fin 3) E)
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (he : ∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)

omit [IsCMField E] in
private theorem diagonal_formValue (x y : Fin 3 → ℂ) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (RepresentationTheory.Theta.Adelic.BallGroupComparison.diagonalForm (P.μ P.b)) x y =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) y x := by
  simp [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct, RepresentationTheory.Theta.Adelic.BallGroupComparison.diagonalForm, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient,
    Datum.RankThreePELDatum.complexMatrixHermitian, Matrix.diagonal, Fin.sum_univ_succ,
    mul_comm, mul_assoc]

omit [IsCMField E] in
include he in
theorem normalizer_equation :
    (normalizerMatrix e).val.conjTranspose * (H.transpose.map P.μ) * (normalizerMatrix e).val =
      RepresentationTheory.Theta.Adelic.BallGroupComparison.diagonalForm (P.μ P.b) := by
  have hf (x y : Fin 3 → ℂ) :
      RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (H.transpose.map P.μ) ((normalizerMatrix e).val.mulVec x)
        ((normalizerMatrix e).val.mulVec y) = RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (RepresentationTheory.Theta.Adelic.BallGroupComparison.diagonalForm (P.μ P.b)) x y := by
    rw [normalizerMatrix_action, normalizerMatrix_action,
      formValue_complexMatrixHermitian, diagonal_formValue]
    exact he y x
  apply Matrix.ext
  intro i j
  have hij := hf (Pi.single i 1) (Pi.single j 1)
  rw [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue_change] at hij
  simpa [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite] using hij

def normalizedEquiv : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map P.μ) ≃ₜ* Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ :=
  (RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology.specialUnitaryBasisContinuousEquiv (H.transpose.map P.μ) (RepresentationTheory.Theta.Adelic.BallGroupComparison.diagonalForm (P.μ P.b))
    (normalizerMatrix e) (normalizer_equation P H e he)).trans
      (RepresentationTheory.Theta.Adelic.BallGroupComparison.diagonalUnitaryContinuousEquiv (P.μ P.b))

omit [IsCMField E] in
theorem normalizedEquiv_action (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (H.transpose.map P.μ)) (x : Fin 3 → ℂ) :
    (normalizedEquiv P H e he g).val.val.mulVec x = e.symm (g.val.val.mulVec (e x)) := by
  change ((normalizerMatrix e).inv * g.val.val * (normalizerMatrix e).val).mulVec x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    normalizerMatrix_action, normalizerMatrix_inverse_action]

variable (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

def rationalHom : Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H) →*
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ :=
  (normalizedEquiv P H e he).toMonoidHom.comp (ArchimedeanModel.HermitianArithmetic.complexHom δ hδ hδ0 H P.μ)

theorem rationalHom_action
    (g : Groups.specialUnitarySubgroup (R := E) (Datum.RankThreePELDatum.matrixHermitian H))
    (x : Fin 3 → ℂ) :
    (rationalHom P H e he δ hδ hδ0 g).val.val.mulVec x =
      e.symm (((LinearMap.toMatrix' g.val.toLinearMap).map P.μ).mulVec (e x)) := by
  change (normalizedEquiv P H e he (ArchimedeanModel.HermitianArithmetic.complexHom δ hδ hδ0 H P.μ g)).val.val.mulVec x = _
  rw [normalizedEquiv_action, ArchimedeanModel.HermitianArithmetic.complexHom_matrix]

theorem rationalHom_injective : Function.Injective (rationalHom P H e he δ hδ hδ0) :=
  (normalizedEquiv P H e he).injective.comp (ArchimedeanModel.HermitianArithmetic.complexHom_injective δ hδ hδ0 H P.μ)

variable (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (N : ℕ)

def principalHom : ↥(Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
    Groups.specialUnitarySubgroup (Datum.RankThreePELDatum.matrixHermitian H)) →*
      Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU P.b P.μ :=
  (rationalHom P H e he δ hδ hδ0).comp (Subgroup.inclusion inf_le_right)

theorem principalHom_injective : Function.Injective (principalHom P H e he δ hδ hδ0 Λ N) := by
  intro g k hgk
  have h := rationalHom_injective P H e he δ hδ hδ0 hgk
  apply Subtype.ext
  exact congrArg (fun a : Groups.specialUnitarySubgroup (R := E)
    (Datum.RankThreePELDatum.matrixHermitian H) => a.val) h

@[instance_reducible]
def principalAction : MulAction ↥(Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
    Groups.specialUnitarySubgroup (Datum.RankThreePELDatum.matrixHermitian H)) P.Domain where
  smul g z := P.arithmeticBallEquiv.symm
    (principalHom P H e he δ hδ hδ0 Λ N g • P.arithmeticBallEquiv z)
  one_smul z := by
    change P.arithmeticBallEquiv.symm
      (principalHom P H e he δ hδ hδ0 Λ N 1 • P.arithmeticBallEquiv z) = z
    rw [map_one, one_smul, Homeomorph.symm_apply_apply]
  mul_smul g k z := by
    change P.arithmeticBallEquiv.symm
      (principalHom P H e he δ hδ hδ0 Λ N (g * k) • P.arithmeticBallEquiv z) =
      P.arithmeticBallEquiv.symm (principalHom P H e he δ hδ hδ0 Λ N g •
        P.arithmeticBallEquiv (P.arithmeticBallEquiv.symm
          (principalHom P H e he δ hδ hδ0 Λ N k • P.arithmeticBallEquiv z)))
    rw [Homeomorph.apply_symm_apply, map_mul, mul_smul]

theorem principalAction_equivariant
    (g : ↥(Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
      Groups.specialUnitarySubgroup (Datum.RankThreePELDatum.matrixHermitian H))) (z : P.Domain) :
    letI := principalAction P H e he δ hδ hδ0 Λ N
    P.arithmeticBallEquiv (g • z) =
      principalHom P H e he δ hδ hδ0 Λ N g • P.arithmeticBallEquiv z :=
  P.arithmeticBallEquiv.apply_symm_apply _

theorem principalAction_val
    (g : ↥(Groups.principalLatticeSubgroup (R := E) Λ.toAddSubgroup N ⊓
      Groups.specialUnitarySubgroup (Datum.RankThreePELDatum.matrixHermitian H))) (z : P.Domain) :
    letI := principalAction P H e he δ hδ hδ0 Λ N
    (g • z).val = P.lineActionVia e g.val z.val := by
  change (fun i : Fin 2 =>
    (principalHom P H e he δ hδ hδ0 Λ N g).val.val.mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val) i.castSucc /
      (principalHom P H e he δ hδ hδ0 Λ N g).val.val.mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val) 2) = _
  change (fun i : Fin 2 =>
    (rationalHom P H e he δ hδ hδ0 ⟨g.val, g.property.2⟩).val.val.mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val) i.castSucc /
      (rationalHom P H e he δ hδ hδ0 ⟨g.val, g.property.2⟩).val.val.mulVec (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val) 2) = _
  simp_rw [rationalHom_action]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.BallAction.HermitianBall
