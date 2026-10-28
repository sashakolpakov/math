import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection

/-! # Intrinsic Geometric Polynomial -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicGeometricPolynomial.Intrinsic

noncomputable section

/-! The native Hodge graph has polynomial columns in the affine ball
coordinates. Its position and momentum matrices are consequently
ambient analytic functions, derived from the actual AdelicTheta graph identity. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d m H K)

def rawGeometricFrame (z : Fin 2 → ℂ) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) : Adelic.BallGeometryData.ComplexPhase A :=
  fun v =>
    (fun ij => if v = A.distinguished then Adelic.DeterminantCoordinates.lineVector z ij.1 * a (v,0,ij.2)
      else if A.positive v ij.2 then a (v,ij) else 0,
     fun ij => if v = A.distinguished then
       Adelic.DeterminantCoordinates.annihilatorVector z 0 ij.1 * a (v,1,ij.2) + Adelic.DeterminantCoordinates.annihilatorVector z 1 ij.1 * a (v,2,ij.2)
      else if A.positive v ij.2 then 0 else a (v,ij))

theorem rawGeometricFrame_ball (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    rawGeometricFrame A z.val a = Adelic.BallGeometryData.geometricFrame A z a := rfl

theorem rawGeometricFrame_analytic (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    ContDiff ℂ ⊤ (fun z => rawGeometricFrame A z a) := by
  apply contDiff_pi.mpr
  intro v
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    rintro ⟨i,j⟩
    by_cases hv : v = A.distinguished
    · fin_cases i <;> simp only [ite_eq_left hv] <;> dsimp [Adelic.DeterminantCoordinates.lineVector] <;> fun_prop
    · simp only [ite_eq_right hv]
      exact contDiff_const
  · apply contDiff_pi.mpr
    rintro ⟨i,j⟩
    by_cases hv : v = A.distinguished
    · fin_cases i <;> simp only [ite_eq_left hv] <;> dsimp [Adelic.DeterminantCoordinates.annihilatorVector] <;> fun_prop
    · simp only [ite_eq_right hv]
      exact contDiff_const

variable (B : Adelic.DataTheta.ComparisonData F H K A)

def framePolynomial (z : Fin 2 → ℂ) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  fun i j => B.complexPhase.symm (rawGeometricFrame A z (Pi.single j 1)) (.inl i)

def momentumPolynomial (z : Fin 2 → ℂ) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  fun i j => B.complexPhase.symm (rawGeometricFrame A z (Pi.single j 1)) (.inr i)

theorem framePolynomial_analytic : ContDiff ℂ ⊤ (framePolynomial A B) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply ℂ ℂ (.inl i)).comp (B.complexPhase.symm.contDiff.comp (rawGeometricFrame_analytic A _))

theorem momentumPolynomial_analytic : ContDiff ℂ ⊤ (momentumPolynomial A B) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply ℂ ℂ (.inr i)).comp (B.complexPhase.symm.contDiff.comp (rawGeometricFrame_analytic A _))

theorem framePolynomial_ball (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    framePolynomial A B z.val = (B.frame z).val := by
  ext i j
  have h := congrArg (fun w => B.complexPhase.symm w) (hG.2.2.2.2.2.2.1 z (Pi.single j 1))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  have hi := congrFun h (.inl i)
  simpa only [framePolynomial,rawGeometricFrame_ball,Matrix.mulVec_single,MulOpposite.op_one,
    one_smul,Matrix.col,Sum.elim_inl,Matrix.transpose_apply] using hi.symm

theorem momentumPolynomial_ball (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    momentumPolynomial A B z.val = (B.period z).matrix * (B.frame z).val := by
  ext i j
  have h := congrArg (fun w => B.complexPhase.symm w) (hG.2.2.2.2.2.2.1 z (Pi.single j 1))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  have hi := congrFun h (.inr i)
  change (B.period z).matrix.mulVec ((B.frame z).val.mulVec (Pi.single j 1)) i = _ at hi
  rw [Matrix.mulVec_mulVec] at hi
  simpa only [momentumPolynomial,rawGeometricFrame_ball,Matrix.mulVec_single,MulOpposite.op_one,
    one_smul,Matrix.col,Matrix.transpose_apply] using hi.symm

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicGeometricPolynomial.Intrinsic
