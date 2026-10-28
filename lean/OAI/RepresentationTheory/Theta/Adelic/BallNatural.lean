import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
import OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Ball Natural -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.BallNatural

/-! The actual SU(2,1) action on the complex two-ball in an affine
negative-line chart. The projective denominator is nowhere zero. -/

open _root_.Matrix

open OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

def standardForm : (Matrix (Fin 3) (Fin 3) ℂ)ˣ where
  val := !![1, 0, 0; 0, 1, 0; 0, 0, -1]
  inv := !![1, 0, 0; 0, 1, 0; 0, 0, -1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

abbrev BallGroup := SpecialUnitary.SU standardForm.val
def Ball := {z : Fin 2 → ℂ | Complex.normSq (z 0) + Complex.normSq (z 1) < 1}

def asSL : BallGroup →* Matrix.SpecialLinearGroup (Fin 3) ℂ where
  toFun g := ⟨g.val.val, congrArg Units.val g.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem formValue_real (x : Fin 3 → ℂ) :
    (Weil.AdelicSplitting.TensorSpace.Construction.formValue standardForm.val x x).re =
      Complex.normSq (x 0) + Complex.normSq (x 1) - Complex.normSq (x 2) := by
  simp [Weil.AdelicSplitting.TensorSpace.Construction.formValue, standardForm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    Complex.mul_re, Complex.normSq_apply]
  ring

theorem line_form_negative (z : Ball) :
    (Weil.AdelicSplitting.TensorSpace.Construction.formValue standardForm.val (DeterminantCoordinates.lineVector z.val) (DeterminantCoordinates.lineVector z.val)).re < 0 := by
  rw [formValue_real]
  change Complex.normSq (z.val 0) + Complex.normSq (z.val 1) - Complex.normSq 1 < 0
  rw [Complex.normSq_one]
  exact sub_lt_zero.mpr z.property

theorem image_form_negative (g : BallGroup) (z : Ball) :
    (Weil.AdelicSplitting.TensorSpace.Construction.formValue standardForm.val ((asSL g).val.mulVec (DeterminantCoordinates.lineVector z.val))
      ((asSL g).val.mulVec (DeterminantCoordinates.lineVector z.val))).re < 0 := by
  have h := Weil.AdelicSplitting.TensorSpace.Construction.formValue_unitary standardForm.val (SpecialUnitary.includeUnitary standardForm.val g)
    (DeterminantCoordinates.lineVector z.val) (DeterminantCoordinates.lineVector z.val)
  change (Weil.AdelicSplitting.TensorSpace.Construction.formValue standardForm.val ((SpecialUnitary.includeUnitary standardForm.val g).val.val.mulVec (DeterminantCoordinates.lineVector z.val))
    ((SpecialUnitary.includeUnitary standardForm.val g).val.val.mulVec (DeterminantCoordinates.lineVector z.val))).re < 0
  rw [h]
  exact line_form_negative z

theorem denominator_ne_zero (g : BallGroup) (z : Ball) : DeterminantCoordinates.denominator (asSL g) z.val ≠ 0 := by
  intro h0
  have hneg := image_form_negative g z
  rw [formValue_real] at hneg
  change (asSL g).val.mulVec (DeterminantCoordinates.lineVector z.val) 2 = 0 at h0
  rw [h0, Complex.normSq_zero, sub_zero] at hneg
  exact (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)).not_gt hneg

def act (g : BallGroup) (z : Ball) : Ball :=
  ⟨DeterminantCoordinates.chartImage (asSL g) z.val, by
    have hneg := image_form_negative g z
    rw [formValue_real] at hneg
    have hd := Complex.normSq_pos.mpr (denominator_ne_zero g z)
    change Complex.normSq ((asSL g).val.mulVec (DeterminantCoordinates.lineVector z.val) 0 / DeterminantCoordinates.denominator (asSL g) z.val) +
      Complex.normSq ((asSL g).val.mulVec (DeterminantCoordinates.lineVector z.val) 1 / DeterminantCoordinates.denominator (asSL g) z.val) < 1
    rw [Complex.normSq_div, Complex.normSq_div, ← add_div, div_lt_one hd]
    exact sub_lt_zero.mp hneg⟩

end RepresentationTheory.Theta.Adelic.BallNatural

namespace RepresentationTheory.Theta.Adelic.BallNatural.Factors

/-! Continuous natural half-determinant factors on the actual complex ball.
The group law is the projective denominator cocycle, and the square is the
determinant calculated from the line and annihilator coordinate frames. -/

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

instance ballMulAction : MulAction BallGroup Ball where
  smul := act
  one_smul z := by
    apply Subtype.ext
    change DeterminantCoordinates.chartImage (asSL 1) z.val = z.val
    rw [map_one, DeterminantCoordinates.chartImage_one]
  mul_smul g h z := by
    apply Subtype.ext
    change DeterminantCoordinates.chartImage (asSL (g * h)) z.val = DeterminantCoordinates.chartImage (asSL g) (DeterminantCoordinates.chartImage (asSL h) z.val)
    rw [map_mul, DeterminantCoordinates.chartImage_mul _ _ _ (denominator_ne_zero h z)]

def automorphyFactor (g : BallGroup) (z : Ball) : ℂ := DeterminantCoordinates.denominator (asSL g) z.val

@[simp] theorem automorphyFactor_one (z : Ball) : automorphyFactor 1 z = 1 := by
  simp [automorphyFactor]

theorem automorphyFactor_ne_zero (g : BallGroup) (z : Ball) : automorphyFactor g z ≠ 0 :=
  denominator_ne_zero g z

theorem automorphyFactor_mul (g h : BallGroup) (z : Ball) :
    automorphyFactor (g * h) z = automorphyFactor g (h • z) * automorphyFactor h z := by
  change DeterminantCoordinates.denominator (asSL (g * h)) z.val = _
  rw [map_mul]
  exact DeterminantCoordinates.denominator_mul (asSL g) (asSL h) z.val (denominator_ne_zero h z)

@[fun_prop] theorem asSL_continuous : Continuous asSL :=
  (Units.continuous_val.comp continuous_subtype_val).subtype_mk _

@[fun_prop] theorem lineVector_continuous : Continuous (DeterminantCoordinates.lineVector : (Fin 2 → ℂ) → Fin 3 → ℂ) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_const

theorem imageVector_continuous :
    Continuous (fun p : BallGroup × Ball => (asSL p.1).val.mulVec (DeterminantCoordinates.lineVector p.2.val)) := by
  fun_prop

@[fun_prop] theorem automorphyFactor_continuous :
    Continuous (fun p : BallGroup × Ball => automorphyFactor p.1 p.2) :=
  (continuous_apply 2).comp imageVector_continuous

instance ballContinuousSMul : ContinuousSMul BallGroup Ball where
  continuous_smul := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_apply i.castSucc).comp imageVector_continuous).div
      automorphyFactor_continuous (fun p => automorphyFactor_ne_zero p.1 p.2)

def naturalHalfFactor (m : ℕ) (g : BallGroup) (z : Ball) : ℂ := automorphyFactor g z ^ m

theorem naturalHalfFactor_continuous (m : ℕ) :
    Continuous (fun p : BallGroup × Ball => naturalHalfFactor m p.1 p.2) :=
  automorphyFactor_continuous.pow m

theorem naturalHalfFactor_mul (m : ℕ) (g h : BallGroup) (z : Ball) :
    naturalHalfFactor m (g * h) z = naturalHalfFactor m g (h • z) * naturalHalfFactor m h z := by
  rw [naturalHalfFactor, automorphyFactor_mul, mul_pow]
  rfl

theorem naturalHalfFactor_sq (m : ℕ) (g : BallGroup) (z : Ball) :
    naturalHalfFactor m g z ^ 2 = DeterminantCoordinates.hodgeDeterminantFactor (asSL g) z.val ^ m :=
  DeterminantCoordinates.natural_halfDeterminant_sq m (asSL g) z.val

end RepresentationTheory.Theta.Adelic.BallNatural.Factors

namespace RepresentationTheory.Theta.Adelic.BallNatural.LineLift

/-! The equivariant square-root line over the ball, with its actual
continuous fibre action. Its tensor square has the calculated Hodge
determinant action. Identification with oscillator operators is separate. -/

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

theorem naturalHalfFactor_inv_left (m : ℕ) (g : BallGroup) (z : Ball) :
    Factors.naturalHalfFactor m g⁻¹ (g • z) * Factors.naturalHalfFactor m g z = 1 := by
  rw [← Factors.naturalHalfFactor_mul, inv_mul_cancel, Factors.naturalHalfFactor, Factors.automorphyFactor_one, one_pow]

def naturalLineAction (m : ℕ) (g : BallGroup) (p : Ball × ℂ) : Ball × ℂ :=
  (g • p.1, Factors.naturalHalfFactor m g p.1 * p.2)

theorem naturalLineAction_continuous (m : ℕ) :
    Continuous (fun p : BallGroup × (Ball × ℂ) => naturalLineAction m p.1 p.2) := by
  unfold naturalLineAction
  apply Continuous.prodMk
  · fun_prop
  · exact ((Factors.naturalHalfFactor_continuous m).comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
        (continuous_snd.comp continuous_snd)

theorem naturalLineAction_mul (m : ℕ) (g h : BallGroup) (p : Ball × ℂ) :
    naturalLineAction m (g * h) p = naturalLineAction m g (naturalLineAction m h p) := by
  apply Prod.ext
  · exact mul_smul g h p.1
  · change Factors.naturalHalfFactor m (g * h) p.1 * p.2 =
      Factors.naturalHalfFactor m g (h • p.1) * (Factors.naturalHalfFactor m h p.1 * p.2)
    rw [Factors.naturalHalfFactor_mul, mul_assoc]

@[simp] theorem naturalLineAction_one (m : ℕ) (p : Ball × ℂ) : naturalLineAction m 1 p = p := by
  simp [naturalLineAction, Factors.naturalHalfFactor]

theorem naturalLineAction_fixed_continuous (m : ℕ) (g : BallGroup) :
    Continuous (naturalLineAction m g) := by
  change Continuous (fun p : Ball × ℂ => (g • p.1, Factors.naturalHalfFactor m g p.1 * p.2))
  apply Continuous.prodMk
  · exact (continuous_const_smul g).comp continuous_fst
  · have hc : Continuous (fun z : Ball => Factors.automorphyFactor g z) := by
      change Continuous (fun z : Ball => g.val.val.mulVec (DeterminantCoordinates.lineVector z.val) 2)
      fun_prop
    exact ((hc.comp continuous_fst).pow m).mul continuous_snd

def naturalLineLift (m : ℕ) : BallGroup →* Homeomorph (Ball × ℂ) (Ball × ℂ) where
  toFun g :=
    { toFun := naturalLineAction m g
      invFun := naturalLineAction m g⁻¹
      left_inv := by
        intro p
        rw [← naturalLineAction_mul, inv_mul_cancel, naturalLineAction_one]
      right_inv := by
        intro p
        rw [← naturalLineAction_mul, mul_inv_cancel, naturalLineAction_one]
      continuous_toFun := naturalLineAction_fixed_continuous m g
      continuous_invFun := naturalLineAction_fixed_continuous m g⁻¹ }
  map_one' := Homeomorph.ext (naturalLineAction_one m)
  map_mul' g h := Homeomorph.ext (naturalLineAction_mul m g h)

/-- The fibre action on the tensor square is the determinant factor of
the Hodge frame; this identifies the constructed line as its square root. -/
theorem naturalLineLift_tensor_square (m : ℕ) (g : BallGroup) (z : Ball) (a b : ℂ) :
    (naturalLineLift m g (z, a)).2 * (naturalLineLift m g (z, b)).2 =
      DeterminantCoordinates.hodgeDeterminantFactor (asSL g) z.val ^ m * (a * b) := by
  change (Factors.naturalHalfFactor m g z * a) * (Factors.naturalHalfFactor m g z * b) = _
  rw [← Factors.naturalHalfFactor_sq]
  ring

end RepresentationTheory.Theta.Adelic.BallNatural.LineLift

end

end OAI
