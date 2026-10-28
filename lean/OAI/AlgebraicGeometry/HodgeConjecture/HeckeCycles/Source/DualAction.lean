import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential
import OAI.RepresentationTheory.Theta.Adelic.AnnihilatorFrame

/-! # Dual Action -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DualAction.CM

/-! The source's conjugate Hermitian block is the actual dual action
after multiplying the last coordinate by b. This identifies its displayed
annihilator coordinates with AdelicTheta's explicitly computed dual frame. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E}

def complexSL (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (τ : Gal(E/ℚ)) :
    Matrix.SpecialLinearGroup (Fin 3) ℂ :=
  Matrix.SpecialLinearGroup.map (E.val.toRingHom.comp τ.toRingHom) g.val

theorem complexSL_apply (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (τ : Gal(E/ℚ)) (x : GeometricSource.CM.Vec ℂ) :
    (complexSL E g τ).val.mulVec x = UnitaryEq.CM.Frames.localAction E g τ x := rfl

def weighted (b : E) (y : GeometricSource.CM.Vec ℂ) : GeometricSource.CM.Vec ℂ := ![y 0, y 1, (b : ℂ) * y 2]

theorem pairing_weighted (x y : GeometricSource.CM.Vec ℂ) :
    GeometricSource.CM.localPairing E B.b 1 x y = dotProduct x (weighted E B.b y) := by
  simp [GeometricSource.CM.localPairing, weighted, dotProduct, Fin.sum_univ_succ]
  ring

theorem weighted_dual_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (y : GeometricSource.CM.Vec ℂ) :
    weighted E B.b (UnitaryEq.CM.Frames.localAction E g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) y) =
      (complexSL E g 1)⁻¹.val.transpose.mulVec (weighted E B.b y) := by
  funext i
  let x := UnitaryEq.CM.Frames.localAction E g⁻¹ 1 (Pi.single i 1)
  have hx : UnitaryEq.CM.Frames.localAction E g 1 x = Pi.single i 1 := by
    change UnitaryEq.CM.Frames.localAction E g 1 (UnitaryEq.CM.Frames.localAction E g⁻¹ 1 (Pi.single i 1)) = _
    rw [← Module.End.mul_apply, ← UnitaryEq.CM.PrescribedAction.localAction_mul, mul_inv_cancel,
      UnitaryEq.CM.PrescribedAction.localAction_one, Module.End.one_apply]
  have hp := UnitaryEq.CM.Frames.pairing_preserved E g 1 x y
  rw [mul_one, pairing_weighted, pairing_weighted, hx] at hp
  have hd := RepresentationTheory.Theta.Adelic.AnnihilatorFrame.inverseTranspose_pairing
    (complexSL E g 1) x (weighted E B.b y)
  rw [complexSL_apply, hx] at hd
  simpa [dotProduct, Pi.single_apply] using hp.trans hd.symm

theorem weighted_annihilator (z : GeometricSource.CM.BallChart) (y : GeometricSource.CM.Vec ℂ)
    (hy : GeometricSource.CM.localPairing E B.b 1 (GeometricSource.CM.BallDatum.lineVector z) y = 0) :
    weighted E B.b y = RepresentationTheory.Theta.Adelic.AnnihilatorFrame.frameVector z
      (fun i : Fin 2 => y i.castSucc) := by
  have h := RepresentationTheory.Theta.Adelic.AnnihilatorFrame.annihilator_frame_coordinates z
    (weighted E B.b y) ((pairing_weighted E _ _).symm.trans hy)
  convert h using 1
  congr 1
  funext i
  fin_cases i <;> rfl

theorem annihilator_action_coordinates (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (y : GeometricSource.CM.Vec ℂ)
    (hy : GeometricSource.CM.localPairing E B.b 1 (GeometricSource.CM.BallDatum.lineVector z) y = 0) :
    (fun i : Fin 2 => UnitaryEq.CM.Frames.localAction E g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) y i.castSucc) =
      (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.dualCoordinates (complexSL E g 1) z).mulVec
        (fun i : Fin 2 => y i.castSucc) := by
  have he := weighted_dual_action E g y
  rw [weighted_annihilator E z y hy] at he
  have hframe : RepresentationTheory.Theta.Adelic.AnnihilatorFrame.frameVector z (fun i : Fin 2 => y i.castSucc) =
      y 0 • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector z 0 +
        y 1 • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector z 1 := by
    ext i
    fin_cases i <;>
      simp [RepresentationTheory.Theta.Adelic.AnnihilatorFrame.frameVector,
        RepresentationTheory.Theta.Adelic.DeterminantCoordinates.annihilatorVector]
    ring
  rw [hframe, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at he
  funext i
  have h := congrFun he i.castSucc
  fin_cases i <;>
    simpa [weighted, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.dualCoordinates,
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.dualColumn, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, mul_comm] using h

theorem annihilator_coordinate_det (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) :
    (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.dualCoordinates (complexSL E g 1) z).det =
      PeriodDifferential.CM.lineScale E g z :=
  RepresentationTheory.Theta.Adelic.DeterminantCoordinates.dualCoordinates_det (complexSL E g 1) z

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DualAction.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DualAction.CM.Frame

/-! The exact action on the source's adapted Lagrangian frame. Its
determinant is the square of the distinguished line factor: compact
blocks have determinant one and the annihilator contributes the same
factor as the line. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PrescribedAction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DualAction.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} (places : GeometricSource.CM.Places E) (d : Gal(E/ℚ) → Bool)

def distinguishedBlock (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let A := RepresentationTheory.Theta.Adelic.DeterminantCoordinates.dualCoordinates (complexSL E g 1) z
  !![PeriodDifferential.CM.lineScale E g z, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

theorem distinguishedBlock_det (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) :
    (distinguishedBlock E g z).det = PeriodDifferential.CM.lineScale E g z ^ 2 := by
  calc
    _ = PeriodDifferential.CM.lineScale E g z *
      (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.dualCoordinates (complexSL E g 1) z).det := by
        simp [distinguishedBlock, Matrix.det_fin_three, Matrix.det_fin_two]
        ring
    _ = _ := by rw [annihilator_coordinate_det, pow_two]

def frameBlock (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) (i : Fin places.count) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  if i = places.distinguished then distinguishedBlock E g z
  else (complexSL E g (if d (places.representative i) then
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i else places.representative i)).val

theorem frameBlock_det (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) (i : Fin places.count) :
    (frameBlock E places d g z i).det =
      if i = places.distinguished then PeriodDifferential.CM.lineScale E g z ^ 2 else 1 := by
  unfold frameBlock
  split_ifs
  · exact distinguishedBlock_det E g z
  · exact (complexSL E g _).property
  · exact (complexSL E g _).property

def blockCoordinates : (GeometricSource.CM.Positions E places → ℂ) ≃ₗ[ℂ] (Fin places.count → GeometricSource.CM.Vec ℂ) where
  toFun x i j := x (i, j)
  invFun x p := x p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def frameAction (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) :
    Module.End ℂ (GeometricSource.CM.Positions E places → ℂ) :=
  (blockCoordinates E places).symm.toLinearMap.comp
    ((LinearMap.pi (fun i => (Matrix.toLin' (frameBlock E places d g z i)).comp
      (LinearMap.proj i))).comp (blockCoordinates E places).toLinearMap)

theorem frameAction_apply (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart)
    (x : GeometricSource.CM.Positions E places → ℂ) (p : GeometricSource.CM.Positions E places) :
    frameAction E places d g z x p =
      (frameBlock E places d g z p.1).mulVec (fun j => x (p.1, j)) p.2 := rfl

theorem frameAction_det (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) :
    LinearMap.det (frameAction E places d g z) = PeriodDifferential.CM.lineScale E g z ^ 2 := by
  let F := LinearMap.pi (fun i => (Matrix.toLin' (frameBlock E places d g z i)).comp
    (LinearMap.proj i))
  have he : LinearMap.det (frameAction E places d g z) = LinearMap.det F := by
    simpa only [LinearEquiv.symm_symm, frameAction, F, LinearMap.comp_assoc] using
      LinearMap.det_conj F (blockCoordinates E places).symm
  rw [he, LinearMap.det_pi]
  simp_rw [LinearMap.det_toLin', frameBlock_det]
  simp

theorem line_action_coordinate (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : GeometricSource.CM.Vec ℂ)
    (hx : x ∈ ℂ ∙ GeometricSource.CM.BallDatum.lineVector z) :
    UnitaryEq.CM.Frames.localAction E g 1 x 2 = PeriodDifferential.CM.lineScale E g z * x 2 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
  rw [← ha, map_smul, PeriodDifferential.CM.line_scale_action E g z hz]
  change a * (PeriodDifferential.CM.lineScale E g z * 1) = PeriodDifferential.CM.lineScale E g z * (a * 1)
  ring

theorem adapted_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (w : GeometricSource.CM.Ambient E)
    (hw : GeometricSource.CM.prescribed E B places d z w) :
    GeometricSource.CM.adaptedCoordinates E places d (ComplexAction.CM.ambientOperator E g w) =
      frameAction E places d g z (GeometricSource.CM.adaptedCoordinates E places d w) := by
  funext p
  rcases p with ⟨i, j⟩
  rw [frameAction_apply]
  by_cases hi : i = places.distinguished
  · subst i
    have hp := hw places.distinguished
    simp only [places.identity, mul_one] at hp
    have hl := line_action_coordinate E g z hz (w 1) hp.1
    have ha := annihilator_action_coordinates E g z (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) hp.2
    fin_cases j
    · simpa [GeometricSource.CM.adaptedCoordinates, frameBlock, distinguishedBlock, places.identity,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, UnitaryEq.CM.Frames.ambientOperator_apply] using hl
    · simpa [GeometricSource.CM.adaptedCoordinates, frameBlock, distinguishedBlock, places.identity,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, UnitaryEq.CM.Frames.ambientOperator_apply] using congrFun ha 0
    · simpa [GeometricSource.CM.adaptedCoordinates, frameBlock, distinguishedBlock, places.identity,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, UnitaryEq.CM.Frames.ambientOperator_apply] using congrFun ha 1
  · simp only [GeometricSource.CM.adaptedCoordinates, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right hi, frameBlock]
    split_ifs <;> rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.DualAction.CM.Frame

end

end OAI
