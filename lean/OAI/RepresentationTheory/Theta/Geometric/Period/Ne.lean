import OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall
import OAI.RepresentationTheory.Theta.Geometric.Descent

/-! # Ne -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.Ne

noncomputable section

/-!
The rational period action is built from the actual special unitary matrix
group, its distinguished complex embedding, and its action on negative
lines. Extending it by the identity outside the ball supplies an ambient
action for the calculus API; on the open ball it is exactly the usual
fractional-linear map.
-/

open scoped Classical
open OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

open OAI.Geometry.ComplexBall.ArithmeticQuotientBoostBall

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

def rationalPeriodPerm (b : E) (μ : E →+* ℂ) :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b →* Equiv.Perm LinearTheta.BallCoordinates :=
  Equiv.Perm.ofSubtype.comp
    ((MulAction.toPermHom (Geometry.ComplexBall.ArithmeticQuotientEquationsData.ArchimedeanSU b μ) (Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (μ b))).comp
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ))

@[instance_reducible] def rationalPeriodAction (b : E) (μ : E →+* ℂ) :
    MulAction (Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) LinearTheta.BallCoordinates :=
  MulAction.compHom LinearTheta.BallCoordinates (rationalPeriodPerm b μ)

theorem rationalPeriodPerm_on_ball (b : E) (μ : E →+* ℂ)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) (x : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (μ b)) :
    rationalPeriodPerm b μ γ x.val = (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ γ • x).val := by
  exact Equiv.Perm.ofSubtype_apply_of_mem _ x.property

theorem rationalPeriodPerm_preserves (b : E) (μ : E →+* ℂ)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) (x : LinearTheta.BallCoordinates) (hx : x ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (μ b)) :
    rationalPeriodPerm b μ γ x ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (μ b) := by
  rw [rationalPeriodPerm_on_ball b μ γ ⟨x, hx⟩]
  exact (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ γ • (⟨x, hx⟩ : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (μ b))).property

def periodRow (b : E) (μ : E →+* ℂ) (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b)
    (i : Fin 3) (x : LinearTheta.BallCoordinates) : ℂ :=
  (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ γ).val i 0 * x 0 +
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ γ).val i 1 * x 1 +
    (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ γ).val i 2

def fractionalPeriodMap (b : E) (μ : E →+* ℂ) (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b)
    (x : LinearTheta.BallCoordinates) : LinearTheta.BallCoordinates :=
  fun i => periodRow b μ γ i.castSucc x / periodRow b μ γ 2 x

theorem periodRow_eq_mulVec (b : E) (μ : E →+* ℂ) (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b)
    (i : Fin 3) (x : LinearTheta.BallCoordinates) :
    periodRow b μ γ i x =
      (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ γ).val.val.mulVec (Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftVector x) i := by
  simp [periodRow, Matrix.mulVec, dotProduct, Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftVector, Fin.sum_univ_succ, add_assoc]

theorem rationalPeriodPerm_eq_fractional (b : E) (μ : E →+* ℂ)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) (x : LinearTheta.BallCoordinates) (hx : x ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (μ b)) :
    rationalPeriodPerm b μ γ x = fractionalPeriodMap b μ γ x := by
  rw [rationalPeriodPerm_on_ball b μ γ ⟨x, hx⟩]
  funext i
  change _ / _ = periodRow b μ γ i.castSucc x / periodRow b μ γ 2 x
  rw [periodRow_eq_mulVec, periodRow_eq_mulVec]
  rfl

theorem periodRow_last_ne_zero (b : E) (μ : E →+* ℂ)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) (x : Geometry.ComplexBall.ArithmeticQuotientBoostBall.Ball (μ b)) : periodRow b μ γ 2 x.val ≠ 0 := by
  rw [periodRow_eq_mulVec]
  exact Geometry.ComplexBall.ArithmeticQuotientBoostBall.cone_last_ne_zero (μ b) (Geometry.ComplexBall.ArithmeticQuotientEquationsData.infinitePlaceMap b μ γ • Geometry.ComplexBall.ArithmeticQuotientBoostBall.liftBall (μ b) x)

/-- Holomorphy is proved from the matrix formula on the actual negative-line
domain; it is not an additional assumption on the rational action. -/
theorem rationalPeriodPerm_differentiableOn (b : E) (μ : E →+* ℂ)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) :
    DifferentiableOn ℂ (rationalPeriodPerm b μ γ)
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (μ b) : Set LinearTheta.BallCoordinates) := by
  have hfrac : DifferentiableOn ℂ (fractionalPeriodMap b μ γ)
      (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (μ b) : Set LinearTheta.BallCoordinates) := by
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_pi.mpr
    intro i
    change DifferentiableAt ℂ
      (fun y => periodRow b μ γ i.castSucc y / periodRow b μ γ 2 y) x
    have hrow (j : Fin 3) : DifferentiableAt ℂ (periodRow b μ γ j) x := by
      unfold periodRow
      fun_prop
    convert! (hrow i.castSucc).mul
      ((hrow 2).inv (periodRow_last_ne_zero b μ γ ⟨x, hx⟩)) using 1
  exact hfrac.congr (rationalPeriodPerm_eq_fractional b μ γ)

end

end OAI.RepresentationTheory.Theta.Geometric.Period.Ne
