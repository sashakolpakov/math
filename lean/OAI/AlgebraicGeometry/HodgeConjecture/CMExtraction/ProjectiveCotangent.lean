import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryFrameAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FrameProjection

/-! # Projective Cotangent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCotangent.Frame

noncomputable section

/-! The weighted annihilator coordinates give the cotangent action on
the projective chart. Differentiate the exact bilinear pairing identity. -/

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FrameProjection.Multiplicity
open scoped _root_.Matrix

theorem weighted_pairing_between_points (b : ℂ) (hb : b ≠ 0)
    (x y : Fin 2 → ℂ) (j : Fin 2) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector y ⬝ᵥ (UnitaryFrameAction.diagonalForm b).mulVec (UnitaryFrameAction.weightedAnnihilator b x j) = y j - x j := by
  fin_cases j <;>
    simp [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, UnitaryFrameAction.diagonalForm, Matrix.mulVec_diagonal, UnitaryFrameAction.weightedAnnihilator,
      dotProduct, Fin.sum_univ_succ] <;> field_simp <;> ring

theorem weighted_pairing_value (b : ℂ) (y : Fin 2 → ℂ) (w : Fin 3 → ℂ) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector y ⬝ᵥ (UnitaryFrameAction.diagonalForm b).mulVec w =
      FrameProjection.Multiplicity.coordinateCovector (fun i : Fin 2 => w i.castSucc) y + b * w 2 := by
  simp [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, UnitaryFrameAction.diagonalForm, Matrix.mulVec_diagonal, FrameProjection.Multiplicity.coordinateCovector_apply,
    dotProduct, Fin.sum_univ_succ]
  ring

def weightedColumnCovector (b : ℂ) (B : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (x : Fin 2 → ℂ) (j : Fin 2) : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent :=
  FrameProjection.Multiplicity.coordinateCovector (fun i => UnitaryFrameAction.weightedDualCoordinates b B x i j)

theorem weighted_projective_affine_identity (b : ℂ) (hb : b ≠ 0)
    (A B : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (hAB : A.val.transpose * UnitaryFrameAction.diagonalForm b * B.val = UnitaryFrameAction.diagonalForm b)
    (x y : Fin 2 → ℂ) (hy : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A y ≠ 0) (j : Fin 2) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A y *
        (weightedColumnCovector b B x j (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage A y) +
          b * (B.val.mulVec (UnitaryFrameAction.weightedAnnihilator b x j)) 2) = y j - x j := by
  have h := UnitaryFrameAction.weighted_pairing_preserved b A B hAB (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector y) (UnitaryFrameAction.weightedAnnihilator b x j)
  rw [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector_chartImage A y hy, smul_dotProduct,
    weighted_pairing_between_points b hb x y j, weighted_pairing_value] at h
  exact h

theorem denominator_differentiable (A : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Differentiable ℂ (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A) := by
  unfold RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector Matrix.mulVec dotProduct
  simp [Fin.sum_univ_succ]
  fun_prop

theorem weighted_cotangent_column (b : ℂ) (hb : b ≠ 0)
    (A B : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (hAB : A.val.transpose * UnitaryFrameAction.diagonalForm b * B.val = UnitaryFrameAction.diagonalForm b)
    (O : Set (Fin 2 → ℂ)) (hO : IsOpen O) (x : Fin 2 → ℂ) (hx : x ∈ O)
    (hd : ∀ y ∈ O, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A y ≠ 0)
    (f : (Fin 2 → ℂ) → Fin 2 → ℂ) (hf : DifferentiableAt ℂ f x)
    (heq : ∀ y ∈ O, f y = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage A y) (j : Fin 2) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A x • (weightedColumnCovector b B x j).comp (fderiv ℂ f x) =
      ContinuousLinearMap.proj j := by
  let l := weightedColumnCovector b B x j
  let c := b * (B.val.mulVec (UnitaryFrameAction.weightedAnnihilator b x j)) 2
  have hzero : l (f x) + c = 0 := by
    have h := weighted_projective_affine_identity b hb A B hAB x x (hd x hx) j
    rw [sub_self, ← heq x hx] at h
    exact (mul_eq_zero.mp h).resolve_left (hd x hx)
  have hprod := (denominator_differentiable A x).hasFDerivAt.mul
    ((l.hasFDerivAt.comp x hf.hasFDerivAt).add_const c)
  have hder : HasFDerivAt (fun y => RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A y * (l (f y) + c))
      (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A x • l.comp (fderiv ℂ f x)) x := by
    change HasFDerivAt (fun y => RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A y * (l (f y) + c))
      (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A x • l.comp (fderiv ℂ f x) +
        (l (f x) + c) • fderiv ℂ (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A) x) x at hprod
    have hzD : (0 : ℂ) • fderiv ℂ (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A) x = 0 := by
      apply ContinuousLinearMap.ext
      intro y
      exact zero_mul _
    rw [hzero, hzD, add_zero] at hprod
    exact hprod
  have hnear : (fun y : Fin 2 → ℂ => y j - x j) =ᶠ[nhds x]
      (fun y => RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A y * (l (f y) + c)) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    rw [heq y hy]
    exact (weighted_projective_affine_identity b hb A B hAB x y (hd y hy) j).symm
  exact (hder.congr_of_eventuallyEq hnear).unique
    ((ContinuousLinearMap.proj j : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent).hasFDerivAt.sub_const (x j))

theorem weighted_cotangent (b : ℂ) (hb : b ≠ 0)
    (A B : Matrix.SpecialLinearGroup (Fin 3) ℂ)
    (hAB : A.val.transpose * UnitaryFrameAction.diagonalForm b * B.val = UnitaryFrameAction.diagonalForm b)
    (O : Set (Fin 2 → ℂ)) (hO : IsOpen O) (x : Fin 2 → ℂ) (hx : x ∈ O)
    (hd : ∀ y ∈ O, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A y ≠ 0)
    (f : (Fin 2 → ℂ) → Fin 2 → ℂ) (hf : DifferentiableAt ℂ f x)
    (heq : ∀ y ∈ O, f y = RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage A y) (c u : Fin 2 → ℂ) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator A x * FrameProjection.Multiplicity.coordinateCovector (UnitaryFrameAction.weightedDualCoordinates b B x *ᵥ c) (fderiv ℂ f x u) =
      FrameProjection.Multiplicity.coordinateCovector c u := by
  have h0 := congrArg (fun l : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent => l u)
    (weighted_cotangent_column b hb A B hAB O hO x hx hd f hf heq 0)
  have h1 := congrArg (fun l : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent => l u)
    (weighted_cotangent_column b hb A B hAB O hO x hx hd f hf heq 1)
  simp [weightedColumnCovector, FrameProjection.Multiplicity.coordinateCovector_apply, Fin.sum_univ_succ] at h0 h1 ⊢
  linear_combination c 0 * h0 + c 1 * h1

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCotangent.Frame
