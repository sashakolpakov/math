import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PureTopCoefficient
import OAI.AlgebraicTopology.Kunneth.FinAlternatingProduct

/-! # Two Form Wedge -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TwoFormWedge.CM

noncomputable section

/-! ThetaCycle: the literal native exterior product of two determinant
two-covectors is their four-row coordinate determinant. -/

open OAI.AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions

theorem alternating_coordinate_product_eq_det {E : Type*} (n : ℕ)
    (f : Fin n → E → ℂ) (v : Fin n → E) :
    AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (fun w => ∏ i, f i (w i)) v = Matrix.det (fun i j => f j (v i)) := by
  simpa only [AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum, Function.comp_def] using!
    (Matrix.det_apply (show Matrix (Fin n) (Fin n) ℂ from fun i j => f j (v i))).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem two_form_wedge_det (a b : E [⋀^Fin 2]→L[ℝ] ℂ)
    (f g : Fin 2 → E → ℂ)
    (ha : ∀ v, a v = Matrix.det (fun i j => f j (v i)))
    (hb : ∀ v, b v = Matrix.det (fun i j => g j (v i)))
    (v : Fin 4 → E) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b v = Matrix.det (fun i j => Fin.addCases f g j (v i)) := by
  have ha' : (a : (Fin 2 → E) → ℂ) = AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (fun w => ∏ i, f i (w i)) := by
    funext w
    exact (ha w).trans (alternating_coordinate_product_eq_det 2 f w).symm
  have hb' : (b : (Fin 2 → E) → ℂ) = AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (fun w => ∏ i, g i (w i)) := by
    funext w
    exact (hb w).trans (alternating_coordinate_product_eq_det 2 g w).symm
  rw [AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum, ha', hb',
    AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_left, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_right]
  have hp : AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (fun w : Fin 2 → E => ∏ i, f i (w i))
      (fun w : Fin 2 → E => ∏ i, g i (w i)) =
      (fun w : Fin 4 → E => ∏ i, Fin.addCases f g i (w i)) := by
    funext w
    simp only [AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct, Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]
  rw [hp, alternating_coordinate_product_eq_det]
  norm_num
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TwoFormWedge.CM
