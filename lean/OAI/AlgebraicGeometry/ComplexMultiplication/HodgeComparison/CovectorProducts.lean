import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WedgeAssociativity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Covector Products -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorProducts.CM.Construction

noncomputable section

/-! Products of actual one-covectors evaluate as the determinant of
their values on tangent vectors, with the standard exterior normalization. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def covectorOneProduct : (n : ℕ) → (Fin n → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) → Analysis.DifferentialForms.Manifold.Basic.FormValue E n
  | 0, _ => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1
  | n + 1, a => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (covectorOneProduct n (fun i => a i.castSucc)) (a (Fin.last n))

theorem covectorOneProduct_alternatingSum (n : ℕ) (a : Fin n → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : Fin n → E) :
    Construction.covectorOneProduct n a v = AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (fun w => ∏ i, a i (fun _ => w i)) v := by
  induction n with
  | zero => simp [Construction.covectorOneProduct, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum]
  | succ n ih =>
      rw [Construction.covectorOneProduct, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
      have hprev : (fun w => Construction.covectorOneProduct n (fun i => a i.castSucc) w) =
          AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (fun w => ∏ i, a i.castSucc (fun _ => w i)) := by
        funext w
        exact ih (fun i => a i.castSucc) w
      change _ • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct
        (fun w => Construction.covectorOneProduct n (fun i => a i.castSucc) w) (a (Fin.last n))) v = _
      rw [hprev, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_left]
      simp only [Nat.factorial_one, Nat.cast_one, mul_one]
      rw [← Nat.cast_smul_eq_nsmul ℝ,
        inv_smul_smul₀ (by exact_mod_cast Nat.factorial_ne_zero n : (n.factorial : ℝ) ≠ 0)]
      apply congrArg (fun f => AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum f v)
      funext w
      rw [Fin.prod_univ_castSucc]
      unfold AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct
      congr 1
      congr 1
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl

theorem covectorOneProduct_det (n : ℕ) (a : Fin n → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : Fin n → E) :
    Construction.covectorOneProduct n a v = (Matrix.of (fun i j => a j (fun _ => v i))).det := by
  rw [covectorOneProduct_alternatingSum, Matrix.det_apply]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorProducts.CM.Construction
