import OAI.AlgebraicTopology.Kunneth.WedgeAlgebra
import OAI.AlgebraicTopology.Kunneth.FinAlternatingProduct

/-! # Wedge Associativity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WedgeAssociativity.CM.Construction

noncomputable section

/-! Associativity of the actual normalized exterior product, with
the finite degree transports made explicit. -/

variable {E : Type*} {p q r : ℕ}

theorem finBlockProduct_assoc (f : (Fin p → E) → ℂ) (g : (Fin q → E) → ℂ)
    (h : (Fin r → E) → ℂ) (v : Fin (p + (q + r)) → E) :
    AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct f g) h (fun i => v (Fin.cast (Nat.add_assoc p q r) i)) =
      AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct f (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct g h) v := by
  have hl : (fun i : Fin r => v (Fin.cast (Nat.add_assoc p q r) (Fin.natAdd (p + q) i))) =
      (fun i : Fin r => v (Fin.natAdd p (Fin.natAdd q i))) := by
    funext i
    congr 1
    apply Fin.ext
    exact Nat.add_assoc p q i.val
  unfold AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct
  rw [hl]
  exact mul_assoc _ _ _

theorem finBlockProduct_real_smul_left (c : ℝ) (f : (Fin p → E) → ℂ)
    (g : (Fin q → E) → ℂ) :
    AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (fun v => c • f v) g = fun v => c • AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct f g v := by
  funext v
  exact smul_mul_assoc c _ _

theorem finBlockProduct_real_smul_right (c : ℝ) (f : (Fin p → E) → ℂ)
    (g : (Fin q → E) → ℂ) :
    AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct f (fun v => c • g v) = fun v => c • AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct f g v := by
  funext v
  exact mul_smul_comm c _ _

theorem wedgeNormalization_left (p q r : ℕ) :
    (((((p + q).factorial : ℝ) * (r.factorial : ℝ))⁻¹) *
      ((((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) * ((p + q).factorial : ℝ))) =
      (((p.factorial : ℝ) * (q.factorial : ℝ) * (r.factorial : ℝ))⁻¹) := by
  have hp : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hr : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hpq : ((p + q).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (p + q)
  field_simp

theorem wedgeNormalization_right (p q r : ℕ) :
    (((p.factorial : ℝ) * ((q + r).factorial : ℝ))⁻¹) *
      ((((q.factorial : ℝ) * (r.factorial : ℝ))⁻¹) * ((q + r).factorial : ℝ)) =
      (((p.factorial : ℝ) * (q.factorial : ℝ) * (r.factorial : ℝ))⁻¹) := by
  have hp : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hr : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hqr : ((q + r).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (q + r)
  field_simp

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covectorWedge_nested_left (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E p) (b : Analysis.DifferentialForms.Manifold.Basic.FormValue E q)
    (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E r) (v : Fin ((p + q) + r) → E) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b) c v =
      (((p.factorial : ℝ) * (q.factorial : ℝ) * (r.factorial : ℝ))⁻¹) •
        AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a b) c) v := by
  rw [AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
  have hab : (fun w => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b w) =
      fun w => (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a b) w :=
    funext (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum a b)
  change _ • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (fun w => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b w) c) v = _
  rw [hab, finBlockProduct_real_smul_left, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_real_smul, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_left]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, mul_assoc, wedgeNormalization_left]

theorem covectorWedge_nested_right (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E p) (b : Analysis.DifferentialForms.Manifold.Basic.FormValue E q)
    (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E r) (v : Fin (p + (q + r)) → E) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge b c) v =
      (((p.factorial : ℝ) * (q.factorial : ℝ) * (r.factorial : ℝ))⁻¹) •
        AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct b c)) v := by
  rw [AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
  have hbc : (fun w => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge b c w) =
      fun w => (((q.factorial : ℝ) * (r.factorial : ℝ))⁻¹) • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct b c) w :=
    funext (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum b c)
  change _ • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a (fun w => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge b c w)) v = _
  rw [hbc, finBlockProduct_real_smul_right, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_real_smul, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_right]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, mul_assoc, wedgeNormalization_right]

theorem covectorWedge_assoc (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E p) (b : Analysis.DifferentialForms.Manifold.Basic.FormValue E q) (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E r) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (Nat.add_assoc p q r) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b) c) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge b c) := by
  ext v
  rw [AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast_apply, covectorWedge_nested_left, covectorWedge_nested_right]
  congr 1
  have hcast := AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_cast (Nat.add_assoc p q r) (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a b) c) v
  exact hcast.symm.trans (congrArg (fun f => AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum f v)
    (funext (finBlockProduct_assoc a b c)))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WedgeAssociativity.CM.Construction
