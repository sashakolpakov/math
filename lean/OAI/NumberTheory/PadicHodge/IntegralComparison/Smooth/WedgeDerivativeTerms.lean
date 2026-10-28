import OAI.AlgebraicTopology.Kunneth.WedgeLeibniz

/-! # Wedge Derivative Terms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.WedgeDerivativeTerms.Leibniz

noncomputable section

section

/-! The right-derivative term of the genuine smooth exterior product,
including its permutation sign and factorial normalization. -/

open OAI.AlgebraicTopology.Kunneth.WedgeLeibniz.Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q : ℕ}

theorem alternatingSum_rightDerivative_reindex
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E → E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (v : Fin (p + q + 1) → E) :
    AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (fun w =>
      a (fun i => w (Fin.castAdd q i).succ) *
        (fderiv ℝ b x) (w 0) (fun i => w (Fin.natAdd p i).succ)) v =
      (-1 : ℤ) ^ p • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum
        (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a (fun w => (fderiv ℝ b x) (w 0) (Fin.tail w)))
        (fun i => v (Fin.cast (by omega) i)) := by
  let g : (Fin (q + 1) → E) → ℂ := fun w => (fderiv ℝ b x) (w 0) (Fin.tail w)
  let hd : p + (q + 1) = p + q + 1 := by omega
  let F : (Fin (p + q + 1) → E) → ℂ :=
    fun w => AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a g (fun i => w (Fin.cast hd i))
  let τ : Equiv.Perm (Fin (p + q + 1)) := Fin.cycleRange ⟨p, by omega⟩
  have hf : (fun w : Fin (p + q + 1) → E =>
      a (fun i => w (Fin.castAdd q i).succ) *
        (fderiv ℝ b x) (w 0) (fun i => w (Fin.natAdd p i).succ)) =
      fun w => F (w ∘ τ) := by
    funext w
    change _ = a (fun i => w (AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.rightDerivativeIndex p q (Sum.inl i))) *
      (fderiv ℝ b x) (w (AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.rightDerivativeIndex p q (Sum.inr 0)))
        (fun i => w (AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.rightDerivativeIndex p q (Sum.inr i.succ)))
    simp only [AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.rightDerivativeIndex_left, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.rightDerivativeIndex_zero, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.rightDerivativeIndex_right]
  rw [hf, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_permute]
  change Equiv.Perm.sign (Fin.cycleRange (⟨p, by omega⟩ : Fin (p + q + 1))) • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum F v = _
  rw [Fin.sign_cycleRange]
  change (-1 : ℤ) ^ p • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum F v = _
  exact congrArg ((-1 : ℤ) ^ p • ·) (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_cast hd (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a g) v)

theorem alternatingSum_finBlock_right_fderiv
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E → E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (v : Fin (p + (q + 1)) → E) :
    ((q + 1 : ℕ) : ℂ) * AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum
        (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a (fun w => (fderiv ℝ b x) (w 0) (Fin.tail w))) v =
      AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a (extDeriv b x)) v := by
  let g : (Fin (q + 1) → E) → ℂ := fun w => (fderiv ℝ b x) (w 0) (Fin.tail w)
  have hg (w : Fin (q + 1) → E) : AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum g w = (q.factorial : ℂ) * extDeriv b x w := by
    rw [← nsmul_eq_mul]
    exact AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_fderiv b x w
  have he : AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a (AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum g) =
      fun w => (q.factorial : ℂ) * AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a (extDeriv b x) w := by
    funext w
    simp only [AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct, hg]
    ring
  have h := AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_right a g v
  rw [he, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_smul, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul] at h
  apply mul_left_cancel₀ (show (q.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero q)
  calc
    (q.factorial : ℂ) * (((q + 1 : ℕ) : ℂ) * AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a g) v) =
        (((q + 1 : ℕ) : ℂ) * (q.factorial : ℂ)) * AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct a g) v := by ring
    _ = _ := h.symm

end

/-! The full graded Leibniz rule for the actual smooth exterior
product, proved with the native normalization. -/

open OAI.AlgebraicTopology.Kunneth.WedgeLeibniz.Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q : ℕ}

theorem left_term (a : E → E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (v : Fin (p + q + 1) → E) :
    (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
        AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (fun w =>
          (fderiv ℝ a x) (w 0) (fun i => w (Fin.castAdd q i).succ) *
            b (fun i => w (Fin.natAdd p i).succ)) v =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (extDeriv a x) b) v := by
  rw [AlgebraicTopology.Kunneth.WedgeLeibniz.Constructions.alternatingSum_leftDerivative_reindex, AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast_apply,
    AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
  have h := AlgebraicTopology.Kunneth.WedgeLeibniz.Constructions.alternatingSum_finBlock_fderiv a b x (fun i => v (Fin.cast (by omega) i))
  rw [← h]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, Nat.factorial_succ, Nat.cast_mul]
  have hp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hs : ((p + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  field_simp

theorem right_term (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E → E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (v : Fin (p + q + 1) → E) :
    (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
        AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (fun w =>
          a (fun i => w (Fin.castAdd q i).succ) *
            (fderiv ℝ b x) (w 0) (fun i => w (Fin.natAdd p i).succ)) v =
      (-1 : ℤ) ^ p • AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a (extDeriv b x)) v := by
  rw [alternatingSum_rightDerivative_reindex,
    smul_comm (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) ((-1 : ℤ) ^ p)]
  apply congrArg ((-1 : ℤ) ^ p • ·)
  rw [AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast_apply, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
  have h := alternatingSum_finBlock_right_fderiv a b x (fun i => v (Fin.cast (by omega) i))
  rw [← h]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, Nat.factorial_succ, Nat.cast_mul]
  have hp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hs : ((q + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  field_simp

theorem extDeriv_wedge (a : E → E [⋀^Fin p]→L[ℝ] ℂ) (b : E → E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (ha : ContDiffAt ℝ 1 a x) (hb : ContDiffAt ℝ 1 b x) :
    extDeriv (fun y => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a y) (b y)) x =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (extDeriv a x) (b x)) +
        (-1 : ℤ) ^ p • AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a x) (extDeriv b x)) := by
  ext v
  change extDeriv (fun y => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a y) (b y)) x v =
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (extDeriv a x) (b x)) v +
      (-1 : ℤ) ^ p • AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorDegreeCast (by omega) (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a x) (extDeriv b x)) v
  rw [AlgebraicTopology.Kunneth.WedgeLeibniz.Constructions.extDeriv_covectorWedge_apply a b x ha hb, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_add, smul_add,
    left_term, right_term]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.WedgeDerivativeTerms.Leibniz
