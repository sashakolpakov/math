import OAI.AlgebraicTopology.Kunneth.WedgeAlternating
import OAI.AlgebraicTopology.Kunneth.FinAlternatingProduct

/-! # Wedge Leibniz -/

namespace OAI.AlgebraicTopology.Kunneth.WedgeLeibniz

noncomputable section

/-! The product rule with a closed right factor, used to compare cup products. -/

set_option backward.isDefEq.respectTransparency false

namespace Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q : ℕ}

theorem extDeriv_covectorWedge_apply
    (a : E → E [⋀^Fin p]→L[ℝ] ℂ) (b : E → E [⋀^Fin q]→L[ℝ] ℂ) (x : E)
    (ha : ContDiffAt ℝ 1 a x) (hb : ContDiffAt ℝ 1 b x)
    (v : Fin (p + q + 1) → E) :
    extDeriv (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x v =
      (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
        WedgeAlternating.Constructions.alternatingSum (fun w =>
          (fderiv ℝ a x) (w 0) (fun i => w (Fin.castAdd q i).succ) *
            b x (fun i => w (Fin.natAdd p i).succ) +
          a x (fun i => w (Fin.castAdd q i).succ) *
            (fderiv ℝ b x) (w 0) (fun i => w (Fin.natAdd p i).succ)) v := by
  let c : ℝ := ((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹
  let F : E → (Fin (p + q) → E) → ℂ := fun u w =>
    (fderiv ℝ a x u) (fun i => w (Fin.castAdd q i)) *
      b x (fun i => w (Fin.natAdd p i)) +
    a x (fun i => w (Fin.castAdd q i)) *
      (fderiv ℝ b x u) (fun i => w (Fin.natAdd p i))
  have had : DifferentiableAt ℝ a x := ha.differentiableAt (by simp)
  have hbd : DifferentiableAt ℝ b x := hb.differentiableAt (by simp)
  have hwd : DifferentiableAt ℝ (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x :=
    (CovectorWedge.Constructions.contDiffAt_covectorWedge ha hb).differentiableAt (by simp)
  have hd (u : E) (w : Fin (p + q) → E) :
      (fderiv ℝ (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x u) w =
        c • WedgeAlternating.Constructions.alternatingSum (F u) w := by
    rw [← fderiv_continuousAlternatingMap_apply_const_apply hwd]
    exact WedgeAlternating.Constructions.covectorWedge_fderiv_apply had hbd u w
  have h : (p + q).factorial •
      extDeriv (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x v =
      (p + q).factorial • (c • WedgeAlternating.Constructions.alternatingSum (fun w => F (w 0) (Fin.tail w)) v) := by
    rw [← WedgeAlternating.Constructions.alternatingSum_fderiv]
    simp_rw [hd]
    rw [WedgeAlternating.Constructions.alternatingSum_real_smul, WedgeAlternating.Constructions.alternatingSum_tail, smul_comm]
  simp only [nsmul_eq_mul] at h
  exact mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero (p + q)) h

theorem alternatingSum_finBlock_fderiv
    (a : E → E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (v : Fin ((p + 1) + q) → E) :
    ((p + 1 : ℕ) : ℂ) * WedgeAlternating.Constructions.alternatingSum
      (FinAlternatingProduct.Constructions.finBlockProduct (fun w => (fderiv ℝ a x) (w 0) (Fin.tail w)) b) v =
        WedgeAlternating.Constructions.alternatingSum (FinAlternatingProduct.Constructions.finBlockProduct (extDeriv a x) b) v := by
  let f : (Fin (p + 1) → E) → ℂ := fun w => (fderiv ℝ a x) (w 0) (Fin.tail w)
  have hf (w : Fin (p + 1) → E) : WedgeAlternating.Constructions.alternatingSum f w = (p.factorial : ℂ) * extDeriv a x w := by
    rw [← nsmul_eq_mul]
    exact WedgeAlternating.Constructions.alternatingSum_fderiv a x w
  have he : FinAlternatingProduct.Constructions.finBlockProduct (WedgeAlternating.Constructions.alternatingSum f) b =
      fun w => (p.factorial : ℂ) * FinAlternatingProduct.Constructions.finBlockProduct (extDeriv a x) b w := by
    funext w
    simp only [FinAlternatingProduct.Constructions.finBlockProduct, hf, mul_assoc]
  have h := FinAlternatingProduct.Constructions.alternatingSum_finBlock_left f b v
  rw [he, WedgeAlternating.Constructions.alternatingSum_smul, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul] at h
  apply mul_left_cancel₀ (show (p.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero p)
  calc
    (p.factorial : ℂ) * (((p + 1 : ℕ) : ℂ) * WedgeAlternating.Constructions.alternatingSum (FinAlternatingProduct.Constructions.finBlockProduct f b) v) =
        (((p + 1 : ℕ) : ℂ) * (p.factorial : ℂ)) *
          WedgeAlternating.Constructions.alternatingSum (FinAlternatingProduct.Constructions.finBlockProduct f b) v := by ring
    _ = _ := h.symm

theorem alternatingSum_leftDerivative_reindex
    (a : E → E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ)
    (x : E) (v : Fin (p + q + 1) → E) :
    WedgeAlternating.Constructions.alternatingSum (fun w =>
      (fderiv ℝ a x) (w 0) (fun i => w (Fin.castAdd q i).succ) *
        b (fun i => w (Fin.natAdd p i).succ)) v =
    WedgeAlternating.Constructions.alternatingSum
      (FinAlternatingProduct.Constructions.finBlockProduct (fun w => (fderiv ℝ a x) (w 0) (Fin.tail w)) b)
      (fun i => v (Fin.cast (by omega) i)) := by
  let f : (Fin (p + 1) → E) → ℂ := fun w => (fderiv ℝ a x) (w 0) (Fin.tail w)
  have hr := WedgeAlternating.Constructions.alternatingSum_reindex (WedgeAlternating.Constructions.leftDerivativeIndex p q) (WedgeAlternating.Constructions.blockProduct f b) v
  rw [FinAlternatingProduct.Constructions.alternatingSum_finBlockProduct]
  convert hr using 1
  · congr 1
    funext w
    change _ = (fderiv ℝ a x) (w (WedgeAlternating.Constructions.leftDerivativeIndex p q (Sum.inl 0)))
      (fun i => w (WedgeAlternating.Constructions.leftDerivativeIndex p q (Sum.inl i.succ))) *
        b (fun i => w (WedgeAlternating.Constructions.leftDerivativeIndex p q (Sum.inr i)))
    simp only [WedgeAlternating.Constructions.leftDerivativeIndex_zero, WedgeAlternating.Constructions.leftDerivativeIndex_left, WedgeAlternating.Constructions.leftDerivativeIndex_right]
  · rfl

/-- Differentiating the product with a closed right factor differentiates its left factor. -/
theorem extDeriv_covectorWedge_of_right_closed
    (a : E → E [⋀^Fin p]→L[ℝ] ℂ) (b : E → E [⋀^Fin q]→L[ℝ] ℂ) (x : E)
    (ha : ContDiffAt ℝ 1 a x) (hb : ContDiffAt ℝ 1 b x) (hdb : extDeriv b x = 0) :
    extDeriv (fun y => CovectorWedge.Constructions.covectorWedge (a y) (b y)) x =
      CovectorWedge.Constructions.covectorDegreeCast (by omega) (CovectorWedge.Constructions.covectorWedge (extDeriv a x) (b x)) := by
  ext v
  rw [extDeriv_covectorWedge_apply a b x ha hb,
    WedgeAlternating.Constructions.alternatingSum_add, WedgeAlternating.Constructions.alternatingSum_derivative_right_zero (a x) b x hdb,
    add_zero, alternatingSum_leftDerivative_reindex,
    CovectorWedge.Constructions.covectorDegreeCast_apply, FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
  have h := alternatingSum_finBlock_fderiv a (b x) x
    (fun i => v (Fin.cast (by omega) i))
  rw [← h]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_natCast, Nat.factorial_succ, Nat.cast_mul]
  have hp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hq : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hs : ((p + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  field_simp

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.WedgeLeibniz
