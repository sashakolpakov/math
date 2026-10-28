import OAI.Analysis.DifferentialForms.Manifold.Alternatization
import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Covector Wedge -/

namespace OAI.AlgebraicTopology.Kunneth.CovectorWedge

noncomputable section

/-! The usual exterior product of complex-valued continuous real covectors. -/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p q : ℕ}

/-- Multiply the values of two multilinear maps on the two blocks of inputs. -/
def covectorProduct (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (p + q) => E) ℂ :=
  let scale : ℂ →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℂ :=
    (ContinuousLinearMap.lsmul ℝ ℂ).flip b.toContinuousMultilinearMap
  (scale.compContinuousMultilinearMap a.toContinuousMultilinearMap).uncurrySum.domDomCongr
    finSumFinEquiv

@[simp] theorem covectorProduct_apply
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ)
    (v : Fin (p + q) → E) :
    covectorProduct a b v =
      a (fun i => v (Fin.castAdd q i)) * b (fun i => v (Fin.natAdd p i)) := rfl

/-- Alternating the block product, with the standard factorial normalization. -/
def covectorWedge (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    E [⋀^Fin (p + q)]→L[ℝ] ℂ :=
  (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
    OAI.Analysis.DifferentialForms.Manifold.Alternatization.alternatizationCLM E ℂ (Fin (p + q)) (covectorProduct a b)

theorem covectorWedge_apply
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ)
    (v : Fin (p + q) → E) :
    covectorWedge a b v =
      (((p.factorial : ℝ) * (q.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (p + q)), Equiv.Perm.sign σ •
          (a (fun i => v (σ (Fin.castAdd q i))) *
            b (fun i => v (σ (Fin.natAdd p i)))) := by
  simp only [covectorWedge, ContinuousAlternatingMap.smul_apply,
    OAI.Analysis.DifferentialForms.Manifold.Alternatization.alternatizationCLM_apply, ContinuousMultilinearMap.alternatization_apply_apply,
    covectorProduct_apply, Function.comp_def]

theorem covectorProduct_add_left (a a' : E [⋀^Fin p]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    covectorProduct (a + a') b = covectorProduct a b + covectorProduct a' b := by
  ext v
  simp [add_mul]

theorem covectorProduct_add_right (a : E [⋀^Fin p]→L[ℝ] ℂ)
    (b b' : E [⋀^Fin q]→L[ℝ] ℂ) :
    covectorProduct a (b + b') = covectorProduct a b + covectorProduct a b' := by
  ext v
  simp [mul_add]

theorem covectorProduct_smul_left (c : ℂ) (a : E [⋀^Fin p]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    covectorProduct (c • a) b = c • covectorProduct a b := by
  ext v
  simp [mul_assoc]

theorem covectorProduct_smul_right (c : ℂ) (a : E [⋀^Fin p]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    covectorProduct a (c • b) = c • covectorProduct a b := by
  ext v
  simp [mul_left_comm]

theorem covectorProduct_norm_le
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    ‖covectorProduct a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  rw [covectorProduct_apply, norm_mul]
  calc
    ‖a (fun i => v (Fin.castAdd q i))‖ * ‖b (fun i => v (Fin.natAdd p i))‖ ≤
        (‖a‖ * ∏ i, ‖v (Fin.castAdd q i)‖) *
          (‖b‖ * ∏ i, ‖v (Fin.natAdd p i)‖) :=
      mul_le_mul (a.le_opNorm _) (b.le_opNorm _) (norm_nonneg _) (by positivity)
    _ = (‖a‖ * ‖b‖) * ∏ i, ‖v i‖ := by
      rw [Fin.prod_univ_add]
      ring

/-- The block product is a bounded bilinear operation. -/
def covectorProductCLM (p q : ℕ) :
    (E [⋀^Fin p]→L[ℝ] ℂ) →L[ℝ]
      (E [⋀^Fin q]→L[ℝ] ℂ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (p + q) => E) ℂ :=
  (LinearMap.mk₂ ℝ covectorProduct covectorProduct_add_left
    (fun c a b => by
      ext v
      simp [Complex.real_smul, mul_assoc])
    covectorProduct_add_right
    (fun c a b => by
      ext v
      simp [Complex.real_smul, mul_left_comm])).mkContinuous₂ 1
        (fun a b => by simpa only [LinearMap.mk₂_apply, one_mul] using covectorProduct_norm_le a b)

@[simp] theorem covectorProductCLM_apply
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    covectorProductCLM (E := E) p q a b = covectorProduct a b := rfl

theorem contDiff_covectorWedge {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {r : WithTop ℕ∞} {a : D → E [⋀^Fin p]→L[ℝ] ℂ}
    {b : D → E [⋀^Fin q]→L[ℝ] ℂ}
    (ha : ContDiff ℝ r a) (hb : ContDiff ℝ r b) :
    ContDiff ℝ r (fun x => covectorWedge (a x) (b x)) := by
  have hp : ContDiff ℝ r (fun x => covectorProduct (a x) (b x)) := by
    simpa only [Function.comp_apply, covectorProductCLM_apply] using
      (((covectorProductCLM (E := E) p q).contDiff.comp ha).clm_apply hb)
  exact ((OAI.Analysis.DifferentialForms.Manifold.Alternatization.alternatizationCLM E ℂ (Fin (p + q))).contDiff.comp hp).const_smul _

theorem contDiffOn_covectorWedge {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {r : WithTop ℕ∞} {a : D → E [⋀^Fin p]→L[ℝ] ℂ}
    {b : D → E [⋀^Fin q]→L[ℝ] ℂ} {s : Set D}
    (ha : ContDiffOn ℝ r a s) (hb : ContDiffOn ℝ r b s) :
    ContDiffOn ℝ r (fun x => covectorWedge (a x) (b x)) s := by
  have hp : ContDiffOn ℝ r (fun x => covectorProduct (a x) (b x)) s := by
    simpa only [Function.comp_apply, covectorProductCLM_apply] using
      (((covectorProductCLM (E := E) p q).contDiff.comp_contDiffOn ha).clm_apply hb)
  exact ((OAI.Analysis.DifferentialForms.Manifold.Alternatization.alternatizationCLM E ℂ (Fin (p + q))).contDiff.comp_contDiffOn hp).const_smul _

theorem contDiffAt_covectorWedge {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {r : WithTop ℕ∞} {a : D → E [⋀^Fin p]→L[ℝ] ℂ}
    {b : D → E [⋀^Fin q]→L[ℝ] ℂ} {x : D}
    (ha : ContDiffAt ℝ r a x) (hb : ContDiffAt ℝ r b x) :
    ContDiffAt ℝ r (fun y => covectorWedge (a y) (b y)) x := by
  have hp : ContDiffAt ℝ r (fun y => covectorProduct (a y) (b y)) x := by
    simpa only [Function.comp_apply, covectorProductCLM_apply] using
      (((covectorProductCLM (E := E) p q).contDiff.contDiffAt.comp x ha).clm_apply hb)
  exact ((OAI.Analysis.DifferentialForms.Manifold.Alternatization.alternatizationCLM E ℂ (Fin (p + q))).contDiff.contDiffAt.comp x hp).const_smul _

/-- Exterior multiplication commutes with pullback of covectors. -/
theorem covectorWedge_pullback {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (a : F [⋀^Fin p]→L[ℝ] ℂ) (b : F [⋀^Fin q]→L[ℝ] ℂ) :
    covectorWedge (a.compContinuousLinearMap f) (b.compContinuousLinearMap f) =
      (covectorWedge a b).compContinuousLinearMap f := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    covectorWedge_apply, Function.comp_def]

/-- The character of an exterior product is the product of the two characters. -/
theorem covectorWedge_eigen (f : E → E) (c d : ℂ)
    (a : E [⋀^Fin p]→L[ℝ] ℂ) (b : E [⋀^Fin q]→L[ℝ] ℂ)
    (ha : ∀ v, a (fun i => f (v i)) = c * a v)
    (hb : ∀ v, b (fun i => f (v i)) = d * b v)
    (v : Fin (p + q) → E) :
    covectorWedge a b (fun i => f (v i)) = (c * d) * covectorWedge a b v := by
  rw [covectorWedge_apply, covectorWedge_apply, mul_smul_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [ha, hb, mul_smul_comm]
  congr 1
  ring

/-- Reindex a covector along equality of degrees. -/
def covectorDegreeCast {n m : ℕ} (h : n = m) (a : E [⋀^Fin n]→L[ℝ] ℂ) :
    E [⋀^Fin m]→L[ℝ] ℂ := h ▸ a

@[simp] theorem covectorDegreeCast_rfl {n : ℕ} (a : E [⋀^Fin n]→L[ℝ] ℂ) :
    covectorDegreeCast rfl a = a := rfl

theorem covectorDegreeCast_apply {n m : ℕ} (h : n = m)
    (a : E [⋀^Fin n]→L[ℝ] ℂ) (v : Fin m → E) :
    covectorDegreeCast h a v = a (fun i => v (Fin.cast h i)) := by
  subst m
  rfl

theorem covectorDegreeCast_eq_cast {n m : ℕ} (h : n = m)
    (a : E [⋀^Fin n]→L[ℝ] ℂ) :
    covectorDegreeCast h a = cast (congrArg (fun k => E [⋀^Fin k]→L[ℝ] ℂ) h) a := by
  subst m
  exact covectorDegreeCast_rfl a

/-- Pure Hodge types add under exterior multiplication. -/
theorem hasBidegree_covectorWedge [NormedSpace ℂ E] {p q r s : ℕ}
    (a : E [⋀^Fin (p + q)]→L[ℝ] ℂ) (b : E [⋀^Fin (r + s)]→L[ℝ] ℂ)
    (ha : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q a) (hb : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E r s b) :
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (p + r) (q + s)
      (covectorDegreeCast (add_add_add_comm p q r s) (covectorWedge a b)) := by
  intro z v
  have h := covectorWedge_eigen (fun x : E => (z : ℂ) • x)
    (OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z) (OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter r s z) a b (ha z) (hb z)
    (fun i => v (Fin.cast (add_add_add_comm p q r s) i))
  simp only [covectorDegreeCast_apply]
  have hc : OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter r s z =
      OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + r) (q + s) z := by
    simp only [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_add]
    ring
  rw [hc] at h
  exact h

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.CovectorWedge
