import OAI.AlgebraicTopology.Kunneth.WedgeLeibniz
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative

/-! # Wedge Algebra -/

namespace OAI.AlgebraicTopology.Kunneth.WedgeAlgebra

noncomputable section

/-! Complex bilinearity and the smooth-form version of the exterior product. -/

set_option backward.isDefEq.respectTransparency false

namespace Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p q : ℕ}

theorem covectorWedge_add_left (a a' : E [⋀^Fin p]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    CovectorWedge.Constructions.covectorWedge (a + a') b = CovectorWedge.Constructions.covectorWedge a b + CovectorWedge.Constructions.covectorWedge a' b := by
  simp only [CovectorWedge.Constructions.covectorWedge, CovectorWedge.Constructions.covectorProduct_add_left, map_add, smul_add]

theorem covectorWedge_add_right (a : E [⋀^Fin p]→L[ℝ] ℂ)
    (b b' : E [⋀^Fin q]→L[ℝ] ℂ) :
    CovectorWedge.Constructions.covectorWedge a (b + b') = CovectorWedge.Constructions.covectorWedge a b + CovectorWedge.Constructions.covectorWedge a b' := by
  simp only [CovectorWedge.Constructions.covectorWedge, CovectorWedge.Constructions.covectorProduct_add_right, map_add, smul_add]

theorem covectorWedge_smul_left (c : ℂ) (a : E [⋀^Fin p]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    CovectorWedge.Constructions.covectorWedge (c • a) b = c • CovectorWedge.Constructions.covectorWedge a b := by
  ext v
  rw [FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum, ContinuousAlternatingMap.smul_apply,
    FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
  have he : FinAlternatingProduct.Constructions.finBlockProduct (c • a) b = fun w => c * FinAlternatingProduct.Constructions.finBlockProduct a b w := by
    funext w
    simp only [FinAlternatingProduct.Constructions.finBlockProduct, ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_assoc]
  rw [he, WedgeAlternating.Constructions.alternatingSum_smul, smul_eq_mul, mul_smul_comm]

theorem covectorWedge_smul_right (c : ℂ) (a : E [⋀^Fin p]→L[ℝ] ℂ)
    (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    CovectorWedge.Constructions.covectorWedge a (c • b) = c • CovectorWedge.Constructions.covectorWedge a b := by
  ext v
  rw [FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum, ContinuousAlternatingMap.smul_apply,
    FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
  have he : FinAlternatingProduct.Constructions.finBlockProduct a (c • b) = fun w => c * FinAlternatingProduct.Constructions.finBlockProduct a b w := by
    funext w
    simp only [FinAlternatingProduct.Constructions.finBlockProduct, ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_left_comm]
  rw [he, WedgeAlternating.Constructions.alternatingSum_smul, smul_eq_mul, mul_smul_comm]

@[simp] theorem covectorWedge_zero_left (b : E [⋀^Fin q]→L[ℝ] ℂ) :
    CovectorWedge.Constructions.covectorWedge (0 : E [⋀^Fin p]→L[ℝ] ℂ) b = 0 := by
  have h := covectorWedge_smul_left (0 : ℂ) (0 : E [⋀^Fin p]→L[ℝ] ℂ) b
  have h₁ : (0 : ℂ) • (0 : E [⋀^Fin p]→L[ℝ] ℂ) = 0 := by
    ext v
    exact zero_mul (0 : ℂ)
  have h₂ : (0 : ℂ) • CovectorWedge.Constructions.covectorWedge (0 : E [⋀^Fin p]→L[ℝ] ℂ) b = 0 := by
    ext v
    exact zero_mul _
  rw [h₁, h₂] at h
  exact h

@[simp] theorem covectorWedge_zero_right (a : E [⋀^Fin p]→L[ℝ] ℂ) :
    CovectorWedge.Constructions.covectorWedge a (0 : E [⋀^Fin q]→L[ℝ] ℂ) = 0 := by
  have h := covectorWedge_smul_right (0 : ℂ) a (0 : E [⋀^Fin q]→L[ℝ] ℂ)
  have h₁ : (0 : ℂ) • (0 : E [⋀^Fin q]→L[ℝ] ℂ) = 0 := by
    ext v
    exact zero_mul (0 : ℂ)
  have h₂ : (0 : ℂ) • CovectorWedge.Constructions.covectorWedge a (0 : E [⋀^Fin q]→L[ℝ] ℂ) = 0 := by
    ext v
    exact zero_mul _
  rw [h₁, h₂] at h
  exact h

local instance wedgeFormsAddGroup (n : ℕ) : AddCommGroup (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance
local instance wedgeFormsModule (n : ℕ) : Module ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance

def normedWedge (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q) : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (p + q) :=
  Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth (fun x => CovectorWedge.Constructions.covectorWedge (a x) (b x))
    (CovectorWedge.Constructions.contDiff_covectorWedge a.smooth b.smooth)

@[simp] theorem normedWedge_apply (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q) (x : E) :
    normedWedge a b x = CovectorWedge.Constructions.covectorWedge (a x) (b x) := rfl

def normedWedgeLM (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.SmoothForm E (p + q) :=
  LinearMap.mk₂ ℂ normedWedge
    (fun a a' b => by apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext; intro x; exact covectorWedge_add_left (a x) (a' x) (b x))
    (fun c a b => by apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext; intro x; exact covectorWedge_smul_left c (a x) (b x))
    (fun a b b' => by apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext; intro x; exact covectorWedge_add_right (a x) (b x) (b' x))
    (fun c a b => by apply Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ext; intro x; exact covectorWedge_smul_right c (a x) (b x))

@[simp] theorem normedWedgeLM_apply (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q) :
    normedWedgeLM (E := E) p q a b = normedWedge a b := rfl

@[simp] theorem normedWedge_zero_left (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q) :
    normedWedge (0 : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) b = 0 := by
  change normedWedgeLM (E := E) p q 0 b = 0
  rw [map_zero]
  rfl

@[simp] theorem normedWedge_zero_right (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) :
    normedWedge a (0 : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q) = 0 := (normedWedgeLM p q a).map_zero

def normedFormDegreeCast {n m : ℕ} (h : n = m) : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.SmoothForm E m :=
  h ▸ LinearEquiv.refl ℂ (Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n)

@[simp] theorem normedFormDegreeCast_apply {n m : ℕ} (h : n = m) (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) (x : E) :
    normedFormDegreeCast h a x = CovectorWedge.Constructions.covectorDegreeCast h (a x) := by
  subst m
  rfl

theorem normedWedge_d_of_right_closed (a : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E p) (b : Analysis.DifferentialForms.Manifold.Basic.SmoothForm E q)
    {x : E} (hb : Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d b x = 0) :
    Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (normedWedge a b) x =
      normedFormDegreeCast (by omega) (normedWedge (Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a) b) x := by
  rw [normedFormDegreeCast_apply, normedWedge_apply]
  exact WedgeLeibniz.Constructions.extDeriv_covectorWedge_of_right_closed a b x
    (a.smooth.contDiffAt.of_le (by simp)) (b.smooth.contDiffAt.of_le (by simp)) hb

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.WedgeAlgebra
