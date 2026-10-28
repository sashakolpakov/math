import OAI.Geometry.Nikodym.Jacobi.ODE

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance nikodymRadialEndTopologicalRing : IsTopologicalRing ((ℝ × E) →L[ℝ] (ℝ × E)) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing ((ℝ × E) →L[ℝ] (ℝ × E)) inferInstance

/-- A linear, nonsingular-in-the-parameter realization of the radial
Jacobi system on one extra real coordinate. -/
def radialGenerator (κ : ℝ) (x : E) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  ((-κ) • (innerSL ℝ x).comp (ContinuousLinearMap.snd ℝ ℝ E)).prod
    ((ContinuousLinearMap.fst ℝ ℝ E).smulRight x)

omit [FiniteDimensional ℝ E] in
@[simp] theorem radialGenerator_apply (κ : ℝ) (x : E) (p : ℝ × E) :
    radialGenerator κ x p = (-κ * ⟪x,p.2⟫,p.1 • x) := rfl

def radialGeneratorLinear (κ : ℝ) : E →L[ℝ] ((ℝ × E) →L[ℝ] (ℝ × E)) :=
  ({ toFun := radialGenerator κ
     map_add' := by
       intro x y
       ext p <;> simp [radialGenerator_apply,inner_add_left,smul_add,mul_add]
     map_smul' := by
       intro c x
       ext p <;> simp [radialGenerator_apply,real_inner_smul_left,smul_smul,mul_comm,mul_left_comm]
   } : E →ₗ[ℝ] ((ℝ × E) →L[ℝ] (ℝ × E))).toContinuousLinearMap

@[simp] theorem radialGeneratorLinear_apply (κ : ℝ) (x : E) :
    radialGeneratorLinear κ x = radialGenerator κ x := rfl

def radialExponential (κ : ℝ) (x : E) : ℝ × E :=
  NormedSpace.exp (radialGenerator κ x) (1,0)

theorem contDiff_radialExponential (κ : ℝ) : ContDiff ℝ ∞ (radialExponential κ : E → ℝ × E) := by
  have hExp : ContDiff ℝ ∞ (fun x : E => NormedSpace.exp (radialGenerator κ x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hg0 : ContDiff ℝ ∞ (fun y : E => radialGeneratorLinear κ y) :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E)
        (F := ((ℝ × E) →L[ℝ] (ℝ × E))) (n := ∞) (radialGeneratorLinear (E := E) κ)
    have hg : ContDiffAt ℝ ∞ (radialGenerator κ : E → ((ℝ × E) →L[ℝ] (ℝ × E))) x := by
      simpa only [radialGeneratorLinear_apply] using! hg0.contDiffAt (x := x)
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) (radialGenerator κ x)).contDiffAt.comp x
      hg
  exact hExp.clm_apply contDiff_const

omit [FiniteDimensional ℝ E] in
@[simp] theorem radialExponential_zero (κ : ℝ) : radialExponential κ (0:E) = (1,0) := by
  have h0 : radialGenerator κ (0:E) = 0 := by ext p <;> simp
  simp [radialExponential,h0,NormedSpace.exp_zero]

def radialExponentialFlow (κ : ℝ) (x : E) (t : ℝ) : ℝ × E :=
  NormedSpace.exp (t • radialGenerator κ x) (1,0)

theorem hasDerivAt_radialExponentialFlow (κ : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (radialExponentialFlow κ x)
      (radialGenerator κ x (radialExponentialFlow κ x t)) t := by
  have hd := (hasDerivAt_exp_smul_const' (radialGenerator κ x) t).clm_apply
    (hasDerivAt_const t (1,0))
  simpa only [radialExponentialFlow,mul_apply_eq_comp,map_zero,add_zero] using! hd

omit [FiniteDimensional ℝ E] in
@[simp] theorem radialExponentialFlow_zero (κ : ℝ) (x : E) :
    radialExponentialFlow κ x 0 = (1,0) := by simp [radialExponentialFlow,NormedSpace.exp_zero]

theorem hasFDerivAt_radialExponential_zero (κ : ℝ) :
    HasFDerivAt (radialExponential κ : E → ℝ × E)
      (ContinuousLinearMap.inr ℝ ℝ E) 0 := by
  have h0 : radialGenerator κ (0:E) = 0 := by ext p <;> simp
  have hg : HasFDerivAt (radialGenerator κ : E → ((ℝ × E) →L[ℝ] (ℝ × E)))
      (radialGeneratorLinear κ) 0 := (radialGeneratorLinear (E := E) κ).hasFDerivAt
  have he : HasFDerivAt NormedSpace.exp
      (1 : ((ℝ × E) →L[ℝ] (ℝ × E)) →L[ℝ] ((ℝ × E) →L[ℝ] (ℝ × E)))
      (radialGenerator κ (0:E)) := by
    rw [h0]
    exact hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := ((ℝ × E) →L[ℝ] (ℝ × E)))
  have hexp : HasFDerivAt (fun x : E => NormedSpace.exp (radialGenerator κ x))
      (radialGeneratorLinear κ) 0 := by
    have hcomp := HasFDerivAt.comp (𝕜 := ℝ) (E := E)
      (F := ((ℝ × E) →L[ℝ] (ℝ × E))) (G := ((ℝ × E) →L[ℝ] (ℝ × E)))
      (f := radialGenerator κ) (g := fun A : (ℝ × E) →L[ℝ] (ℝ × E) => NormedSpace.exp A)
      (0:E) he hg
    simpa using! hcomp
  convert hexp.clm_apply (hasFDerivAt_const (1,0) (0:E)) using 1 <;>
    first | rfl | (ext w <;> simp [radialGenerator_apply])

end OAI.Geometry.Nikodym
