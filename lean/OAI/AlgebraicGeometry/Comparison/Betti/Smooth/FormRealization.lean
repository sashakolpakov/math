import OAI.AlgebraicGeometry.Comparison.Betti.OneFormRealization
import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant
import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication
import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws

/-! # Form Realization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormRealization

noncomputable section

/-!
# Realization in the actual smooth manifold de Rham complex

An algebra of smooth complex-valued functions acts on genuine smooth forms.
The exterior derivative of its zero-forms is a derivation, so the already
constructed algebraic one-form quotient maps to genuine smooth one-forms.
-/

open Set ChartedSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {A : Type*} [CommRing A] [Algebra ℂ A]
  (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a : A, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (φ a))

include hφ in
theorem evaluated_in_chart (a : A) (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    ContDiffAt ℝ ∞ (fun z => φ a (e.symm z)) y := by
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
  exact ((hφ a).contMDiffAt.comp y hs).contDiffAt

def zeroFormMap : A →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 where
  toFun a := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ofSmooth (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (φ a)) (by
    intro e he y hy
    rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart]
    exact ((ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.contDiffAt.comp y
      (evaluated_in_chart φ hφ a e he hy.1)).contDiffWithinAt)
  map_add' a b := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    exact congrArg (fun f : C(M, ℂ) => f x) (map_add φ a b)
  map_smul' c a := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    exact congrArg (fun f : C(M, ℂ) => f x) (map_smul φ c a)

@[simp]
theorem zeroFormMap_apply (a : A) (x : M) (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x) :
    zeroFormMap φ hφ a x v = φ a x := rfl

@[instance_reducible]
def formSectionModule (n : ℕ) : Module A (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) where
  smul a α := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φ a) (hφ a) α
  one_smul α := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext; intro x
    change φ 1 x • α x = α x
    simp
  mul_smul a b α := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext; intro x
    change φ (a * b) x • α x = φ a x • (φ b x • α x)
    simp [mul_smul]
  smul_zero a := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext; intro x
    ext v
    change φ a x * 0 = 0
    exact mul_zero _
  smul_add a α β := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext; intro x
    change φ a x • (α x + β x) = φ a x • α x + φ a x • β x
    exact smul_add _ _ _
  zero_smul α := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext; intro x
    change φ 0 x • α x = 0
    rw [map_zero]
    ext v
    change 0 * α x v = 0
    exact zero_mul _
  add_smul a b α := by
    apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext; intro x
    change φ (a + b) x • α x = φ a x • α x + φ b x • α x
    rw [map_add]
    ext v
    change (φ a x + φ b x) * α x v = φ a x * α x v + φ b x * α x v
    exact add_mul _ _ _

theorem formSectionScalarTower (n : ℕ) :
    letI := formSectionModule φ hφ n
    IsScalarTower ℂ A (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) := by
  let := formSectionModule φ hφ n
  refine ⟨fun c a α => ?_⟩
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change φ (c • a) x • α x = c • (φ a x • α x)
  rw [map_smul]
  exact smul_assoc c (φ a x) (α x)

theorem formSectionSmulComm (n : ℕ) :
    letI := formSectionModule φ hφ n
    SMulCommClass A ℂ (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) := by
  let := formSectionModule φ hφ n
  refine ⟨fun a c α => ?_⟩
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change φ a x • (c • α x) = c • (φ a x • α x)
  exact smul_comm _ _ _

/-- Coordinate formula for the derivative of a realized function. -/
theorem d_zeroFormMap_apply (a : A) (x : M)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, E) x) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ a) x v =
      fderiv ℝ (fun z => φ a ((chartAt E x).symm z)) ((chartAt E x) x)
        (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (chartAt E x) x (v 0)) := by
  change extDeriv ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (φ a)).inChart (chartAt E x))
    ((chartAt E x) x) (fun i => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (chartAt E x) x (v i)) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart, extDeriv_constOfIsEmpty]
  rfl

theorem d_zeroFormMap_one : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ 1) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  rw [d_zeroFormMap_apply]
  simp only [map_one, ContinuousMap.one_apply]
  exact congrArg (fun L : E →L[ℝ] ℂ => L (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (chartAt E x) x (v 0)))
    (congrFun (fderiv_const (𝕜 := ℝ) (E := E) (1 : ℂ)) ((chartAt E x) x))

/-- The ordinary product rule holds in the actual smooth one-form space. -/
theorem d_zeroFormMap_mul (a b : A) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ (a * b)) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φ a) (hφ a) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ b)) +
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φ b) (hφ b) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ a)) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext v
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ (a * b)) x v =
    φ a x * (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ b) x v) +
      φ b x * (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ a) x v)
  rw [d_zeroFormMap_apply, d_zeroFormMap_apply, d_zeroFormMap_apply]
  simp only [map_mul, ContinuousMap.mul_apply]
  have hx := (chartAt E x).map_source (mem_chart_source E x)
  rw [fderiv_fun_mul
    ((evaluated_in_chart φ hφ a (chartAt E x) (chart_mem_atlas E x) hx).differentiableAt (by simp))
    ((evaluated_in_chart φ hφ b (chartAt E x) (chart_mem_atlas E x) hx).differentiableAt (by simp))]
  simp only [(chartAt E x).left_inv (mem_chart_source E x)]
  rfl

def functionDerivation :
    letI := formSectionModule φ hφ 1
    Derivation ℂ A (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) := by
  letI := formSectionModule φ hφ 1
  exact { Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d.comp (zeroFormMap φ hφ) with
    map_one_eq_zero' := d_zeroFormMap_one φ hφ
    leibniz' := d_zeroFormMap_mul φ hφ }

/-- Realization in actual smooth one-forms, with no cohomological hypothesis. -/
def oneFormMap : Algebraic.Forms.Form A 1 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1 := by
  letI := formSectionModule φ hφ 1
  letI := formSectionScalarTower φ hφ 1
  letI := formSectionSmulComm φ hφ 1
  exact OneFormRealization.oneFormRealization (functionDerivation φ hφ)

@[simp]
theorem oneFormMap_symbol (a : Fin 2 → A) :
    oneFormMap φ hφ (Algebraic.Forms.formSymbol A a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (φ (a 0)) (hφ (a 0))
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ (a 1))) := by
  let := formSectionModule φ hφ 1
  let := formSectionScalarTower φ hφ 1
  let := formSectionSmulComm φ hφ 1
  exact OneFormRealization.oneFormRealization_symbol (functionDerivation φ hφ) a

/-- The first square of the actual de Rham complexes commutes. -/
theorem oneFormMap_d0 (a : Algebraic.Forms.Form A 0) :
    oneFormMap φ hφ (Algebraic.Forms.differential A 0 a) =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (zeroFormMap φ hφ (Algebraic.Forms.zeroEvaluation A a)) := by
  let := formSectionModule φ hφ 1
  let := formSectionScalarTower φ hφ 1
  let := formSectionSmulComm φ hφ 1
  exact OneFormRealization.oneFormRealization_d0 (functionDerivation φ hφ) a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FormRealization
