import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ZeroFormFunctions
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Smooth Scalar Exterior -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior

noncomputable section

section

/-! The actual exterior derivative product rule for scalar functions on the original manifold opens. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {U : Opens M}

theorem smoothScalarOpenZeroForm_d_inChart (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ OAI.Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M)) :
    (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)).extension.inChart e y =
      ofSubsingleton ℝ E ℂ (0 : Fin 1) (fderiv ℝ (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f ∘ e.symm) y) := by
  rw [OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_inChart _ e he hy]
  have heq : (SmoothScalarForm.smoothScalarOpenZeroForm f).extension.inChart e =ᶠ[𝓝 y]
      (fun z => constOfIsEmpty ℝ E (Fin 0) (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm z))) := by
    filter_upwards [(OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hy] with z hz
    exact SmoothScalarForm.smoothScalarOpenZeroForm_inChart f e hz.2
  unfold extDeriv
  rw [heq.fderiv_eq]
  exact extDeriv_constOfIsEmpty (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f ∘ e.symm) y

theorem smoothScalarOpenZeroForm_d_mul (f g : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothScalarForm.smoothComplexOpenFunctionMul f g)) =
      SmoothScalarForm.smoothScalarOpenFormMul f (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm g)) +
        SmoothScalarForm.smoothScalarOpenFormMul g (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)) := by
  apply sub_eq_zero.mp
  apply (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn U _).mpr
  intro e he
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  change (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothScalarForm.smoothComplexOpenFunctionMul f g))).extension.inChart e y =
    (SmoothScalarForm.smoothScalarOpenFormMul f (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm g)) +
      SmoothScalarForm.smoothScalarOpenFormMul g (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f))).extension.inChart e y
  simp only [OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply,
    SmoothScalarForm.smoothScalarOpenFormMul_inChart _ _ e y.property.2,
    smoothScalarOpenZeroForm_d_inChart _ e he y.property]
  have hf := ((SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff f e he).contDiffAt
    ((OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have hg := ((SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff g e he).contDiffAt
    ((OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have hprod : (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (SmoothScalarForm.smoothComplexOpenFunctionMul f g) ∘ e.symm) =ᶠ[𝓝 (y : E)]
      (fun z => OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm z) * OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U g (e.symm z)) := by
    filter_upwards [(OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property] with z hz
    change OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (SmoothScalarForm.smoothComplexOpenFunctionMul f g) (e.symm z) = _
    rw [OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U _ ⟨e.symm z, hz.2⟩,
      OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f ⟨e.symm z, hz.2⟩,
      OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U g ⟨e.symm z, hz.2⟩]
    rfl
  have hder := fderiv_fun_mul hf hg
  simp only [Function.comp_apply] at hder
  rw [hprod.fderiv_eq, hder]
  ext v
  rfl

end

section

/-! The actual exterior derivative of a smooth complex exponential on a manifold open. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap Filter
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {U : Opens M}

def smoothComplexOpenFunctionExp (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) U :=
  ⟨fun x => Complex.exp (f x), Complex.contDiff_exp.contMDiff.comp f.property⟩

theorem smoothScalarOpenZeroForm_d_exp (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (smoothComplexOpenFunctionExp f)) =
      SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp f) (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)) := by
  apply sub_eq_zero.mp
  apply (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn U _).mpr
  intro e he
  rw [map_sub]
  apply sub_eq_zero.mpr
  apply OAI.Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro y
  change (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm (smoothComplexOpenFunctionExp f))).extension.inChart e y =
    (SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp f)
      (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f))).extension.inChart e y
  rw [SmoothScalarForm.smoothScalarOpenFormMul_inChart _ _ e y.property.2,
    smoothScalarOpenZeroForm_d_inChart _ e he y.property,
    smoothScalarOpenZeroForm_d_inChart _ e he y.property]
  have hf := ((SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff f e he).contDiffAt
    ((OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property)).differentiableAt (by simp)
  have hexp : (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (smoothComplexOpenFunctionExp f) ∘ e.symm) =ᶠ[𝓝 (y : E)]
      (fun z => Complex.exp (OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm z))) := by
    filter_upwards [(OAI.Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds y.property] with z hz
    change OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension U (smoothComplexOpenFunctionExp f) (e.symm z) = _
    rw [OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U _ ⟨e.symm z, hz.2⟩,
      OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f ⟨e.symm z, hz.2⟩]
    rfl
  have hd := hf.hasFDerivAt.cexp.fderiv
  simp only [Function.comp_apply] at hd
  rw [hexp.fderiv_eq, hd,
    OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U (smoothComplexOpenFunctionExp f) ⟨e.symm y, y.property.2⟩,
    OAI.Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f ⟨e.symm y, y.property.2⟩]
  ext v
  rfl

end

/-! The actual local connection derivative and its exponential gauge law on original smooth sections. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {U W : Opens M} {n : ℕ}

def openZeroFormMul (A : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 →ₗ[ℂ] OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n where
  toFun a := SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction a) A
  map_add' a b := by
    apply OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    change (SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction (a + b)) A) x =
      (SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction a) A) x + (SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction b) A) x
    rw [SmoothScalarForm.smoothScalarOpenFormMul_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply,
      Open.ZeroFormFunctions.openZeroFormFunction_apply _ x 0, Open.ZeroFormFunctions.openZeroFormFunction_apply _ x 0, Open.ZeroFormFunctions.openZeroFormFunction_apply _ x 0]
    exact add_smul (a x 0) (b x 0) (A x)
  map_smul' z a := by
    apply OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    change (SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction (z • a)) A) x =
      z • (SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction a) A) x
    rw [SmoothScalarForm.smoothScalarOpenFormMul_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply, Open.ZeroFormFunctions.openZeroFormFunction_smul]
    exact mul_smul z (Open.ZeroFormFunctions.openZeroFormFunction a x) (A x)

theorem openZeroFormMul_apply (A : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (a : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) (x : U) :
    openZeroFormMul A a x = a x 0 • A x := by
  change SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction a) A x = _
  rw [SmoothScalarForm.smoothScalarOpenFormMul_apply, Open.ZeroFormFunctions.openZeroFormFunction_apply a x 0]

theorem openZeroFormMul_scalar (A : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    openZeroFormMul A (SmoothScalarForm.smoothScalarOpenZeroForm f) = SmoothScalarForm.smoothScalarOpenFormMul f A := by
  change SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction (SmoothScalarForm.smoothScalarOpenZeroForm f)) A = _
  rw [Open.ZeroFormFunctions.openZeroFormFunction_smoothScalarOpenZeroForm]

theorem openZeroFormMul_restrict (h : W ≤ U) (A : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (a : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (openZeroFormMul A a) =
      openZeroFormMul (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h A) (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) := by
  change OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (SmoothScalarForm.smoothScalarOpenFormMul (Open.ZeroFormFunctions.openZeroFormFunction a) A) = _
  rw [SmoothScalarForm.smoothScalarOpenFormMul_restrict, ← Open.ZeroFormFunctions.openZeroFormFunction_restrict]
  rfl

def openConnectionDerivative (A : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 →ₗ[ℂ] OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 :=
  OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d + openZeroFormMul A

theorem openConnectionDerivative_scalar (A : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    openConnectionDerivative A (SmoothScalarForm.smoothScalarOpenZeroForm f) =
      OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f) + SmoothScalarForm.smoothScalarOpenFormMul f A := by
  change OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f) + openZeroFormMul A (SmoothScalarForm.smoothScalarOpenZeroForm f) = _
  rw [openZeroFormMul_scalar]

theorem openConnectionDerivative_restrict (h : W ≤ U) (A : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (a : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (openConnectionDerivative A a) =
      openConnectionDerivative (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h A) (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) := by
  change OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a + openZeroFormMul A a) = _
  rw [map_add, OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d, openZeroFormMul_restrict]
  rfl

theorem openConnectionDerivative_exp_gauge (A B : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (l f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hA : A = B + OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm l)) :
    openConnectionDerivative B (SmoothScalarForm.smoothScalarOpenZeroForm (SmoothScalarForm.smoothComplexOpenFunctionMul (smoothComplexOpenFunctionExp l) f)) =
      SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp l)
        (openConnectionDerivative A (SmoothScalarForm.smoothScalarOpenZeroForm f)) := by
  rw [openConnectionDerivative_scalar, openConnectionDerivative_scalar, smoothScalarOpenZeroForm_d_mul,
    smoothScalarOpenZeroForm_d_exp, hA]
  apply OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  change ((SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp l) (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f))) x +
    (SmoothScalarForm.smoothScalarOpenFormMul f (SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp l)
      (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm l)))) x) +
    (SmoothScalarForm.smoothScalarOpenFormMul (SmoothScalarForm.smoothComplexOpenFunctionMul (smoothComplexOpenFunctionExp l) f) B) x = _
  simp only [OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.add_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply]
  change ((Complex.exp (l x) • OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f) x) +
    f x • (Complex.exp (l x) • OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm l) x)) +
    (Complex.exp (l x) * f x) • B x =
      Complex.exp (l x) • (OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f) x +
        f x • (B x + OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm l) x))
  module

theorem openConnectionDerivative_exp_gauge_form (A B : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (l : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) (a : OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0)
    (hA : A = B + OAI.Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm l)) :
    openConnectionDerivative B (SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp l) a) =
      SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp l) (openConnectionDerivative A a) := by
  let f := Open.ZeroFormFunctions.openZeroFormFunction a
  have ha : SmoothScalarForm.smoothScalarOpenZeroForm f = a := Open.ZeroFormFunctions.smoothScalarOpenZeroForm_openZeroFormFunction a
  have hp : SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp l) a =
      SmoothScalarForm.smoothScalarOpenZeroForm (SmoothScalarForm.smoothComplexOpenFunctionMul (smoothComplexOpenFunctionExp l) f) :=
    (congrArg (SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp l)) ha).symm.trans
      (SmoothScalarForm.smoothScalarOpenZeroForm_mul (smoothComplexOpenFunctionExp l) f).symm
  exact (congrArg (openConnectionDerivative B) hp).trans
    ((openConnectionDerivative_exp_gauge A B l f hA).trans
      (congrArg (fun b => SmoothScalarForm.smoothScalarOpenFormMul (smoothComplexOpenFunctionExp l) (openConnectionDerivative A b)) ha))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior
