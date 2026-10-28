import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultZeroForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms

/-! # Dolbeault Open -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOpen

noncomputable section

section

/-! An actual smooth zero-form in the Dolbeault kernel gives an original holomorphic function section. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem contDiffOn_complex_iff_dolbeault_zero
    {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℂ ∞ f U ↔
      ∀ x ∈ U, Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (fun y => constOfIsEmpty ℝ E (Fin 0) (f y)) x = 0 := by
  rw [DolbeaultZeroForms.extDerivDoublePrime_zeroForm_eq_zero_on_open_iff hU (hf.differentiableOn (by simp))]
  constructor
  · intro h
    exact h.differentiableOn (by simp)
  · exact Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn hU

def holomorphicFunctionOfDbarZero {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0)
    (h : ∀ x : U, Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form.extension x = 0) :
    Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) :=
  ⟨fun x => form x 0, by
    have hs : ContDiffOn ℂ ∞ (AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms.zeroFormScalarExtension form) (U : Set E) := by
      apply (contDiffOn_complex_iff_dolbeault_zero U.isOpen (AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms.zeroFormScalarExtension_smooth form)).mpr
      intro x hx
      rw [AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms.zeroFormScalarExtension_reconstruct]
      exact h ⟨x, hx⟩
    intro x
    have hc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ∞ (AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms.zeroFormScalarExtension form) (x : E) :=
      (hs.contDiffAt (U.isOpen.mem_nhds x.property)).contMDiffAt
    have ht := (contMDiffAt_subtype_iff (U := U) (x := x)).mpr hc
    simpa only [AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms.zeroFormScalarExtension_apply] using ht⟩

theorem holomorphicFunctionOfDbarZero_apply {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0)
    (h : ∀ x : U, Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form.extension x = 0) (x : U) :
    holomorphicFunctionOfDbarZero form h x = form x 0 := rfl

end

section

/-! Original holomorphic function sections are exactly actual smooth zero-forms in the Dolbeault kernel. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem holomorphicOpenExtend_contDiffOn {U : Opens E}
    (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    ContDiffOn ℂ ∞ (Holomorphic.OpenExtension.holomorphicOpenExtend g) (U : Set E) :=
  (Holomorphic.OpenExtension.holomorphicOpenExtend_contMDiffOn g).contDiffOn

def holomorphicFunctionZeroForm {U : Opens E} (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw U (fun x => constOfIsEmpty ℝ E (Fin 0) (Holomorphic.OpenExtension.holomorphicOpenExtend g x))
    ((constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp_contDiffOn
      ((holomorphicOpenExtend_contDiffOn g).restrict_scalars ℝ))

theorem holomorphicFunctionZeroForm_apply {U : Opens E}
    (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) (x : U) (v : Fin 0 → E) :
    holomorphicFunctionZeroForm g x v = g x :=
  Holomorphic.OpenExtension.holomorphicOpenExtend_apply g x x.property

theorem holomorphicFunctionZeroForm_dbar {U : Opens E}
    (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) (x : U) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (holomorphicFunctionZeroForm g).extension x = 0 := by
  have he := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_ofRaw_eventuallyEq
    (fun y => constOfIsEmpty ℝ E (Fin 0) (Holomorphic.OpenExtension.holomorphicOpenExtend g y))
    ((constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp_contDiffOn
      ((holomorphicOpenExtend_contDiffOn g).restrict_scalars ℝ)) x
  have hc := ((holomorphicOpenExtend_contDiffOn g).differentiableOn (by simp) x x.property).differentiableAt
    (U.isOpen.mem_nhds x.property)
  have hz := (DolbeaultZeroForms.extDerivDoublePrime_zeroForm_eq_zero_iff (hc.restrictScalars ℝ)).mpr hc
  have heD : fderiv ℝ (holomorphicFunctionZeroForm g).extension (x : E) =
      fderiv ℝ (fun y => constOfIsEmpty ℝ E (Fin 0) (Holomorphic.OpenExtension.holomorphicOpenExtend g y)) (x : E) :=
    he.fderiv_eq
  change ContinuousAlternatingMap.alternatizeUncurryFin
    (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E 0)
      (fderiv ℝ (holomorphicFunctionZeroForm g).extension (x : E))) = 0
  rw [heD]
  exact hz

variable [FiniteDimensional ℂ E]

theorem holomorphicFunctionZeroForm_ofDbarZero {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0)
    (h : ∀ x : U, Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form.extension x = 0) :
    holomorphicFunctionZeroForm (holomorphicFunctionOfDbarZero form h) = form := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  rw [holomorphicFunctionZeroForm_apply, holomorphicFunctionOfDbarZero_apply]
  congr 1
  exact Subsingleton.elim _ _

theorem holomorphicFunctionOfDbarZero_zeroForm {U : Opens E}
    (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    holomorphicFunctionOfDbarZero (holomorphicFunctionZeroForm g) (holomorphicFunctionZeroForm_dbar g) = g := by
  apply ContMDiffMap.ext
  intro x
  rw [holomorphicFunctionOfDbarZero_apply, holomorphicFunctionZeroForm_apply]

omit [FiniteDimensional ℂ E] in
theorem holomorphicFunctionZeroForm_restrict {U V : Opens E} (h : V ≤ U)
    (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))
    (g' : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := V))
    (hg : ∀ x : V, g' x = g (Opens.inclusion h x)) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h (holomorphicFunctionZeroForm g) = holomorphicFunctionZeroForm g' := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change holomorphicFunctionZeroForm g (Opens.inclusion h x) v = holomorphicFunctionZeroForm g' x v
  rw [holomorphicFunctionZeroForm_apply, holomorphicFunctionZeroForm_apply, hg]

end

/-! The actual antiholomorphic differential on smooth open-domain forms. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {n : ℕ}

theorem contDiffOn_extDerivDoublePrime {U : Set E} (hU : IsOpen U)
    {form : Analysis.DifferentialForms.Manifold.Basic.RawForm E n} (hf : ContDiffOn ℝ ∞ form U) :
    ContDiffOn ℝ ∞ (Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form) U := by
  change ContDiffOn ℝ ∞
    ((alternatizeUncurryFinCLM ℝ E ℂ) ∘
      ((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)).restrictScalars ℝ) ∘ fderiv ℝ form) U
  exact ((hf.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousLinearMap_comp
    ((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)).restrictScalars ℝ)).continuousLinearMap_comp
    (alternatizeUncurryFinCLM ℝ E ℂ)

theorem extDerivDoublePrime_add {a b : Analysis.DifferentialForms.Manifold.Basic.RawForm E n} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (a + b) x = Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x + Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime b x := by
  unfold Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
  rw [fderiv_add ha hb, map_add, alternatizeUncurryFin_add]

theorem extDerivDoublePrime_complex_smul (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.RawForm E n) (x : E) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (c • a) x = c • Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x := by
  unfold Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
  rw [fderiv_const_smul_field (𝕜 := ℝ) (f := a) c]
  change alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (c • fderiv ℝ a x)) = _
  rw [map_smul, alternatizeUncurryFin_smul]

def openDolbeaultD {U : Opens E} (n : ℕ) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1) where
  toFun form := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw U (Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form.extension)
    (contDiffOn_extDerivDoublePrime U.isOpen form.smooth)
  map_add' a b := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    change Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (a + b).extension x =
      Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a.extension x + Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime b.extension x
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_add]
    exact extDerivDoublePrime_add
      ((a.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))
      ((b.smooth.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp))
  map_smul' c a := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    change Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (c • a).extension x = c • Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a.extension x
    rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_smul, extDerivDoublePrime_complex_smul]

theorem openDolbeaultD_apply {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) (x : U) :
    openDolbeaultD n form x = Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form.extension x := rfl

theorem openDolbeaultD_zero_iff {U : Opens E} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    openDolbeaultD n form = 0 ↔ ∀ x : U, Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form.extension x = 0 := by
  constructor
  · intro h x
    exact congrArg (fun a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1) => a x) h
  · intro h
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOpen
