import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.VectorCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ManifoldPurity

/-! # Coefficient Mem -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientMem

noncomputable section

section

/-! Actual holomorphic forms on an open domain have holomorphic coefficient functions,
and pure holomorphic coefficient functions give actual holomorphic forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {U : Opens E} {n : ℕ}

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem open_form_coefficients_holomorphic [FiniteDimensional ℂ E] (a : DeRhamComplex.forms E U n) :
    ContDiffOn ℂ ∞ ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm (DeRhamComplex.inclusion E U n a)).extension
      (U : Set E) := by
  intro y hy
  let x : U := ⟨y, hy⟩
  have h := VectorCoefficients.form_coefficients_holomorphic a (chartAt E x) (chart_mem_atlas E x)
  rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.open_chartAt_target] at h
  apply h.congr _ y hy
  intro z hz
  change Analysis.DifferentialForms.Manifold.OpenD.openFormExtension U ((Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv U n).symm
    (DeRhamComplex.inclusion E U n a).val) z = (DeRhamComplex.inclusion E U n a).val.inChart (chartAt E x) z
  rw [Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply U _ ⟨z, hz⟩]
  exact Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_symm_eq_inChart _ _ (chart_mem_atlas E x) ⟨z, hz⟩

theorem open_coefficients_mem_forms (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n)
    (hp : ∀ x : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (a x))
    (hc : ContDiffOn ℂ ∞ a.extension (U : Set E)) :
    (⟨Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n a,
      (Open.ManifoldPurity.Holomorphic.smoothOpenManifoldEquiv_pure_iff (p := n) (q := 0) a).mpr hp⟩ :
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E U n 0) ∈ DeRhamComplex.forms E U n := by
  apply (ChartCoefficients.mem_forms_iff_coefficients_complex _).mpr
  intro e he y hy
  have hyU : y ∈ U := by rwa [Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target e he] at hy
  have hs : ContDiffOn ℂ ∞ ((Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv U n a).inChart e) (U : Set E) :=
    hc.congr (fun z hz => Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_inChart a e he hz)
  exact (hs.contDiffAt (U.isOpen.mem_nhds hyU)).differentiableAt (by simp)

end

section

/-! An independent coefficient definition of holomorphic forms on an open domain. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

def holomorphicOpenCoefficients (U : Opens E) (n : ℕ) :
    Submodule ℂ (U → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) where
  carrier := {f | (∀ x : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (f x)) ∧
    ContDiffOn ℂ ∞ (Analysis.DifferentialForms.Manifold.OpenD.openFormExtension U f) (U : Set E)}
  zero_mem' := by
    constructor
    · intro x
      exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).zero_mem
    · rw [Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_zero]
      exact contDiffOn_const
  add_mem' := by
    rintro f g ⟨hf, hfc⟩ ⟨hg, hgc⟩
    constructor
    · intro x
      exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).add_mem (hf x) (hg x)
    · rw [Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_add]
      exact hfc.add hgc
  smul_mem' := by
    rintro c f ⟨hf, hfc⟩
    constructor
    · intro x
      exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).smul_mem c (hf x)
    · rw [Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_smul]
      exact hfc.const_smul c

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def holomorphicCoefficientsSmoothForm {U : Opens E} {n : ℕ}
    (f : holomorphicOpenCoefficients U n) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n :=
  ⟨f.val, f.property.2.restrict_scalars ℝ⟩

def holomorphicCoefficientsToForm (U : Opens E) (n : ℕ) :
    holomorphicOpenCoefficients U n →ₗ[ℂ] DeRhamComplex.forms E U n where
  toFun f :=
    ⟨⟨Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n (holomorphicCoefficientsSmoothForm f),
      (Open.ManifoldPurity.Holomorphic.smoothOpenManifoldEquiv_pure_iff (p := n) (q := 0) _).mpr f.property.1⟩,
      open_coefficients_mem_forms (holomorphicCoefficientsSmoothForm f) f.property.1 f.property.2⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).map_add
      (holomorphicCoefficientsSmoothForm f) (holomorphicCoefficientsSmoothForm g)
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).map_smul c (holomorphicCoefficientsSmoothForm f)

theorem holomorphicCoefficientsToForm_inclusion (U : Opens E) (n : ℕ)
    (f : holomorphicOpenCoefficients U n) :
    DeRhamComplex.inclusion E U n (holomorphicCoefficientsToForm U n f) =
      Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n (holomorphicCoefficientsSmoothForm f) := rfl

end

section

/-! Coordinate coefficients and the actual kernel of d-double-prime are canonically equivalent. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def formToHolomorphicCoefficients (U : Opens E) (n : ℕ) :
    DeRhamComplex.forms E U n →ₗ[ℂ] holomorphicOpenCoefficients U n where
  toFun a :=
    ⟨((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm (DeRhamComplex.inclusion E U n a)).val,
      Open.ManifoldPurity.Holomorphic.smoothOpenManifoldEquiv_symm_pure (p := n) (q := 0)
        (DeRhamComplex.inclusion E U n a) a.val.hasManifoldBidegree,
      open_form_coefficients_holomorphic a⟩
  map_add' a b := by
    apply Subtype.ext
    exact congrArg (fun f : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n => f.val)
      ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm.map_add (DeRhamComplex.inclusion E U n a) (DeRhamComplex.inclusion E U n b))
  map_smul' c a := by
    apply Subtype.ext
    exact congrArg (fun f : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n => f.val)
      ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm.map_smul c (DeRhamComplex.inclusion E U n a))

theorem coefficientsToForm_formToCoefficients (U : Opens E) (n : ℕ) (a : DeRhamComplex.forms E U n) :
    holomorphicCoefficientsToForm U n (formToHolomorphicCoefficients U n a) = a := by
  apply Subtype.ext
  apply Subtype.ext
  exact (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).apply_symm_apply _

theorem formToCoefficients_coefficientsToForm (U : Opens E) (n : ℕ)
    (a : holomorphicOpenCoefficients U n) :
    formToHolomorphicCoefficients U n (holomorphicCoefficientsToForm U n a) = a := by
  apply Subtype.ext
  exact congrArg (fun f : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n => f.val) ((Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n).symm_apply_apply
    (holomorphicCoefficientsSmoothForm a))

def holomorphicCoefficientsEquivForms (U : Opens E) (n : ℕ) :
    holomorphicOpenCoefficients U n ≃ₗ[ℂ] DeRhamComplex.forms E U n where
  toLinearMap := holomorphicCoefficientsToForm U n
  invFun := formToHolomorphicCoefficients U n
  left_inv := formToCoefficients_coefficientsToForm U n
  right_inv := coefficientsToForm_formToCoefficients U n

theorem holomorphicCoefficientsEquivForms_inclusion (U : Opens E) (n : ℕ)
    (a : holomorphicOpenCoefficients U n) :
    DeRhamComplex.inclusion E U n (holomorphicCoefficientsEquivForms U n a) =
      Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U n (holomorphicCoefficientsSmoothForm a) := rfl

end

/-! Holomorphic vector-valued functions on an actual open domain, with pointwise operations. -/

open _root_.TopologicalSpace
open scoped ContDiff

def openCoefficientExtension {E F : Type} [TopologicalSpace E] [Zero F]
    (U : Opens E) (f : U → F) (x : E) : F := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else 0

theorem openCoefficientExtension_apply {E F : Type} [TopologicalSpace E] [Zero F]
    (U : Opens E) (f : U → F) (x : U) : openCoefficientExtension U f x = f x := by
  simp [openCoefficientExtension, x.property]

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

def holomorphicSections (U : Opens E) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] :
    Submodule ℂ (U → F) where
  carrier := {f | ContDiffOn ℂ ∞ (openCoefficientExtension U f) (U : Set E)}
  zero_mem' := by
    apply contDiffOn_const.congr
    intro x hx
    exact openCoefficientExtension_apply U (0 : U → F) ⟨x, hx⟩
  add_mem' := by
    intro f g hf hg
    apply (hf.add hg).congr
    intro x hx
    simp only [openCoefficientExtension_apply U _ ⟨x, hx⟩, Pi.add_apply]
  smul_mem' := by
    intro c f hf
    apply (hf.const_smul c).congr
    intro x hx
    simp only [openCoefficientExtension_apply U _ ⟨x, hx⟩, Pi.smul_apply]

def holomorphicSectionMap (U : Opens E) (L : F →L[ℂ] G) :
    holomorphicSections U F →ₗ[ℂ] holomorphicSections U G where
  toFun f := ⟨fun x => L (f.val x), by
    have hL : ContDiff ℂ ∞ L := ContinuousLinearMap.contDiff _
    apply (hL.comp_contDiffOn f.property).congr
    intro x hx
    simp only [Function.comp_apply, openCoefficientExtension_apply U _ ⟨x, hx⟩]⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact L.map_add _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact L.map_smul c _

theorem holomorphicSectionMap_apply (U : Opens E) (L : F →L[ℂ] G)
    (f : holomorphicSections U F) (x : U) :
    (holomorphicSectionMap U L f).val x = L (f.val x) := rfl

def holomorphicSectionEquiv (U : Opens E) (L : F ≃L[ℂ] G) :
    holomorphicSections U F ≃ₗ[ℂ] holomorphicSections U G where
  toLinearMap := holomorphicSectionMap U L.toContinuousLinearMap
  invFun := holomorphicSectionMap U L.symm.toContinuousLinearMap
  left_inv f := by
    apply Subtype.ext
    funext x
    exact L.symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    funext x
    exact L.apply_symm_apply _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientMem
