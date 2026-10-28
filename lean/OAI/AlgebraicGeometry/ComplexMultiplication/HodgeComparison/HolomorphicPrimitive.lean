import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Holomorphic Primitive -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction

noncomputable section

/-! Holomorphic primitives of exact one-forms, for the HodgeComparison Hodge decomposition. -/

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- A real derivative of type (1,0) is the restriction of a complex derivative. -/
theorem complexDifferentiableAt_of_holomorphic_derivative
    {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (ht : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0
      (ContinuousAlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) (fderiv ℝ f x))) :
    DifferentiableAt ℂ f x := by
  let D := fderiv ℝ f x
  have hsmul (z : ℂ) (v : E) : D (z • v) = z • D v := by
    by_cases hz : z = 0
    · simp [hz]
    · have h := ht (Units.mk0 z hz) (fun _ => v)
      change D (z • v) = OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 (Units.mk0 z hz) * D v at h
      simpa only [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter,
        Units.val_mk0, pow_one, pow_zero, mul_one, smul_eq_mul] using h
  let DC : E →L[ℂ] ℂ :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := hsmul
      cont := D.continuous }
  have hres : DC.restrictScalars ℝ = D := by ext v; rfl
  exact (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt hres).differentiableAt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Evaluate a nullary covector to obtain its scalar function. -/
def zeroFormScalar (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (x : M) : ℂ := form x 0

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- The scalar coordinate expression is just composition with the inverse chart. -/
theorem zeroFormScalar_inChart (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (e : OpenPartialHomeomorph M E) :
    (fun y => form.val.inChart e y 0) = zeroFormScalar form ∘ e.symm := by
  funext y
  change form (e.symm y) _ = form (e.symm y) 0
  congr 1
  exact Subsingleton.elim _ _

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- Reconstruct the nullary covector from its scalar coordinate expression. -/
theorem zeroFormScalar_reconstruct (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (e : OpenPartialHomeomorph M E) :
    form.val.inChart e = fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0)
      (zeroFormScalar form (e.symm y)) := by
  funext y
  ext v
  change form (e.symm y) _ = form (e.symm y) 0
  congr 1
  exact Subsingleton.elim _ _

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem zeroFormScalar_contDiffAt_inChart (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) :
    ContDiffAt ℝ ∞ (zeroFormScalar form ∘ e.symm) y := by
  rw [← zeroFormScalar_inChart form e]
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).symm.contDiff.comp_contDiffAt y
    (OAI.Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart form.property e he hy)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A scalar primitive whose differential has type (1,0) is holomorphic in charts. -/
theorem zeroFormScalar_complexDifferentiableAt_inChart
    (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (ht : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form).val)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E}
    (hy : y ∈ e.target) :
    DifferentiableAt ℂ (zeroFormScalar form ∘ e.symm) y := by
  apply complexDifferentiableAt_of_holomorphic_derivative
    ((zeroFormScalar_contDiffAt_inChart form e he hy).differentiableAt (by simp))
  have h := ht e he y hy
  rw [OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart form e he hy, zeroFormScalar_reconstruct,
    extDeriv_constOfIsEmpty] at h
  exact h

variable [IsManifold 𝓘(ℂ, E) ∞ M]

/-- Such a primitive is holomorphic on the actual complex manifold. -/
theorem zeroFormScalar_mdifferentiable
    (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (ht : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form).val) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (zeroFormScalar form) := by
  intro x
  let e := chartAt E x
  have hex : x ∈ e.source := mem_chart_source E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hd := zeroFormScalar_complexDifferentiableAt_inChart form ht e he (e.map_source hex)
  have hediff : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) e x :=
    (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, E)) (n := ∞) he) hex).mdifferentiableAt
        (by simp)
  have hc := hd.mdifferentiableAt.comp x hediff
  have heq : (zeroFormScalar form ∘ e.symm) ∘ e =ᶠ[𝓝 x] zeroFormScalar form := by
    filter_upwards [e.open_source.mem_nhds hex] with y hy
    exact congrArg (zeroFormScalar form) (e.left_inv hy)
  exact heq.mdifferentiableAt_iff.mp hc

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
/-- A locally constant scalar function has zero exterior derivative. -/
theorem d_zeroForm_eq_zero_of_locallyConstant
    (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (hf : IsLocallyConstant (zeroFormScalar form)) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 := by
  apply OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt E x
  have hex : x ∈ e.source := mem_chart_source E x
  have hcont : ContinuousAt e.symm (e x) := e.symm.continuousAt (e.map_source hex)
  have heq : zeroFormScalar form ∘ e.symm =ᶠ[𝓝 (e x)]
      fun _ => zeroFormScalar form x := by
    change ∀ᶠ y in 𝓝 (e x), zeroFormScalar form (e.symm y) = zeroFormScalar form x
    have h := hcont.tendsto.eventually (hf.eventually_eq (e.symm (e x)))
    simpa only [Function.comp_apply, e.left_inv hex] using h
  have hder : fderiv ℝ (zeroFormScalar form ∘ e.symm) (e x) = 0 := by
    rw [heq.fderiv_eq]
    exact fderiv_const_apply _
  ext v
  change extDeriv (form.val.inChart e) (e x)
    (fun i => OAI.Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x (v i)) = 0
  rw [zeroFormScalar_reconstruct, extDeriv_constOfIsEmpty]
  change fderiv ℝ (zeroFormScalar form ∘ e.symm) (e x) _ = 0
  rw [hder]
  rfl

variable [CompactSpace M]

/-- On a compact complex manifold an exact holomorphic one-form vanishes. -/
theorem d_zeroForm_eq_zero_of_holomorphic
    (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (ht : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form).val) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 :=
  d_zeroForm_eq_zero_of_locallyConstant form
    (zeroFormScalar_mdifferentiable form ht).isLocallyConstant

/-- A holomorphic closed one-form with zero de Rham class is zero. -/
theorem holomorphic_oneForm_eq_zero_of_class_eq_zero
    (form : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1)
    (ht : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 form.val.val)
    (hc : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 form = 0) : form = 0 := by
  obtain ⟨primitive, hp⟩ := (OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff E M 1 form).mp hc
  change OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive = form.val at hp
  apply Subtype.ext
  change form.val = 0
  rw [← hp]
  apply d_zeroForm_eq_zero_of_holomorphic
  simpa only [hp] using ht

/-- The class map is injective on holomorphic closed one-forms. -/
theorem holomorphic_formClass_injective :
    Function.Injective (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureFormClass E M 1 0) := by
  intro form other h
  have hc : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 (form.val - other.val) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact h
  have ht : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0 (form.val - other.val).val.val :=
    (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms E M 1 0).sub_mem form.property other.property
  have hz := holomorphic_oneForm_eq_zero_of_class_eq_zero (form.val - other.val) ht hc
  exact Subtype.ext (sub_eq_zero.mp hz)

/-- Conjugation reduces exact antiholomorphic one-forms to the holomorphic case. -/
theorem d_zeroForm_eq_zero_of_antiholomorphic
    (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0)
    (ht : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form).val) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 := by
  have hconj : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 0
      (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Conjugation.CM.Construction.conjugateSmoothForm form)).val := by
    rw [Conjugation.CM.Construction.d_conjugateSmoothForm]
    apply (OAI.Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mpr
    exact Conjugation.CM.Construction.conjugateRawForm_antiholomorphic _
      ((OAI.Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp ht)
  have hz := d_zeroForm_eq_zero_of_holomorphic (Conjugation.CM.Construction.conjugateSmoothForm form) hconj
  rw [Conjugation.CM.Construction.d_conjugateSmoothForm] at hz
  have h := congrArg Conjugation.CM.Construction.conjugateSmoothForm hz
  simpa only [Conjugation.CM.Construction.conjugateSmoothForm_involutive, Conjugation.CM.Construction.conjugateSmoothForm_zero] using h

/-- A vanishing antiholomorphic de Rham class has zero representative. -/
theorem antiholomorphic_oneForm_eq_zero_of_class_eq_zero
    (form : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 1)
    (ht : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 form.val.val)
    (hc : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 form = 0) : form = 0 := by
  obtain ⟨primitive, hp⟩ := (OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff E M 1 form).mp hc
  change OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d primitive = form.val at hp
  apply Subtype.ext
  change form.val = 0
  rw [← hp]
  apply d_zeroForm_eq_zero_of_antiholomorphic
  simpa only [hp] using ht

/-- The antiholomorphic class map is injective as well. -/
theorem antiholomorphic_formClass_injective :
    Function.Injective (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureFormClass E M 0 1) := by
  intro form other h
  have hc : OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 (form.val - other.val) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact h
  have ht : OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 1 (form.val - other.val).val.val :=
    (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms E M 0 1).sub_mem form.property other.property
  have hz := antiholomorphic_oneForm_eq_zero_of_class_eq_zero (form.val - other.val) ht hc
  exact Subtype.ext (sub_eq_zero.mp hz)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction
