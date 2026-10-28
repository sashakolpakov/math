import OAI.Analysis.HodgeTheory.Decomposition.Pointwise
import Mathlib.Algebra.BigOperators.Ring.List
import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws

/-! # Projectors -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Projectors.Constructions

noncomputable section

section

/-! Finite spectral projectors formed from separating scalar actions.
All constructions are algebraic, so their application to smooth forms preserves smoothness. -/

open scoped BigOperators

variable {ι Z V : Type*}
  [AddCommGroup V] [Module ℂ V]
  (T : Z → Module.End ℂ V) (χ : ι → Z → ℂ) (hχ : Function.Injective χ)

def characterSeparator (i j : ι) (hij : i ≠ j) : Z :=
  Classical.choose (Function.ne_iff.mp (hχ.ne hij))

theorem characterSeparator_spec (i j : ι) (hij : i ≠ j) :
    χ i (characterSeparator χ hχ i j hij) ≠ χ j (characterSeparator χ hχ i j hij) :=
  Classical.choose_spec (Function.ne_iff.mp (hχ.ne hij))

variable [DecidableEq ι]

def spectralFactor (i j : ι) : Module.End ℂ V :=
  if hij : i = j then 1 else
    let z := characterSeparator χ hχ i j hij
    ((χ i z - χ j z)⁻¹) • (T z - χ j z • 1)

def spectralFactorScalar (i j k : ι) : ℂ :=
  if hij : i = j then 1 else
    let z := characterSeparator χ hχ i j hij
    (χ i z - χ j z)⁻¹ * (χ k z - χ j z)

theorem spectralFactor_apply (i j k : ι) (v : V)
    (hv : ∀ z, T z v = χ k z • v) :
    spectralFactor T χ hχ i j v = spectralFactorScalar χ hχ i j k • v := by
  by_cases hij : i = j
  · simp [spectralFactor, spectralFactorScalar, hij]
  · simp only [spectralFactor, spectralFactorScalar, dite_eq_right hij,
      LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hv,
      ← sub_smul, smul_smul]

theorem spectralFactorScalar_self (i j : ι) : spectralFactorScalar χ hχ i j i = 1 := by
  by_cases hij : i = j
  · simp [spectralFactorScalar, hij]
  · simp only [spectralFactorScalar, dite_eq_right hij]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (characterSeparator_spec χ hχ i j hij))

theorem spectralFactorScalar_other (i k : ι) (hik : i ≠ k) :
    spectralFactorScalar χ hχ i k k = 0 := by
  simp [spectralFactorScalar, hik]

variable [Fintype ι]

/-- An ordered product suffices; no commutativity of all endomorphisms is assumed. -/
def spectralProjector (i : ι) : Module.End ℂ V :=
  (Finset.univ.toList.map (spectralFactor T χ hχ i)).prod

omit [Fintype ι] [DecidableEq ι] in
theorem end_listProd_apply (l : List ι) (A : ι → Module.End ℂ V) (c : ι → ℂ)
    (v : V) (hv : ∀ j, A j v = c j • v) :
    (l.map A).prod v = (l.map c).prod • v := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul, hv,
      smul_smul]
    rw [mul_comm]

theorem spectralProjector_apply (i k : ι) (v : V) (hv : ∀ z, T z v = χ k z • v) :
    spectralProjector T χ hχ i v = (∏ j, spectralFactorScalar χ hχ i j k) • v := by
  unfold spectralProjector
  rw [end_listProd_apply _ _ _ v (fun j => spectralFactor_apply T χ hχ i j k v hv),
    Finset.prod_map_toList]

theorem spectralProjector_identity (i : ι) (v : V) (hv : ∀ z, T z v = χ i z • v) :
    spectralProjector T χ hχ i v = v := by
  rw [spectralProjector_apply T χ hχ i i v hv]
  simp only [spectralFactorScalar_self, Finset.prod_const_one, one_smul]

theorem spectralProjector_zero (i k : ι) (hik : i ≠ k) (v : V)
    (hv : ∀ z, T z v = χ k z • v) : spectralProjector T χ hχ i v = 0 := by
  rw [spectralProjector_apply T χ hχ i k v hv]
  have hp : (∏ j, spectralFactorScalar χ hχ i j k) = 0 :=
    Finset.prod_eq_zero (f := fun j => spectralFactorScalar χ hχ i j k)
      (Finset.mem_univ k) (spectralFactorScalar_other χ hχ i k hik)
  rw [hp, zero_smul]

/-- On a spanning family of character subspaces, the constructed projector takes values in
its prescribed subspace. This will be applied to the proved covector spanning theorem. -/
theorem spectralProjector_mem (S : ι → Submodule ℂ V)
    (hS : ∀ k v, v ∈ S k → ∀ z, T z v = χ k z • v)
    (hspan : (⨆ k, S k) = ⊤) (i : ι) (v : V) : spectralProjector T χ hχ i v ∈ S i := by
  have hv : v ∈ ⨆ k, S k := hspan.symm ▸ Submodule.mem_top
  refine Submodule.iSup_induction S (motive := fun v => spectralProjector T χ hχ i v ∈ S i) hv ?_ ?_ ?_
  · intro k v hv
    by_cases hik : i = k
    · subst k
      rwa [spectralProjector_identity T χ hχ i v (hS i v hv)]
    · rw [spectralProjector_zero T χ hχ i k hik v (hS k v hv)]
      exact (S i).zero_mem
  · simp
  · intro x y hx hy
    simpa only [map_add] using (S i).add_mem hx hy

/-- The finite projectors sum to the identity on the proved span of character subspaces. -/
theorem sum_spectralProjector (S : ι → Submodule ℂ V)
    (hS : ∀ k v, v ∈ S k → ∀ z, T z v = χ k z • v)
    (hspan : (⨆ k, S k) = ⊤) (v : V) : (∑ i, spectralProjector T χ hχ i v) = v := by
  have hv : v ∈ ⨆ k, S k := hspan.symm ▸ Submodule.mem_top
  refine Submodule.iSup_induction S
    (motive := fun v => (∑ i, spectralProjector T χ hχ i v) = v) hv ?_ ?_ ?_
  · intro k v hv
    rw [Finset.sum_eq_single k]
    · exact spectralProjector_identity T χ hχ k v (hS k v hv)
    · intro i _ hik
      exact spectralProjector_zero T χ hχ i k hik v (hS k v hv)
    · simp
  · simp
  · intro x y hx hy
    simp only [map_add, Finset.sum_add_distrib, hx, hy]

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

omit [Fintype ι] in
/-- Intertwining each scalar action intertwines each factor of the finite projector. -/
theorem spectralFactor_intertwine (U : Z → Module.End ℂ W) (L : V →ₗ[ℂ] W)
    (hL : ∀ z v, L (T z v) = U z (L v)) (i j : ι) (v : V) :
    L (spectralFactor T χ hχ i j v) = spectralFactor U χ hχ i j (L v) := by
  by_cases hij : i = j
  · simp [spectralFactor, hij]
  · simp only [spectralFactor, dite_eq_right hij, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_smul, map_sub, hL]

/-- The projector commutes with every linear map intertwining the scalar actions. -/
theorem spectralProjector_intertwine (U : Z → Module.End ℂ W) (L : V →ₗ[ℂ] W)
    (hL : ∀ z v, L (T z v) = U z (L v)) (i : ι) (v : V) :
    L (spectralProjector T χ hχ i v) = spectralProjector U χ hχ i (L v) := by
  suffices ∀ (l : List ι) (v : V),
      L ((l.map (spectralFactor T χ hχ i)).prod v) =
        (l.map (spectralFactor U χ hχ i)).prod (L v) from
    this Finset.univ.toList v
  intro l
  induction l with
  | nil => intro v; simp
  | cons j l ih =>
    intro v
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply,
      spectralFactor_intertwine T χ hχ U L hL, ih]

end

/-! Type projectors and the general direct-sum decomposition of genuine smooth forms. -/

open scoped BigOperators _root_.Manifold ContDiff

def bidegreeEquivFin (n : ℕ) : Core.Constructions.Bidegree n ≃ Fin (n + 1) where
  toFun i := ⟨i.val.1, by have h := i.property; omega⟩
  invFun i := ⟨(i.val, n - i.val), by have h := i.isLt; omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have h := i.property; dsimp; omega
  right_inv i := Fin.ext rfl

instance bidegreeFintype (n : ℕ) : Fintype (Core.Constructions.Bidegree n) :=
  Fintype.ofEquiv (Fin (n + 1)) (bidegreeEquivFin n).symm

section Covectors

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- Inverse-scalar action on the actual algebraic alternating covectors. -/
def algebraicAction (n : ℕ) (z : ℂˣ) : Module.End ℂ (E [⋀^Fin n]→ₗ[ℝ] ℂ) where
  toFun f := f.compLinearMap ((ContinuousLinearMap.lsmul ℝ ℂ (↑(z⁻¹) : ℂ)).toLinearMap)
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl

theorem algebraicPureSpace_eigen (n : ℕ) (i : Core.Constructions.Bidegree n)
    (f : E [⋀^Fin n]→ₗ[ℝ] ℂ) (hf : f ∈ Pointwise.Constructions.algebraicPureSpace E n i) (z : ℂˣ) :
    algebraicAction E n z f = Types.Constructions.inverseTypeCharacter i z • f := by
  ext v
  exact hf z⁻¹ v

end Covectors

/-- Each projector is a finite expression in smooth scalar actions. -/
def componentProjection (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (i : Core.Constructions.Bidegree n) :
    Module.End ℂ (X.componentForms n) :=
  spectralProjector (Types.Constructions.componentAction X n) Types.Constructions.inverseTypeCharacter
    (Types.Constructions.inverseTypeCharacter_injective n) i

/-- Taking an actual chart value is a complex-linear map. -/
def componentChartEval (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (C : irreducibleComponents X.carrier)
    (e : OpenPartialHomeomorph (X.componentVariety C).analyticSpace (X.componentVariety C).analyticModel)
    (y : (X.componentVariety C).analyticModel) :
    X.componentForms n →ₗ[ℂ] ((X.componentVariety C).analyticModel [⋀^Fin n]→ₗ[ℝ] ℂ) where
  toFun form := ((form C).val.inChart e y).toAlternatingMap
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl

theorem componentChartEval_action (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (C : irreducibleComponents X.carrier)
    (e : OpenPartialHomeomorph (X.componentVariety C).analyticSpace (X.componentVariety C).analyticModel)
    (he : e ∈ atlas (X.componentVariety C).analyticModel (X.componentVariety C).analyticSpace)
    (y : (X.componentVariety C).analyticModel) (hy : y ∈ e.target)
    (z : ℂˣ) (form : X.componentForms n) :
    componentChartEval X n C e y (Types.Constructions.componentAction X n z form) =
      algebraicAction (X.componentVariety C).analyticModel n z
        (componentChartEval X n C e y form) := by
  change ((DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z (form C).val).inChart e y).toAlternatingMap = _
  rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart z (form C).val e he hy]
  rfl

theorem componentProjection_inChart (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (C : irreducibleComponents X.carrier)
    (e : OpenPartialHomeomorph (X.componentVariety C).analyticSpace (X.componentVariety C).analyticModel)
    (he : e ∈ atlas (X.componentVariety C).analyticModel (X.componentVariety C).analyticSpace)
    (y : (X.componentVariety C).analyticModel) (hy : y ∈ e.target)
    (i : Core.Constructions.Bidegree n) (form : X.componentForms n) :
    componentChartEval X n C e y (componentProjection X n i form) =
      spectralProjector (algebraicAction (X.componentVariety C).analyticModel n)
        Types.Constructions.inverseTypeCharacter (Types.Constructions.inverseTypeCharacter_injective n) i
        (componentChartEval X n C e y form) :=
  spectralProjector_intertwine (Types.Constructions.componentAction X n) Types.Constructions.inverseTypeCharacter
    (Types.Constructions.inverseTypeCharacter_injective n) (algebraicAction (X.componentVariety C).analyticModel n)
    (componentChartEval X n C e y) (componentChartEval_action X n C e he y hy) i form

/-- Chartwise purity is exactly membership in the already constructed algebraic pure spaces. -/
theorem pureFormsAt_iff_chartEval (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i : Core.Constructions.Bidegree n) (form : X.componentForms n) :
    form ∈ Core.Constructions.pureFormsAt X n i ↔ ∀ C,
      ∀ e ∈ atlas (X.componentVariety C).analyticModel (X.componentVariety C).analyticSpace,
      ∀ y ∈ e.target, componentChartEval X n C e y form ∈
        Pointwise.Constructions.algebraicPureSpace (X.componentVariety C).analyticModel n i := by
  rcases i with ⟨⟨p, q⟩, h⟩
  subst n
  change form ∈ X.componentPureForms p q ↔ _
  rw [X.mem_componentPureForms_iff]
  rfl

/-- The finite smooth projector really takes values in its stated pure type. -/
theorem componentProjection_pure (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (i : Core.Constructions.Bidegree n) (form : X.componentForms n) :
    componentProjection X n i form ∈ Core.Constructions.pureFormsAt X n i := by
  rw [pureFormsAt_iff_chartEval]
  intro C e he y hy
  rw [componentProjection_inChart X n C e he y hy]
  exact spectralProjector_mem _ Types.Constructions.inverseTypeCharacter (Types.Constructions.inverseTypeCharacter_injective n)
    (Pointwise.Constructions.algebraicPureSpace (X.componentVariety C).analyticModel n)
    (algebraicPureSpace_eigen (X.componentVariety C).analyticModel n)
    (Pointwise.Constructions.algebraicPureSpace_span (X.componentVariety C).analyticModel n) i _

/-- The smooth type projectors sum to the identity in every degree. -/
theorem sum_componentProjection (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    (form : X.componentForms n) : (∑ i : Core.Constructions.Bidegree n, componentProjection X n i form) = form := by
  funext C
  apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt (X.componentVariety C).analyticModel x
  have he : e ∈ atlas (X.componentVariety C).analyticModel (X.componentVariety C).analyticSpace :=
    chart_mem_atlas _ x
  have hx : x ∈ e.source := mem_chart_source _ x
  have hy : e x ∈ e.target := e.map_source hx
  have hval : componentChartEval X n C e (e x)
      (∑ i : Core.Constructions.Bidegree n, componentProjection X n i form) = componentChartEval X n C e (e x) form := by
    rw [map_sum]
    simp_rw [componentProjection_inChart X n C e he (e x) hy]
    exact sum_spectralProjector _ Types.Constructions.inverseTypeCharacter (Types.Constructions.inverseTypeCharacter_injective n)
      (Pointwise.Constructions.algebraicPureSpace (X.componentVariety C).analyticModel n)
      (algebraicPureSpace_eigen (X.componentVariety C).analyticModel n)
      (Pointwise.Constructions.algebraicPureSpace_span (X.componentVariety C).analyticModel n) _
  have hchart : (((∑ i : Core.Constructions.Bidegree n, componentProjection X n i form) C).val.inChart e (e x)) =
      (form C).val.inChart e (e x) := by
    ext v
    exact congrArg (fun a : (X.componentVariety C).analyticModel [⋀^Fin n]→ₗ[ℝ] ℂ => a v) hval
  have h := congrArg (fun a => a.compContinuousLinearMap (DifferentialForms.Manifold.Charts.chartTangentMap e x)) hchart
  rw [DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ e he hx,
    DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_comp_chartTangentMap _ e he hx] at h
  exact h

/-- All genuine smooth forms are sums of their pure-type components. -/
theorem pureFormsAt_span (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    (⨆ i : Core.Constructions.Bidegree n, Core.Constructions.pureFormsAt X n i) = ⊤ := by
  apply top_unique
  intro form _
  rw [← sum_componentProjection X n form]
  apply Submodule.sum_mem
  intro i _
  exact le_iSup (Core.Constructions.pureFormsAt X n) i (componentProjection_pure X n i form)

/-- The usual type decomposition on smooth forms, before passage to cohomology. -/
theorem smoothForms_directSum (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    DirectSum.IsInternal (Core.Constructions.pureFormsAt X n) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (Types.Constructions.pureFormsAt_iSupIndep X n) (pureFormsAt_span X n)

end

end OAI.Analysis.HodgeTheory.Decomposition.Projectors.Constructions
