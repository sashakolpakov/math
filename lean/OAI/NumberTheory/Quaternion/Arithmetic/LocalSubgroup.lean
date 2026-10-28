import OAI.NumberTheory.Quaternion.Arithmetic.ExponentialProducts

/-! # Local Subgroup -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalSubgroup

noncomputable section

section

/-! An inverse-function argument inside the tangent subspace. A continuous
linear projection makes the parameter map globally defined; on the small
subgroup logarithms it agrees with the identity. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

attribute [local instance] TangentBracket.finiteClosedPrimeNontriviallyNormedField
attribute [local instance 50] OrderedProductDerivative.finitePrimeNormedAlgebra

variable {F : Type} [Field F] [NumberField F]

theorem exp_eventually_mem_of_local_parameterization (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    (W : Submodule (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A) [CompleteSpace W]
    (P : A →L[TangentBracket.closedPrimeSubfield (v.adicCompletion F)] W)
    (hP : ∀ x : W, P (x : A) = x)
    (H : Submonoid A)
    (hlog : ∀ g ∈ H, g ∈ SpanLocal.finiteLogDomain v A → SpanLocal.finiteLocalLog v A g ∈ W)
    (f : W → A) (hf0 : f 0 = 1)
    (hf : HasStrictFDerivAt f W.subtypeL 0)
    (hfH : ∀ᶠ x in 𝓝 (0 : W), f x ∈ H) :
    ∀ᶠ (x : W) in 𝓝 (0 : W), NormedSpace.exp (x : A) ∈ H := by
  let : NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A := OrderedProductDerivative.finitePrimeNormedSpace v A
  let q : W → W := fun x => P (SpanLocal.finiteLocalLog v A (f x))
  have hlogf : HasStrictFDerivAt (fun x => SpanLocal.finiteLocalLog v A (f x)) W.subtypeL 0 := by
    have hl : HasStrictFDerivAt (SpanLocal.finiteLocalLog v A)
        (ContinuousLinearMap.id (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A) (f 0) := by
      rw [hf0]
      exact OrderedProductDerivative.finiteLog_hasStrictFDerivAt_prime v A
    convert! hl.comp (0 : W) hf using 1
  have hq : HasStrictFDerivAt q
      (ContinuousLinearMap.id (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) W) 0 := by
    convert! P.hasStrictFDerivAt.comp (0 : W) hlogf using 1
    ext x
    exact congrArg Subtype.val (hP x).symm
  have hq0 : q 0 = 0 := by simp only [q, hf0, SpanLocal.finiteLocalLog_one, map_zero]
  have hm : Filter.map q (𝓝 (0 : W)) = 𝓝 (0 : W) := by
    simpa only [hq0] using hq.map_nhds_eq_of_equiv
      (f' := ContinuousLinearEquiv.refl (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) W)
  have hdom : ∀ᶠ x in 𝓝 (0 : W), f x ∈ SpanLocal.finiteLogDomain v A := by
    have ht := hf.continuousAt.tendsto
    rw [hf0] at ht
    exact ht (SpanLocal.finiteLogDomain_mem_nhds v A)
  have hpull : ∀ᶠ x in 𝓝 (0 : W), NormedSpace.exp (q x : A) ∈ H := by
    filter_upwards [hfH, hdom] with x hx hd
    have hW := hlog (f x) hx hd
    have he : (q x : A) = SpanLocal.finiteLocalLog v A (f x) :=
      congrArg Subtype.val (hP ⟨SpanLocal.finiteLocalLog v A (f x), hW⟩)
    rw [he, SpanLocal.exp_finiteLocalLog v hd]
    exact hx
  have hout : ∀ᶠ (x : W) in Filter.map q (𝓝 (0 : W)), NormedSpace.exp (x : A) ∈ H := hpull
  rwa [hm] at hout

end

section

/-! Parameterization by a finite basis chosen from actual subgroup
logarithms. All parameter values sufficiently close to zero lie in the
original closed submonoid. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology _root_.Module

attribute [local instance] TangentBracket.finiteClosedPrimeNontriviallyNormedField
attribute [local instance 50] OrderedProductDerivative.finitePrimeNormedAlgebra

variable {F : Type} [Field F] [NumberField F]

theorem subgroup_parameterization_of_basis (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    (H : Submonoid A) (hH : IsClosed (H : Set A))
    (W : Submodule (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A)
    {n : ℕ} (b : Basis (Fin n) (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) W)
    (hb : ∀ i, (b i : A) ∈ Metric.eball 0
      (NormedSpace.expSeries (v.adicCompletion F) A).radius ∧ NormedSpace.exp (b i : A) ∈ H) :
    ∃ f : W → A, f 0 = 1 ∧ HasStrictFDerivAt f W.subtypeL 0 ∧
      ∀ᶠ x in 𝓝 (0 : W), f x ∈ H := by
  let : NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A := OrderedProductDerivative.finitePrimeNormedSpace v A
  let : NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) W := inferInstance
  let L : Fin n → W →L[TangentBracket.closedPrimeSubfield (v.adicCompletion F)]
      TangentBracket.closedPrimeSubfield (v.adicCompletion F) := fun i => (b.coord i).toContinuousLinearMap
  let X : Fin n → A := fun i => (b i : A)
  let f := ExponentialProducts.finiteExpProduct v L X
  have hsum : (∑ i, (L i).smulRight (X i)) = W.subtypeL := by
    ext x
    rw [sum_apply]
    change (∑ i, b.repr x i • (b i : A)) = (x : A)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (b.sum_repr x)
  refine ⟨f, ExponentialProducts.finiteExpProduct_zero (E := W) (A := A) v L X, ?_, ?_⟩
  · rw [← hsum]
    exact ExponentialProducts.finiteExpProduct_hasStrictFDerivAt (E := W) (A := A) v L X
  · exact ExponentialProducts.finiteExpProduct_eventually_mem (E := W) (A := A) v L X H hH
      (fun i => (hb i).1) (fun i => (hb i).2)

theorem exists_subgroup_parameterization (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    (H : Submonoid A) (hH : IsClosed (H : Set A))
    (W : Submodule (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A)
    (hW : W = Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      (SpanLocal.finiteLocalLog v A '' ((H : Set A) ∩ SpanLocal.finiteLogDomain v A))) :
    ∃ f : W → A, f 0 = 1 ∧ HasStrictFDerivAt f W.subtypeL 0 ∧
      ∀ᶠ x in 𝓝 (0 : W), f x ∈ H := by
  subst W
  let s := SpanLocal.finiteLocalLog v A '' ((H : Set A) ∩ SpanLocal.finiteLogDomain v A)
  obtain ⟨n, b, hb⟩ := SpanLocal.exists_fin_basis_span_mem
    (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F)) s
  apply subgroup_parameterization_of_basis v H hH _ b
  intro i
  have hdata :
      (b i : A) ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius ∧
      NormedSpace.exp (b i : A) ∈ H := by
    obtain ⟨g, ⟨hg, hd⟩, he⟩ := hb i
    constructor
    · rw [← he]
      exact hd.2
    · rw [← he, SpanLocal.exp_finiteLocalLog v hd]
      exact hg
  exact hdata

end

/-! A closed submonoid contains exponentials of a whole neighborhood in
its prime-field tangent span. Inclusion of tangent spans therefore gives
local inclusion of the corresponding submonoids. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

attribute [local instance] TangentBracket.finiteClosedPrimeNontriviallyNormedField
attribute [local instance 50] OrderedProductDerivative.finitePrimeNormedAlgebra

variable {F : Type} [Field F] [NumberField F]

def primeLocalTangentSpan (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] (H : Submonoid A) :
    Submodule (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A :=
  Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
    (tangentConeAt (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (H : Set A) 1)

theorem exp_eventually_mem_tangentSpan (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    (H : Submonoid A) (hH : IsClosed (H : Set A)) :
    ∀ᶠ (x : primeLocalTangentSpan v H) in 𝓝 0, NormedSpace.exp (x : A) ∈ H := by
  let : NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A := OrderedProductDerivative.finitePrimeNormedSpace v A
  let : IsScalarTower (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) A :=
    OrderedProductDerivative.finitePrimeScalarTower v A
  let W := primeLocalTangentSpan v H
  let : CompleteSpace W := W.closed_of_finiteDimensional.completeSpace_coe
  have hW : W = Submodule.span (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      (SpanLocal.finiteLocalLog v A '' ((H : Set A) ∩ SpanLocal.finiteLogDomain v A)) :=
    SpanLocal.tangentSpan_eq_span_localLog v H (SpanLocal.finiteLogDomain_mem_nhds v A) Subset.rfl
  obtain ⟨f, hf0, hf, hfH⟩ := exists_subgroup_parameterization v H hH W hW
  obtain ⟨V, hV⟩ := W.exists_isCompl
  let P : A →L[TangentBracket.closedPrimeSubfield (v.adicCompletion F)] W :=
    (W.projectionOnto V hV).toContinuousLinearMap
  have hP (x : W) : P (x : A) = x := Submodule.projectionOnto_apply_left hV x
  apply exp_eventually_mem_of_local_parameterization v W P hP H
    (fun g hg hd => Submodule.subset_span (SpanLocal.finiteLocalLog_mem_tangentCone v H hg hd))
    f hf0 hf hfH

theorem tangentSpan_le_implies_local_containment (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A]
    (H G : Submonoid A) (hH : IsClosed (H : Set A))
    (hspan : primeLocalTangentSpan v G ≤ primeLocalTangentSpan v H) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ G → g ∈ H := by
  let : NormedSpace (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) A := OrderedProductDerivative.finitePrimeNormedSpace v A
  let : IsScalarTower (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) A :=
    OrderedProductDerivative.finitePrimeScalarTower v A
  let W := primeLocalTangentSpan v H
  obtain ⟨V, hV⟩ := W.exists_isCompl
  let P : A →L[TangentBracket.closedPrimeSubfield (v.adicCompletion F)] W :=
    (W.projectionOnto V hV).toContinuousLinearMap
  have hP (x : W) : P (x : A) = x := Submodule.projectionOnto_apply_left hV x
  have ht : Tendsto (fun g => P (SpanLocal.finiteLocalLog v A g)) (𝓝 (1 : A)) (𝓝 (0 : W)) := by
    have hl := (SpanLocal.finiteLocalLog_hasStrictFDerivAt v A).continuousAt.tendsto
    rw [SpanLocal.finiteLocalLog_one] at hl
    simpa only [map_zero, Function.comp_def] using P.continuous.tendsto 0 |>.comp hl
  have hevent := ht (exp_eventually_mem_tangentSpan v H hH)
  filter_upwards [hevent, SpanLocal.finiteLogDomain_mem_nhds v A] with g hg hd
  intro hG
  have hW : SpanLocal.finiteLocalLog v A g ∈ W :=
    hspan (Submodule.subset_span (SpanLocal.finiteLocalLog_mem_tangentCone v G hG hd))
  have he : (P (SpanLocal.finiteLocalLog v A g) : A) = SpanLocal.finiteLocalLog v A g :=
    congrArg Subtype.val (hP ⟨SpanLocal.finiteLocalLog v A g, hW⟩)
  change NormedSpace.exp (P (SpanLocal.finiteLocalLog v A g) : A) ∈ H at hg
  rwa [he, SpanLocal.exp_finiteLocalLog v hd] at hg

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalSubgroup
