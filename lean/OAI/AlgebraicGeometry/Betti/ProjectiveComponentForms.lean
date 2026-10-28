import OAI.AlgebraicGeometry.Betti.ProjectiveComponents
import OAI.AlgebraicTopology.Cohomology.Singular.IndexedProduct
import OAI.AlgebraicTopology.Cohomology.Singular.Representatives
import OAI.Analysis.DifferentialForms.Manifold.ClassRepresentatives
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Projective Component Forms -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Differential forms on all components of a smooth projective presentation

The irreducible components are the actual disjoint integral components of the
given scheme. A form is literally a family of smooth forms on their proved
analytic realizations. Each component retains its own tangent-space dimension.
Exterior differentiation is componentwise, and native categorical cohomology
is canonically the product of the actual component de Rham cohomologies.
-/

open _root_.CategoryTheory

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- A genuine smooth form on every actual integral component, allowing their
analytic models to have different dimensions. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentForms (n : ℕ) :=
  ∀ C : irreducibleComponents P.carrier,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace n

/-- Exterior differentiation of a family of actual smooth component forms. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExteriorDerivative (n : ℕ) :
    P.componentForms n →ₗ[ℂ] P.componentForms (n + 1) :=
  LinearMap.pi fun C => Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d.comp (LinearMap.proj C)

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExteriorDerivative_apply (n : ℕ) (form : P.componentForms n)
    (C : irreducibleComponents P.carrier) :
    P.componentExteriorDerivative n form C = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (form C) := rfl

/-- The exterior derivative squares to zero on these actual families. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExteriorDerivative_squared (n : ℕ) (form : P.componentForms n) :
    P.componentExteriorDerivative (n + 1) (P.componentExteriorDerivative n form) = 0 := by
  funext C
  exact Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared (form C)

/-- The native cochain complex formed from the actual component de Rham complexes. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamComplex : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  Topology.Euclidean.ProductComplexes.Globalization.indexedProductComplex ℂ fun C : irreducibleComponents P.carrier =>
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamComplex_X (n : ℕ) :
    P.componentDeRhamComplex.X n = ModuleCat.of ℂ (P.componentForms n) := rfl

/-- The differential of the native complex is exactly componentwise exterior differentiation. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamComplex_d_apply (n : ℕ) (form : P.componentForms n) :
    P.componentDeRhamComplex.d n (n + 1) form = P.componentExteriorDerivative n form := by
  funext C
  exact Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d_apply (P.componentVariety C).analyticModel
    (P.componentVariety C).analyticSpace n (form C)

/-- The actual projection of the family complex to one component's de Rham complex. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamProjection (C : irreducibleComponents P.carrier) :
    P.componentDeRhamComplex ⟶
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace :=
  AlgebraicTopology.Cohomology.Singular.IndexedProduct.indexedProductProjection ℂ _ C

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamProjection_apply (C : irreducibleComponents P.carrier)
    (n : ℕ) (form : P.componentForms n) :
    (P.componentDeRhamProjection C).f n form = form C := rfl

/-- Native categorical cohomology of the actual component-family complex. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomology (n : ℕ) : ModuleCat ℂ :=
  P.componentDeRhamComplex.homology n

/-- Canonical decomposition of native family cohomology into actual component cohomologies. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv (n : ℕ) :
    P.componentDeRhamCohomology n ≃ₗ[ℂ]
      (∀ C : irreducibleComponents P.carrier, (P.componentVariety C).deRhamCohomology n) :=
  AlgebraicTopology.Cohomology.Singular.IndexedProduct.indexedProductCohomologyEquiv ℂ _ n

/-- Each coordinate of the equivalence is induced by the actual projection of complexes. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_apply (n : ℕ)
    (α : P.componentDeRhamCohomology n) (C : irreducibleComponents P.carrier) :
    P.componentDeRhamCohomologyEquiv n α C =
      HomologicalComplex.homologyMap (P.componentDeRhamProjection C) n α :=
  AlgebraicTopology.Cohomology.Singular.IndexedProduct.indexedProductCohomologyEquiv_apply ℂ _ n α C

/-- Closed families are the actual kernel of componentwise exterior differentiation. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentClosedForms (n : ℕ) : Submodule ℂ (P.componentForms n) :=
  LinearMap.ker (P.componentExteriorDerivative n)

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentClosedForms_iff (n : ℕ) (form : P.componentForms n) :
    form ∈ P.componentClosedForms n ↔ ∀ C, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (form C) = 0 := by
  change P.componentExteriorDerivative n form = 0 ↔ _
  exact ⟨fun h C => congrFun h C, fun h => funext h⟩

/-- These are precisely the concrete cocycles of the native family complex. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentClosedForms_eq_cochainCocycles (n : ℕ) :
    P.componentClosedForms n = AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles P.componentDeRhamComplex n := by
  ext form
  have h := AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff P.componentDeRhamComplex n form
  erw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamComplex_d_apply] at h
  exact h.symm

/-- The actual incoming exterior derivative, including the zero map in degree zero. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentIncomingExteriorDerivative (n : ℕ) :
    P.componentForms (n - 1) →ₗ[ℂ] P.componentForms n :=
  LinearMap.pi fun C =>
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace n).comp (LinearMap.proj C)

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentIncomingExteriorDerivative_apply (n : ℕ)
    (form : P.componentForms (n - 1)) (C : irreducibleComponents P.carrier) :
    P.componentIncomingExteriorDerivative n form C =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n (form C) := rfl

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentIncomingExteriorDerivative_zero :
    P.componentIncomingExteriorDerivative 0 = 0 := by
  ext form C
  rfl

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentIncomingExteriorDerivative_succ (n : ℕ) :
    P.componentIncomingExteriorDerivative (n + 1) = P.componentExteriorDerivative n := by
  ext form C
  rfl

/-- The native incoming differential is the actual incoming exterior derivative in every degree. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamComplex_incoming (n : ℕ) (form : P.componentForms (n - 1)) :
    P.componentDeRhamComplex.d (n - 1) n form = P.componentIncomingExteriorDerivative n form := by
  funext C
  exact ConcreteCategory.congr_hom
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_incoming (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace n) (form C)

/-- Exact families are the actual image of the incoming exterior derivative. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExactForms (n : ℕ) : Submodule ℂ (P.componentForms n) :=
  LinearMap.range (P.componentIncomingExteriorDerivative n)

/-- A family is exact if and only if each component form is exact. Independent
component primitives assemble to an actual family of smooth forms. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentExactForms_iff (n : ℕ) (form : P.componentForms n) :
    form ∈ P.componentExactForms n ↔ ∀ C,
      form C ∈ Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactForms (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n := by
  constructor
  · rintro ⟨primitive, hprimitive⟩ C
    exact ⟨primitive C, congrFun hprimitive C⟩
  · intro h
    choose primitive hprimitive using h
    exact ⟨primitive, funext hprimitive⟩

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExactForms_zero : P.componentExactForms 0 = ⊥ := by
  simp [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExactForms]

/-- Every exact family is closed, by the proved exterior-derivative identity on each component. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExactForms_le_closedForms (n : ℕ) :
    P.componentExactForms n ≤ P.componentClosedForms n := by
  rintro form ⟨primitive, rfl⟩
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentClosedForms_iff]
  intro C
  exact Analysis.DifferentialForms.Manifold.ManifoldDeRham.d_manifoldIncomingExteriorDerivative (P.componentVariety C).analyticModel
    (P.componentVariety C).analyticSpace n (primitive C)

/-- Closed families and families of closed forms are canonically the same module. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentClosedFormsEquiv (n : ℕ) :
    P.componentClosedForms n ≃ₗ[ℂ]
      (∀ C : irreducibleComponents P.carrier,
        Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms (P.componentVariety C).analyticModel
          (P.componentVariety C).analyticSpace n) where
  toFun form C := ⟨form.val C, (P.mem_componentClosedForms_iff n form.val).mp form.property C⟩
  invFun form := ⟨fun C => (form C).val,
    (P.mem_componentClosedForms_iff n _).mpr fun C => (form C).property⟩
  left_inv form := by
    apply Subtype.ext
    rfl
  right_inv form := by
    funext C
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentClosedFormsEquiv_apply (n : ℕ) (form : P.componentClosedForms n)
    (C : irreducibleComponents P.carrier) :
    (P.componentClosedFormsEquiv n form C).val = form.val C := rfl

/-- The canonical class of a closed family: its coordinate classes are exactly
the standard de Rham classes of the actual component forms. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass (n : ℕ) :
    P.componentClosedForms n →ₗ[ℂ] P.componentDeRhamCohomology n :=
  (P.componentDeRhamCohomologyEquiv n).symm.toLinearMap.comp
    ((LinearMap.pi fun C => ((P.componentVariety C).deRhamClass n).comp (LinearMap.proj C)).comp
      (P.componentClosedFormsEquiv n).toLinearMap)

/-- The canonical class map has the expected representative in every component. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_class (n : ℕ) (form : P.componentClosedForms n)
    (C : irreducibleComponents P.carrier) :
    P.componentDeRhamCohomologyEquiv n (P.componentDeRhamClass n form) C =
      (P.componentVariety C).deRhamClass n (P.componentClosedFormsEquiv n form C) := by
  change (P.componentDeRhamCohomologyEquiv n)
    ((P.componentDeRhamCohomologyEquiv n).symm _) C = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- A closed family has zero native cohomology class exactly when it is an exact family. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass_eq_zero_iff (n : ℕ) (form : P.componentClosedForms n) :
    P.componentDeRhamClass n form = 0 ↔ form.val ∈ P.componentExactForms n := by
  rw [← (P.componentDeRhamCohomologyEquiv n).map_eq_zero_iff,
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentExactForms_iff]
  constructor
  · intro h C
    have hC := congrFun h C
    rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_class] at hC
    exact (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace n (P.componentClosedFormsEquiv n form C)).mp hC
  · intro h
    funext C
    rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_class]
    exact (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass_eq_zero_iff (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace n (P.componentClosedFormsEquiv n form C)).mpr (h C)

/-- Every native cohomology class is represented by a genuine closed family of forms. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass_surjective (n : ℕ) :
    Function.Surjective (P.componentDeRhamClass n) := by
  intro α
  have h := fun C : irreducibleComponents P.carrier =>
    Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_surjective (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace n (P.componentDeRhamCohomologyEquiv n α C)
  choose form hform using h
  refine ⟨(P.componentClosedFormsEquiv n).symm form, ?_⟩
  apply (P.componentDeRhamCohomologyEquiv n).injective
  funext C
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_class, LinearEquiv.apply_symm_apply]
  exact hform C

/-- Exact families regarded as a submodule of the closed families. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentExactClosedForms (n : ℕ) : Submodule ℂ (P.componentClosedForms n) :=
  (P.componentExactForms n).comap (P.componentClosedForms n).subtype

/-- The class map's kernel is exactly the genuine exact-form submodule. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass_ker (n : ℕ) :
    LinearMap.ker (P.componentDeRhamClass n) = P.componentExactClosedForms n := by
  ext form
  exact P.componentDeRhamClass_eq_zero_iff n form

/-- Native family cohomology is the literal quotient of closed families by exact families. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamQuotientEquiv (n : ℕ) :
    (P.componentClosedForms n ⧸ P.componentExactClosedForms n) ≃ₗ[ℂ]
      P.componentDeRhamCohomology n :=
  (Submodule.quotEquivOfEq _ _ (P.componentDeRhamClass_ker n).symm).trans
    ((P.componentDeRhamClass n).quotKerEquivOfSurjective (P.componentDeRhamClass_surjective n))

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamQuotientEquiv_mk (n : ℕ) (form : P.componentClosedForms n) :
    P.componentDeRhamQuotientEquiv n (Submodule.Quotient.mk form) =
      P.componentDeRhamClass n form := rfl

/-- Two closed families represent the same class exactly when their difference is exact. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass_eq_iff (n : ℕ) (form other : P.componentClosedForms n) :
    P.componentDeRhamClass n form = P.componentDeRhamClass n other ↔
      form.val - other.val ∈ P.componentExactForms n := by
  simpa only [map_sub, sub_eq_zero, Submodule.coe_sub] using
    P.componentDeRhamClass_eq_zero_iff n (form - other)

/-- Families whose actual smooth component forms have pure bidegree. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureForms (p q : ℕ) : Submodule ℂ (P.componentForms (p + q)) :=
  Submodule.pi Set.univ fun C =>
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule (P.componentVariety C).analyticModel
      (P.componentVariety C).analyticSpace p q

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureForms_iff (p q : ℕ) (form : P.componentForms (p + q)) :
    form ∈ P.componentPureForms p q ↔ ∀ C,
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace p q
        (form C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (P.componentVariety C).analyticModel
          (P.componentVariety C).analyticSpace (p + q)) := by
  simp only [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureForms, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.mem_pureManifoldFormSubmodule]

/-- Pure families inside the actual closed-form kernel. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureClosedForms (p q : ℕ) : Submodule ℂ (P.componentClosedForms (p + q)) :=
  (P.componentPureForms p q).comap (P.componentClosedForms (p + q)).subtype

/-- Purity of a closed family is exactly the established inverse-character
condition on every component's actual complex tangent covectors. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureClosedForms_iff (p q : ℕ)
    (form : P.componentClosedForms (p + q)) :
    form ∈ P.componentPureClosedForms p q ↔ ∀ C,
      Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace p q
        (form.val C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (P.componentVariety C).analyticModel
          (P.componentVariety C).analyticSpace (p + q)) := by
  change form.val ∈ P.componentPureForms p q ↔ _
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureForms_iff]
  exact forall_congr' fun C => Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree (form.val C)

/-- The actual native cohomology subspace represented by closed pure families. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureDeRhamSubspace (p q : ℕ) :
    Submodule ℂ (P.componentDeRhamCohomology (p + q)) :=
  (P.componentPureClosedForms p q).map (P.componentDeRhamClass (p + q))

/-- Membership has precisely the meaning of a genuine closed pure representative family. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureDeRhamSubspace_iff (p q : ℕ)
    (α : P.componentDeRhamCohomology (p + q)) :
    α ∈ P.componentPureDeRhamSubspace p q ↔
      ∃ form : P.componentClosedForms (p + q),
        (∀ C, Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree (P.componentVariety C).analyticModel
          (P.componentVariety C).analyticSpace p q
          (form.val C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (P.componentVariety C).analyticModel
            (P.componentVariety C).analyticSpace (p + q))) ∧
        P.componentDeRhamClass (p + q) form = α := by
  simp only [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureDeRhamSubspace, Submodule.mem_map,
    Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureClosedForms_iff]

/-- The same criterion written using the ordinary equation that exterior differentiation vanishes. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureDeRhamSubspace_iff_smooth (p q : ℕ)
    (α : P.componentDeRhamCohomology (p + q)) :
    α ∈ P.componentPureDeRhamSubspace p q ↔
      ∃ (form : P.componentForms (p + q))
        (hform : P.componentExteriorDerivative (p + q) form = 0),
        (∀ C, Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree (P.componentVariety C).analyticModel
          (P.componentVariety C).analyticSpace p q
          (form C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (P.componentVariety C).analyticModel
            (P.componentVariety C).analyticSpace (p + q))) ∧
        P.componentDeRhamClass (p + q) ⟨form, hform⟩ = α := by
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureDeRhamSubspace_iff]
  constructor
  · rintro ⟨⟨form, hform⟩, hpure, hclass⟩
    exact ⟨form, hform, hpure, hclass⟩
  · rintro ⟨form, hform, hpure, hclass⟩
    exact ⟨⟨form, hform⟩, hpure, hclass⟩

/-- A native family class admits a closed pure representative exactly when all
its component classes admit their genuine closed pure representatives. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureDeRhamSubspace_iff_components (p q : ℕ)
    (α : P.componentDeRhamCohomology (p + q)) :
    α ∈ P.componentPureDeRhamSubspace p q ↔ ∀ C,
      P.componentDeRhamCohomologyEquiv (p + q) α C ∈
        (P.componentVariety C).pureDeRhamSubspace p q := by
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureDeRhamSubspace_iff]
  constructor
  · rintro ⟨form, hpure, rfl⟩ C
    rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_class]
    exact ((P.componentVariety C).mem_pureDeRhamSubspace_iff p q _).mpr
      ⟨P.componentClosedFormsEquiv (p + q) form C, hpure C, rfl⟩
  · intro h
    have hC := fun C : irreducibleComponents P.carrier =>
      ((P.componentVariety C).mem_pureDeRhamSubspace_iff p q _).mp (h C)
    choose form hpure hclass using hC
    refine ⟨(P.componentClosedFormsEquiv (p + q)).symm form, ?_, ?_⟩
    · intro C
      exact hpure C
    · apply (P.componentDeRhamCohomologyEquiv (p + q)).injective
      funext C
      rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_class, LinearEquiv.apply_symm_apply]
      exact hclass C

/-- Under the canonical cohomology equivalence the pure image is exactly the
product of the established pure images of the actual components. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPureDeRhamSubspace_eq_comap (p q : ℕ) :
    P.componentPureDeRhamSubspace p q =
      (Submodule.pi Set.univ fun C : irreducibleComponents P.carrier =>
        (P.componentVariety C).pureDeRhamSubspace p q).comap
          (P.componentDeRhamCohomologyEquiv (p + q)).toLinearMap := by
  ext α
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_componentPureDeRhamSubspace_iff_components]
  simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    LinearEquiv.coe_coe]

end

end OAI.AlgebraicGeometry
