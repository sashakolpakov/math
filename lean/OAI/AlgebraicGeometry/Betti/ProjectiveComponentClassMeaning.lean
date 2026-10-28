import OAI.AlgebraicGeometry.Betti.ProjectiveComponentForms
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback

/-! # Projective Component Class Meaning -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# The native cochain meaning of component de Rham classes

The class previously constructed using the product of the component
cohomologies is exactly the native cochain class of the same closed family.
The cocycle conversions below retain the underlying differential forms.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

section Manifold

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A closed actual form, regarded as a concrete cocycle of its native
manifold de Rham complex. -/
def Betti.ProjectiveComponentClassMeaning.manifoldClosedFormCocycle (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n →ₗ[ℂ]
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n :=
  (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n).subtype.codRestrict _ fun form => by
    erw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
    change (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).d n (n + 1) form.val = 0
    rw [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d_apply]
    exact form.property

@[simp]
theorem Betti.ProjectiveComponentClassMeaning.manifoldClosedFormCocycle_val (n : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    (Betti.ProjectiveComponentClassMeaning.manifoldClosedFormCocycle E M n form).val = form.val := rfl

/-- The literal closed-form quotient class is the native cochain class of
that very form. -/
theorem Betti.ProjectiveComponentClassMeaning.manifoldDeRhamFormClass_eq_cochainClass (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n
        (Betti.ProjectiveComponentClassMeaning.manifoldClosedFormCocycle E M n form) := by
  let K := Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M
  let z := Betti.ProjectiveComponentClassMeaning.manifoldClosedFormCocycle E M n form
  let cycle := (K.sc n).moduleCatCyclesIso.inv z
  have hcycle : (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom cycle = form := by
    apply Subtype.ext
    erw [Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamClosedFormsIso_hom_coe]
    exact ConcreteCategory.congr_hom ((K.sc n).moduleCatCyclesIso_inv_iCycles) z
  have h := ConcreteCategory.congr_hom
    (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso_comp_class E M n) cycle
  change Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n
    ((Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom cycle) = K.homologyπ n cycle at h
  rw [hcycle] at h
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]
  exact h

end Manifold

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The exact same closed component family, viewed as a native concrete
cocycle using the already proved equality of the two kernel submodules. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentClosedFormCocycle (n : ℕ) :
    P.componentClosedForms n →ₗ[ℂ]
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles P.componentDeRhamComplex n where
  toFun form := ⟨form.val, by
    erw [← P.componentClosedForms_eq_cochainCocycles n]
    exact form.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentClosedFormCocycle_val (n : ℕ) (form : P.componentClosedForms n) :
    (P.componentClosedFormCocycle n form).val = form.val := rfl

/-- Projection of the family cocycle is the cocycle of the same component
form, before passing to any cohomology quotient. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentClosedFormCocycle_projection (n : ℕ)
    (form : P.componentClosedForms n) (C : irreducibleComponents P.carrier) :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (P.componentDeRhamProjection C) n
        (P.componentClosedFormCocycle n form) =
      Betti.ProjectiveComponentClassMeaning.manifoldClosedFormCocycle (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n (P.componentClosedFormsEquiv n form C) := by
  apply Subtype.ext
  rfl

/-- The product-defined component class is precisely the native cochain
class of the same closed family of differential forms. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass_eq_cochainClass (n : ℕ) (form : P.componentClosedForms n) :
    P.componentDeRhamClass n form =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass P.componentDeRhamComplex n
        (P.componentClosedFormCocycle n form) := by
  apply (P.componentDeRhamCohomologyEquiv n).injective
  funext C
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_class, Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamCohomologyEquiv_apply,
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentClosedFormCocycle_projection]
  exact Betti.ProjectiveComponentClassMeaning.manifoldDeRhamFormClass_eq_cochainClass
    (P.componentVariety C).analyticModel (P.componentVariety C).analyticSpace n
      (P.componentClosedFormsEquiv n form C)

/-- Equality of the two actual linear class maps on all representatives. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass_eq_cochainClass_comp (n : ℕ) :
    P.componentDeRhamClass n =
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass P.componentDeRhamComplex n).comp
        (P.componentClosedFormCocycle n) := by
  ext form
  exact P.componentDeRhamClass_eq_cochainClass n form

/-- The same class is the categorical homology projection of the canonical
categorical cocycle corresponding to the closed component family. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass_eq_homologyπ (n : ℕ) (form : P.componentClosedForms n) :
    P.componentDeRhamClass n form =
      (P.componentDeRhamComplex.homologyπ n)
        ((P.componentDeRhamComplex.sc n).moduleCatCyclesIso.inv
          (P.componentClosedFormCocycle n form)) := by
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDeRhamClass_eq_cochainClass, AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_homologyπ]

end

end OAI.AlgebraicGeometry
