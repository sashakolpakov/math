import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent
import OAI.Analysis.DifferentialForms.Manifold.Algebra
import OAI.Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence

/-! # Realization Projective Component Raw -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry
open scoped _root_.Manifold
section

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The native real tangent space of a point in an actual integral component. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentTangentFiber
    (s : Σ C : irreducibleComponents P.carrier, (P.componentVariety C).analyticSpace) :=
  TangentSpace 𝓘(ℝ, (P.componentVariety s.1).analyticModel) s.2

/-- The real tangent fiber over a native point, located by the proved component
homeomorphism. Its model is allowed to depend on the component. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointTangentFiber (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :=
  P.componentTangentFiber (P.componentPointsHomeomorph.symm x)

/-- Alternating real covectors at a point in the disjoint union of components. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentCovectorFiber (n : ℕ)
    (s : Σ C : irreducibleComponents P.carrier, (P.componentVariety C).analyticSpace) :=
  P.componentTangentFiber s [⋀^Fin n]→L[ℝ] ℂ

/-- Actual continuous alternating covectors on the component tangent fiber at
a native analytic point. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointCovectorFiber (n : ℕ) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :=
  P.componentCovectorFiber n (P.componentPointsHomeomorph.symm x)

/-- Sections of the dependent alternating-covector family over all native
analytic points. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointCovectorSections (n : ℕ) :=
  ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver, P.pointCovectorFiber n x

/-- At a point of an actual component inclusion, the transported covector
fiber is canonically that component's own covector space. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPointCovectorEquiv (n : ℕ) (C : irreducibleComponents P.carrier)
    (x : (P.componentVariety C).analyticSpace) :
    P.pointCovectorFiber n (P.componentPointMap C x) ≃ₗ[ℂ]
      P.componentCovectorFiber n ⟨C, x⟩ :=
  LinearEquiv.cast (M := P.componentCovectorFiber n)
    (P.componentPointsHomeomorph_symm_componentPointMap C x)

end

section

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- A family of ordinary raw forms on the actual components is precisely a
section of the covector family over the original analytic point space. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentRawFormsSectionsEquiv (n : ℕ) :
    (∀ C : irreducibleComponents P.carrier,
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n) ≃ₗ[ℂ] P.pointCovectorSections n :=
  (LinearEquiv.piCurry ℂ (fun C x => P.componentCovectorFiber n ⟨C, x⟩)).symm.trans
    (LinearEquiv.piCongrLeft' ℂ (P.componentCovectorFiber n)
      P.componentPointsHomeomorph.toEquiv)

end

section

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Forward evaluation uses the unique point and component supplied by the
actual component homeomorphism. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentRawFormsSectionsEquiv_apply (n : ℕ)
    (forms : ∀ C : irreducibleComponents P.carrier,
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :
    P.componentRawFormsSectionsEquiv n forms x =
      forms (P.componentPointsHomeomorph.symm x).1
        (P.componentPointsHomeomorph.symm x).2 :=
  rfl

/-- Inverse evaluation along a component inclusion is the corresponding
canonical dependent-fiber transport. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentRawFormsSectionsEquiv_symm_apply (n : ℕ)
    (s : P.pointCovectorSections n) (C : irreducibleComponents P.carrier)
    (x : (P.componentVariety C).analyticSpace) :
    (P.componentRawFormsSectionsEquiv n).symm s C x =
      P.componentPointCovectorEquiv n C x (s (P.componentPointMap C x)) :=
  eqRec_eq_cast _ _

/-- Pulling a section back to the component of a native point recovers its
value without a remaining fiber cast. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentRawFormsSectionsEquiv_symm_apply_point (n : ℕ)
    (s : P.pointCovectorSections n) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :
    (P.componentRawFormsSectionsEquiv n).symm s
        (P.componentPointsHomeomorph.symm x).1
        (P.componentPointsHomeomorph.symm x).2 = s x :=
  Equiv.piCongrLeft'_symm_apply_apply (P.componentCovectorFiber n)
    P.componentPointsHomeomorph.toEquiv s x

/-- The section associated to a component family restricts to exactly the
original covector field on every actual component. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentRawFormsSectionsEquiv_apply_component (n : ℕ)
    (forms : ∀ C : irreducibleComponents P.carrier,
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n)
    (C : irreducibleComponents P.carrier) (x : (P.componentVariety C).analyticSpace) :
    P.componentPointCovectorEquiv n C x
        (P.componentRawFormsSectionsEquiv n forms (P.componentPointMap C x)) =
      forms C x := by
  rw [← Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentRawFormsSectionsEquiv_symm_apply, LinearEquiv.symm_apply_apply]

end

section

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Smooth sections are those whose restrictions to all actual component
atlases are smooth covector fields. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.smoothPointCovectorSections (n : ℕ) : Submodule ℂ (P.pointCovectorSections n) where
  carrier := {s | ∀ C : irreducibleComponents P.carrier,
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn ((P.componentRawFormsSectionsEquiv n).symm s C) Set.univ}
  zero_mem' := by
    intro C
    simpa only [map_zero, Pi.zero_apply] using
      (Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn.zero (E := (P.componentVariety C).analyticModel)
        (M := (P.componentVariety C).analyticSpace) (n := n) Set.univ)
  add_mem' := by
    intro s t hs ht C
    simpa only [map_add, Pi.add_apply] using (hs C).add (ht C)
  smul_mem' := by
    intro z s hs C
    simpa only [map_smul, Pi.smul_apply] using (hs C).const_smul z

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.mem_smoothPointCovectorSections (n : ℕ) (s : P.pointCovectorSections n) :
    s ∈ P.smoothPointCovectorSections n ↔
      ∀ C : irreducibleComponents P.carrier,
        Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn ((P.componentRawFormsSectionsEquiv n).symm s C) Set.univ :=
  Iff.rfl

end

section

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Smooth component forms are exactly the smooth sections of the actual
dependent covector family. The domain is the literal family of standard
smooth forms, including when different components have different dimensions. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSmoothFormsSectionsEquiv (n : ℕ) :
    (∀ C : irreducibleComponents P.carrier,
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n) ≃ₗ[ℂ] P.smoothPointCovectorSections n where
  toFun forms := ⟨P.componentRawFormsSectionsEquiv n (fun C => (forms C).val), by
    intro C
    simpa only [LinearEquiv.symm_apply_apply] using (forms C).property⟩
  invFun s := fun C => ⟨(P.componentRawFormsSectionsEquiv n).symm s.val C, s.property C⟩
  left_inv forms := by
    funext C
    apply Subtype.ext
    exact congrFun ((P.componentRawFormsSectionsEquiv n).symm_apply_apply
      (fun C => (forms C).val)) C
  right_inv s := by
    apply Subtype.ext
    exact (P.componentRawFormsSectionsEquiv n).apply_symm_apply s.val
  map_add' forms other := by
    apply Subtype.ext
    exact map_add (P.componentRawFormsSectionsEquiv n)
      (fun C => (forms C).val) (fun C => (other C).val)
  map_smul' z forms := by
    apply Subtype.ext
    exact map_smul (P.componentRawFormsSectionsEquiv n) z (fun C => (forms C).val)

end

section

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSmoothFormsSectionsEquiv_apply (n : ℕ)
    (forms : ∀ C : irreducibleComponents P.carrier,
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (P.componentVariety C).analyticModel
        (P.componentVariety C).analyticSpace n)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :
    (P.componentSmoothFormsSectionsEquiv n forms).val x =
      forms (P.componentPointsHomeomorph.symm x).1
        (P.componentPointsHomeomorph.symm x).2 :=
  rfl

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSmoothFormsSectionsEquiv_symm_apply (n : ℕ)
    (s : P.smoothPointCovectorSections n) (C : irreducibleComponents P.carrier)
    (x : (P.componentVariety C).analyticSpace) :
    ((P.componentSmoothFormsSectionsEquiv n).symm s C) x =
      P.componentPointCovectorEquiv n C x (s.val (P.componentPointMap C x)) :=
  P.componentRawFormsSectionsEquiv_symm_apply n s.val C x

end

section

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The native covector fiber also has the literal exterior-power-dual
description, by the proved finite-dimensional tangent-space equivalence. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointExteriorCovectorEquiv (n : ℕ) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :
    P.pointCovectorFiber n x ≃ₗ[ℂ]
      ((⋀[ℝ]^n (P.pointTangentFiber x)) →ₗ[ℝ] ℂ) :=
  Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.tangentExteriorCovectorEquiv
    (E := (P.componentVariety (P.componentPointsHomeomorph.symm x).1).analyticModel)
    (P.componentPointsHomeomorph.symm x).2 n

end

section

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The original exterior-covector evaluation on generators, with the
implicit linear-structure data shared in this reducible expression. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointExteriorGeneratorValue (n : ℕ)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) (form : P.pointCovectorFiber n x)
    (v : Fin n → P.pointTangentFiber x) : ℂ :=
  P.pointExteriorCovectorEquiv n x form (exteriorPower.ιMulti ℝ n v)

/-- The original covector value, kept reducible for the generator identity. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointCovectorValue (n : ℕ)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) (form : P.pointCovectorFiber n x)
    (v : Fin n → P.pointTangentFiber x) : ℂ :=
  form v

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointExteriorCovectorEquiv_apply_ιMulti (n : ℕ)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) (form : P.pointCovectorFiber n x)
    (v : Fin n → P.pointTangentFiber x) :
    P.pointExteriorGeneratorValue n x form v = P.pointCovectorValue n x form v :=
  Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.tangentExteriorCovectorEquiv_apply_ιMulti
    (E := (P.componentVariety (P.componentPointsHomeomorph.symm x).1).analyticModel)
    (P.componentPointsHomeomorph.symm x).2 n form v

end

open scoped ContDiff

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The complete raw section space is the space of sections of the literal
exterior dual of the varying component tangent fibers. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointExteriorSectionsEquiv (n : ℕ) :
    P.pointCovectorSections n ≃ₗ[ℂ]
      (∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver,
        (⋀[ℝ]^n (P.pointTangentFiber x)) →ₗ[ℝ] ℂ) :=
  LinearEquiv.piCongrRight (P.pointExteriorCovectorEquiv n)

/-- Evaluation of the exterior-dual section corresponding to a raw section. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointExteriorSectionValue (n : ℕ) (s : P.pointCovectorSections n)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :
    (⋀[ℝ]^n (P.pointTangentFiber x)) →ₗ[ℝ] ℂ :=
  P.pointExteriorSectionsEquiv n s x

/-- The exterior-dual value of a covector in a native point fiber. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointExteriorCovectorValue (n : ℕ) (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (form : P.pointCovectorFiber n x) :
    (⋀[ℝ]^n (P.pointTangentFiber x)) →ₗ[ℝ] ℂ :=
  P.pointExteriorCovectorEquiv n x form

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.pointExteriorSectionsEquiv_apply (n : ℕ) (s : P.pointCovectorSections n)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) :
    P.pointExteriorSectionValue n s x = P.pointExteriorCovectorValue n x (s x) :=
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.Betti.RealizationProjectiveComponentRaw

/-!
# Covectors on arbitrary smooth projective presentations

The established homeomorphism from the disjoint union of the actual integral
components determines a tangent fiber at each native analytic point. Each
fiber is the tangent space of its own component, so its dimension may vary
between components. Sections of the resulting alternating-covector family
are exactly families of the ordinary covector fields on those components.

The smooth sections are specified by the actual chartwise smoothness on
every component. No tangent spaces, atlas, or regularity assertions are
supplied as additional data.
-/

end AlgebraicGeometry.Betti.RealizationProjectiveComponentRaw

end

end OAI
