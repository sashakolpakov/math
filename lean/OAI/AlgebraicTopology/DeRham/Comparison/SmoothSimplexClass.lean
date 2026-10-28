import OAI.AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain
import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Smooth Simplex Class -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass

noncomputable section

/-!
# Closed-form representatives under actual simplex integration

Stokes makes the integration cochain of a closed differential form a
genuine cocycle. The induced integration map on de Rham cohomology sends
the class of that form to the existing canonical class of this cocycle.
The proof compares the established categorical and concrete class maps.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
open scoped _root_.Manifold ContDiff Simplicial

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- By the proved Stokes cochain identity, the actual integration cochain
of a closed differential form has zero coboundary. -/
theorem smoothSimplexCochain_closed (n : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    SmoothSimplexCochains.smoothSimplexCochain E M n form.val ∈
      Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) n := by
  rw [Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
  have h := ConcreteCategory.congr_hom
    ((SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M).comm n (n + 1)) form.val
  change (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d n (n + 1)
      (SmoothSimplexCochains.smoothSimplexCochain E M n form.val) =
    SmoothSimplexCochains.smoothSimplexCochain E M (n + 1)
      ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).d n (n + 1) form.val) at h
  rw [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d_apply, form.property] at h
  exact h.trans (SmoothSimplexCochains.smoothSimplexCochain E M (n + 1)).hom.map_zero

/-- Closed forms give actual smooth-singular cocycles by integrating over
each smooth simplex. -/
def smoothSimplexIntegrationCocycle (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n →ₗ[ℂ]
      Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) n :=
  ((SmoothSimplexCochains.smoothSimplexCochain E M n).hom.comp (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n).subtype).codRestrict _
    (smoothSimplexCochain_closed E M n)

@[simp]
theorem smoothSimplexIntegrationCocycle_val (n : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    (smoothSimplexIntegrationCocycle E M n form).val =
      SmoothSimplexCochains.smoothSimplexCochain E M n form.val := rfl

/-- Evaluation of the cocycle is precisely the actual signed Duffy integral. -/
@[simp]
theorem smoothSimplexIntegrationCocycle_evaluation (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n)
    (sigma : (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋n⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
      (ModuleCat.of ℂ ℂ) sigma (smoothSimplexIntegrationCocycle E M n form).val =
        SmoothSimplexIntegration.smoothSimplexIntegration sigma form.val :=
  SmoothSimplexCochains.smoothSimplexCochain_evaluation E M n form.val sigma

set_option backward.isDefEq.respectTransparency false in
/-- The induced integration map sends the genuine de Rham class of a
closed form to the canonical cohomology class of its actual integration
cocycle. -/
theorem smoothSimplexIntegrationCohomologyMap_formClass (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E M n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form) =
      Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) n
        (smoothSimplexIntegrationCocycle E M n form) := by
  let K := Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M
  let L := Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M
  let f := SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M
  let cycle := (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).inv form
  have hcycle : (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom cycle = form :=
    (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).toLinearEquiv.apply_symm_apply form
  have hform : K.iCycles n cycle = form.val := by
    rw [← Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamClosedFormsIso_hom_coe]
    exact congrArg Subtype.val hcycle
  have hclass : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form = K.homologyπ n cycle := by
    have h := ConcreteCategory.congr_hom
      (Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso_comp_class E M n) cycle
    change Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n
      ((Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom cycle) = K.homologyπ n cycle at h
    rwa [hcycle] at h
  have htarget :
      (L.sc n).moduleCatCyclesIso.inv (smoothSimplexIntegrationCocycle E M n form) =
        (HomologicalComplex.cyclesMap f n) cycle := by
    apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
    have hL := ConcreteCategory.congr_hom ((L.sc n).moduleCatCyclesIso_inv_iCycles)
      (smoothSimplexIntegrationCocycle E M n form)
    have hf := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) cycle
    change (L.iCycles n) ((L.sc n).moduleCatCyclesIso.inv
      (smoothSimplexIntegrationCocycle E M n form)) = (f.f n) form.val at hL
    change (L.iCycles n) ((HomologicalComplex.cyclesMap f n) cycle) =
      (f.f n) (K.iCycles n cycle) at hf
    rw [hform] at hf
    exact hL.trans hf.symm
  change (HomologicalComplex.homologyMap f n) (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n form) =
    Cohomology.Singular.Representatives.cochainClass L n (smoothSimplexIntegrationCocycle E M n form)
  rw [hclass, Cohomology.Singular.Representatives.cochainClass_eq_homologyπ, htarget]
  exact ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n) cycle

end

end OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass
