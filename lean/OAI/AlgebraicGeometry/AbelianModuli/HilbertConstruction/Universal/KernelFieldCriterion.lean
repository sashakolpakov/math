import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveFieldExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.KernelExactCriterion

/-! # Kernel Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.KernelFieldCriterion

noncomputable section

/-! Specified cycles in finite projective modules are a complete kernel
basis after every ring extension if they are complete after all field-valued
scalar maps. This includes arbitrary nonreduced coefficient rings. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]
variable {V M N : Type u}
variable [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
variable [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
variable (s : V →ₗ[R] M) (d : M →ₗ[R] N) (h : d.comp s = 0)

def scalarExtendedCycleComparison (B : Type u) [CommRing B] [Algebra R B] :
    (B ⊗[R] V) →ₗ[B] (d.baseChange B).ker :=
  KernelDimensionCriterion.linearKernelComparison (s.baseChange B) (d.baseChange B) (by
    rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_zero])

theorem completeKernel_universal_of_field_tests
    (hfield : ∀ (K : Type u) [Field K] (q : R →+* K),
      letI := q.toAlgebra
      Function.Bijective (scalarExtendedCycleComparison s d h K))
    (B : Type u) [CommRing B] [Algebra R B] :
    Function.Bijective (scalarExtendedCycleComparison s d h B) := by
  let C : ShortComplex (ModuleCat.{u} R) := {
    X₁ := ModuleCat.of R V
    X₂ := ModuleCat.of R M
    X₃ := ModuleCat.of R N
    f := ModuleCat.ofHom s
    g := ModuleCat.ofHom d
    zero := ModuleCat.hom_ext h }
  let Z : ShortComplex (ModuleCat.{u} R) := {
    X₁ := ModuleCat.of R V
    X₂ := ModuleCat.of R V
    X₃ := ModuleCat.of R M
    f := 0
    g := ModuleCat.ofHom s
    zero := zero_comp }
  have hC : ∀ (K : Type u) [Field K] (q : R →+* K),
      (C.map (ModuleCat.extendScalars q)).Exact := by
    intro K _ q
    let := q.toAlgebra
    have hk := hfield K q
    have ht : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R K C).Exact := by
      apply (ShortComplex.moduleCat_exact_iff _).mpr
      intro x hx
      obtain ⟨y, hy⟩ := hk.surjective ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    exact (ShortComplex.exact_iff_of_iso
      (C.mapNatIso (Scalar.FunctorComparison.ScalarFunctorComparison.isoOfHom R K q))).mp ht
  have hZ : ∀ (K : Type u) [Field K] (q : R →+* K),
      (Z.map (ModuleCat.extendScalars q)).Exact := by
    intro K _ q
    let := q.toAlgebra
    have hk := hfield K q
    have hi : Function.Injective (s.baseChange K) :=
      (Linear.KernelExactCriterion.linearKernelComparison_injective_iff _ _ _).mp hk.injective
    have ht : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R K Z).Exact := by
      apply (ShortComplex.moduleCat_exact_iff _).mpr
      intro x hx
      have hx0 : x = 0 := hi (hx.trans (s.baseChange K).map_zero.symm)
      exact ⟨0, (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R K Z).f.hom.map_zero.trans hx0.symm⟩
    exact (ShortComplex.exact_iff_of_iso
      (Z.mapNatIso (Scalar.FunctorComparison.ScalarFunctorComparison.isoOfHom R K q))).mp ht
  have hCB : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B C).Exact :=
    HilbertConstruction.Finite.ProjectiveFieldExactness.finiteProjectiveShortComplex_universal_exact_of_field_tests C hC B
  have hZB : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B Z).Exact :=
    HilbertConstruction.Finite.ProjectiveFieldExactness.finiteProjectiveShortComplex_universal_exact_of_field_tests Z hZ B
  have hi : Function.Injective (s.baseChange B) := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hZB x hx
    have hy0 : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B Z).f y = 0 := by
      change ((0 : V →ₗ[R] V).baseChange B) y = 0
      rw [LinearMap.baseChange_zero]
      rfl
    exact hy.symm.trans hy0
  refine ⟨(Linear.KernelExactCriterion.linearKernelComparison_injective_iff _ _ _).mpr hi, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hCB x.val x.property
  exact ⟨y, Subtype.ext hy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.KernelFieldCriterion
