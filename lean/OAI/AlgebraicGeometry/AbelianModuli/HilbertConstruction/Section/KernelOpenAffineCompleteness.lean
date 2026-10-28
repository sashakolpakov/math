import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.KernelOpenAllTests
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FiniteProjectiveExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.KernelExactCriterion

/-! # Kernel Open Affine Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.KernelOpenAffineCompleteness

noncomputable section

/-! On an arbitrary affine test mapping to the cycle-completeness open,
the specified cycles give an actual basis of the scalar-extended kernel.
The test scheme need not be Noetherian or reduced. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {S Y : Scheme.{u}} [IsAffine Y] {r : ℕ}
variable {M N : Type u} [AddCommGroup M] [Module Γ(S, ⊤) M]
variable [AddCommGroup N] [Module Γ(S, ⊤) N]
variable [Module.Finite Γ(S, ⊤) M] [Module.Projective Γ(S, ⊤) M]
variable [Module.Finite Γ(S, ⊤) N] [Module.Projective Γ(S, ⊤) N]
variable (s : (Fin r →₀ Γ(S, ⊤)) →ₗ[Γ(S, ⊤)] M) (d : M →ₗ[Γ(S, ⊤)] N) (h : d.comp s = 0)

theorem sectionKernelOpen_affine_comparison_bijective (b : Y ⟶ S)
    (hb : Set.range b ⊆ (HilbertConstruction.Finite.ProjectiveSectionKernelOpen.finiteProjectiveSectionKernelOpen s d : Set S)) :
    (letI := b.appTop.hom.toAlgebra;
      Function.Bijective (HilbertConstruction.Finite.ProjectiveSectionKernelOpen.baseChangedSectionKernelComparison s d h Γ(Y, ⊤))) := by
  let := b.appTop.hom.toAlgebra
  let R := Γ(S, ⊤)
  let V := Fin r →₀ R
  let B := Γ(Y, ⊤)
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
    zero := by simp }
  have hgeo := (KernelOpenAllTests.finiteProjectiveSectionKernelOpen_all_tests s d h b).mpr hb
  have hC : ∀ (K : Type u) [Field K] (q : Spec (.of K) ⟶ Y),
      (C.map (ModuleCat.extendScalars (q ≫ b).appTop.hom)).Exact := by
    intro K _ q
    let := (q ≫ b).appTop.hom.toAlgebra
    have hk := hgeo K q
    have ht : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R Γ(Spec (.of K), ⊤) C).Exact := by
      apply (ShortComplex.moduleCat_exact_iff _).mpr
      intro x hx
      obtain ⟨y, hy⟩ := hk.surjective ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    exact (ShortComplex.exact_iff_of_iso
      (C.mapNatIso (Scalar.FunctorComparison.ScalarFunctorComparison.isoOfHom R Γ(Spec (.of K), ⊤) (q ≫ b).appTop.hom))).mp ht
  have hZ : ∀ (K : Type u) [Field K] (q : Spec (.of K) ⟶ Y),
      (Z.map (ModuleCat.extendScalars (q ≫ b).appTop.hom)).Exact := by
    intro K _ q
    let := (q ≫ b).appTop.hom.toAlgebra
    have hk := hgeo K q
    have hi : Function.Injective (s.baseChange Γ(Spec (.of K), ⊤)) :=
      (Linear.KernelExactCriterion.linearKernelComparison_injective_iff _ _ _).mp hk.injective
    have ht : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R Γ(Spec (.of K), ⊤) Z).Exact := by
      apply (ShortComplex.moduleCat_exact_iff _).mpr
      intro x hx
      have hx0 : x = 0 := hi (hx.trans (s.baseChange Γ(Spec (.of K), ⊤)).map_zero.symm)
      exact ⟨0, (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R Γ(Spec (.of K), ⊤) Z).f.hom.map_zero.trans hx0.symm⟩
    exact (ShortComplex.exact_iff_of_iso
      (Z.mapNatIso (Scalar.FunctorComparison.ScalarFunctorComparison.isoOfHom R Γ(Spec (.of K), ⊤) (q ≫ b).appTop.hom))).mp ht
  have hCB : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B C).Exact :=
    Geometric.FiniteProjectiveExactness.geometric_finiteProjectiveShortComplex_baseChange_exact b C hC
  have hZB : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R B Z).Exact :=
    Geometric.FiniteProjectiveExactness.geometric_finiteProjectiveShortComplex_baseChange_exact b Z hZ
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

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.KernelOpenAffineCompleteness
