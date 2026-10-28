import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KernelDimensionCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelOpen
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Projective Section Kernel Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveSectionKernelOpen

noncomputable section

/-! A specified finite family of cycles is a complete kernel basis on
an actual open set. The field-valued-point criterion uses two open rank
inequalities and the actual scalar-extended cycle comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u
variable {S : Scheme.{u}} {r : ℕ}
variable {M N : Type u} [AddCommGroup M] [Module Γ(S, ⊤) M]
variable [AddCommGroup N] [Module Γ(S, ⊤) N]
variable [Module.Finite Γ(S, ⊤) M] [Module.Projective Γ(S, ⊤) M]
variable [Module.Finite Γ(S, ⊤) N] [Module.Projective Γ(S, ⊤) N]
variable (s : (Fin r →₀ Γ(S, ⊤)) →ₗ[Γ(S, ⊤)] M) (d : M →ₗ[Γ(S, ⊤)] N)

def finiteProjectiveSectionKernelOpen : S.Opens :=
  ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen s 0 ⊓ ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen d r

def baseChangedSectionKernelComparison (h : d.comp s = 0)
    (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] :
    (B ⊗[Γ(S, ⊤)] (Fin r →₀ Γ(S, ⊤))) →ₗ[B] (d.baseChange B).ker :=
  KernelDimensionCriterion.linearKernelComparison (s.baseChange B) (d.baseChange B) (by
    rw [← LinearMap.baseChange_comp, h, LinearMap.baseChange_zero])

theorem finiteProjectiveSectionKernelOpen_field_point (h : d.comp s = 0)
    {K : Type u} [Field K] (c : Spec (.of K) ⟶ S) :
    (letI := c.appTop.hom.toAlgebra;
      Set.range c ⊆ (finiteProjectiveSectionKernelOpen s d : Set S) ↔
        Function.Bijective (baseChangedSectionKernelComparison s d h Γ(Spec (.of K), ⊤))) := by
  let := c.appTop.hom.toAlgebra
  let : Field Γ(Spec (.of K), ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  have hr : Module.finrank Γ(Spec (.of K), ⊤)
      (Γ(Spec (.of K), ⊤) ⊗[Γ(S, ⊤)] (Fin r →₀ Γ(S, ⊤))) = r := by
    let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) Γ(S, ⊤) (Fin r →₀ Γ(S, ⊤))).baseChange
      Γ(Spec (.of K), ⊤)
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  have hs := ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen_field_point c s 0
  have hd := ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen_field_point c d r
  change Set.range c ⊆
      (ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen s 0 : Set S) ∩ (ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen d r : Set S) ↔
    Function.Bijective (KernelDimensionCriterion.linearKernelComparison (s.baseChange Γ(Spec (.of K), ⊤))
      (d.baseChange Γ(Spec (.of K), ⊤)) _)
  rw [Set.subset_inter_iff, hs, hd, KernelDimensionCriterion.linearKernelComparison_bijective_iff_kernelDimensions, hr]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveSectionKernelOpen
