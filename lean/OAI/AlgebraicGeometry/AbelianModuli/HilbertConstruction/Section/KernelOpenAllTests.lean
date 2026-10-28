import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveSectionKernelOpen
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Kernel Open All Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.KernelOpenAllTests

noncomputable section

/-! The cycle-completeness rank open classifies fiberwise completeness
on every test scheme. This is a geometric field-test condition; identifying
it with complete sections of the Hilbert family is a separate comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {r : ℕ}
variable {M N : Type u} [AddCommGroup M] [Module Γ(S, ⊤) M]
variable [AddCommGroup N] [Module Γ(S, ⊤) N]
variable [Module.Finite Γ(S, ⊤) M] [Module.Projective Γ(S, ⊤) M]
variable [Module.Finite Γ(S, ⊤) N] [Module.Projective Γ(S, ⊤) N]
variable (s : (Fin r →₀ Γ(S, ⊤)) →ₗ[Γ(S, ⊤)] M) (d : M →ₗ[Γ(S, ⊤)] N) (h : d.comp s = 0)

def GeometricSectionKernelComplete {T : Scheme.{u}} (b : T ⟶ S) : Prop :=
  ∀ (K : Type u) [Field K] (q : Spec (.of K) ⟶ T),
    letI := (q ≫ b).appTop.hom.toAlgebra
    Function.Bijective (HilbertConstruction.Finite.ProjectiveSectionKernelOpen.baseChangedSectionKernelComparison s d h Γ(Spec (.of K), ⊤))

theorem finiteProjectiveSectionKernelOpen_all_tests {T : Scheme.{u}} (b : T ⟶ S) :
    GeometricSectionKernelComplete s d h b ↔
      Set.range b ⊆ (HilbertConstruction.Finite.ProjectiveSectionKernelOpen.finiteProjectiveSectionKernelOpen s d : Set S) := by
  constructor
  · intro hb
    rintro _ ⟨t, rfl⟩
    let q := T.fromSpecResidueField t
    let k : Spec (T.residueField t) := (⊥ : PrimeSpectrum (T.residueField t))
    have hk := ((HilbertConstruction.Finite.ProjectiveSectionKernelOpen.finiteProjectiveSectionKernelOpen_field_point s d h (q ≫ b)).mpr
      (hb (T.residueField t) q)) ⟨k, rfl⟩
    change b (T.fromSpecResidueField t k) ∈ HilbertConstruction.Finite.ProjectiveSectionKernelOpen.finiteProjectiveSectionKernelOpen s d at hk
    simpa only [Scheme.fromSpecResidueField_apply, SetLike.mem_coe] using hk
  · intro hb K _ q
    apply (HilbertConstruction.Finite.ProjectiveSectionKernelOpen.finiteProjectiveSectionKernelOpen_field_point s d h (q ≫ b)).mp
    rintro _ ⟨x, rfl⟩
    exact hb ⟨q x, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.KernelOpenAllTests
