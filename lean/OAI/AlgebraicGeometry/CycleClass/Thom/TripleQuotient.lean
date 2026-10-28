import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.TensorChainQuotient

/-! # Triple Quotient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TripleQuotient

noncomputable section

/-! Descending a three-factor tensor map through three actual cokernels. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace Constructions

variable {k : Type} [Field k]

abbrev identitySequence (M : ModuleCat.{0} k) : ShortComplex (ModuleCat.{0} k) :=
  ShortComplex.mk (0 : ModuleCat.of k (Fin 0 → k) ⟶ M) (𝟙 M) (by simp)

theorem identitySequence_exact (M : ModuleCat.{0} k) : (identitySequence M).Exact := by
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  refine ⟨0, ?_⟩
  exact hx.symm

theorem tensor_epi {A B C D : ModuleCat.{0} k} (f : A ⟶ C) (g : B ⟶ D)
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact TensorProduct.map_surjective
    ((ModuleCat.epi_iff_surjective f).mp inferInstance)
    ((ModuleCat.epi_iff_surjective g).mp inferInstance)

variable (s t u : ShortComplex (ModuleCat.{0} k))
variable (hs : s.Exact) (ht : t.Exact) (hu : u.Exact)
variable {M : ModuleCat.{0} k} (f : (s.X₂ ⊗ t.X₂) ⊗ u.X₂ ⟶ M)
variable (h₁ : ((s.f ▷ t.X₂) ▷ u.X₂) ≫ f = 0)
variable (h₂ : ((s.X₂ ◁ t.f) ▷ u.X₂) ≫ f = 0)
variable (h₃ : ((s.X₂ ⊗ t.X₂) ◁ u.f) ≫ f = 0)

def curryFirstTwo : s.X₂ ⊗ t.X₂ ⟶ ModuleCat.of k (u.X₂ →ₗ[k] M) :=
  ModuleCat.ofHom (TensorProduct.curry f.hom)

include h₁ in
theorem curryFirstTwo_left : (s.f ▷ t.X₂) ≫ curryFirstTwo s t u f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  exact ConcreteCategory.congr_hom h₁ (x ⊗ₜ[k] z)

include h₂ in
theorem curryFirstTwo_right : (s.X₂ ◁ t.f) ≫ curryFirstTwo s t u f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro z
  exact ConcreteCategory.congr_hom h₂ (x ⊗ₜ[k] z)

variable [Epi s.g] [Epi t.g]

def firstTwoDesc : (s.X₃ ⊗ t.X₃) ⊗ u.X₂ ⟶ M :=
  ModuleCat.ofHom (TensorProduct.lift
    (HodgeConjecture.DegreeTwo.TensorChainQuotient.Constructions.moduleTensorQuotientDesc s t hs ht (curryFirstTwo s t u f)
      (curryFirstTwo_left s t u f h₁) (curryFirstTwo_right s t u f h₂)).hom)

theorem firstTwoDesc_fac :
    ((s.g ⊗ₘ t.g) ⊗ₘ 𝟙 u.X₂) ≫ firstTwoDesc s t u hs ht f h₁ h₂ = f := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x z
  have he := ConcreteCategory.congr_hom
    (HodgeConjecture.DegreeTwo.TensorChainQuotient.Constructions.moduleTensorQuotientDesc_fac s t hs ht (curryFirstTwo s t u f)
      (curryFirstTwo_left s t u f h₁) (curryFirstTwo_right s t u f h₂)) x
  exact congrArg (fun v => v z) he

include h₃ in
theorem firstTwoDesc_third_zero :
    ((s.X₃ ⊗ t.X₃) ◁ u.f) ≫ firstTwoDesc s t u hs ht f h₁ h₂ = 0 := by
  let : Epi (s.g ⊗ₘ t.g) := tensor_epi s.g t.g
  let : Epi ((s.g ⊗ₘ t.g) ⊗ₘ 𝟙 u.X₁) := tensor_epi (s.g ⊗ₘ t.g) (𝟙 u.X₁)
  apply (cancel_epi ((s.g ⊗ₘ t.g) ⊗ₘ 𝟙 u.X₁)).mp
  change ((s.g ⊗ₘ t.g) ⊗ₘ 𝟙 u.X₁) ≫ ((𝟙 _ ⊗ₘ u.f) ≫ _) = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  have he : (s.g ⊗ₘ t.g) ⊗ₘ u.f =
      (𝟙 (s.X₂ ⊗ t.X₂) ⊗ₘ u.f) ≫ ((s.g ⊗ₘ t.g) ⊗ₘ 𝟙 u.X₂) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [he, Category.assoc, firstTwoDesc_fac]
  exact h₃.trans comp_zero.symm

variable [Epi u.g]

def tripleQuotientDesc : (s.X₃ ⊗ t.X₃) ⊗ u.X₃ ⟶ M :=
  HodgeConjecture.DegreeTwo.TensorChainQuotient.Constructions.moduleTensorQuotientDesc (identitySequence (s.X₃ ⊗ t.X₃)) u
    (identitySequence_exact _) hu (firstTwoDesc s t u hs ht f h₁ h₂)
    (by
      change ((0 : ModuleCat.of k (Fin 0 → k) ⟶ s.X₃ ⊗ t.X₃) ▷ u.X₂) ≫ _ = 0
      simp)
    (firstTwoDesc_third_zero s t u hs ht f h₁ h₂ h₃)

theorem tripleQuotientDesc_fac :
    ((s.g ⊗ₘ t.g) ⊗ₘ u.g) ≫ tripleQuotientDesc s t u hs ht hu f h₁ h₂ h₃ = f := by
  have he : (s.g ⊗ₘ t.g) ⊗ₘ u.g =
      ((s.g ⊗ₘ t.g) ⊗ₘ 𝟙 u.X₂) ≫ (𝟙 (s.X₃ ⊗ t.X₃) ⊗ₘ u.g) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [he, Category.assoc]
  change _ ≫ (((identitySequence (s.X₃ ⊗ t.X₃)).g ⊗ₘ u.g) ≫ _) = _
  rw [tripleQuotientDesc, HodgeConjecture.DegreeTwo.TensorChainQuotient.Constructions.moduleTensorQuotientDesc_fac, firstTwoDesc_fac]

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TripleQuotient
