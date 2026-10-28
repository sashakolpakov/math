import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorModuleLocalization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorGradedAction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.Grading

/-! # Tensor Localized Degrees -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorLocalizedDegrees.GradedModules

noncomputable section

/-! Actual homogeneous degree pieces commute with tensoring and principal module localization. -/

open TensorProduct DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
variable (S : Type t) [AddCommGroup S] [Module R S]

theorem awayModuleTensorEquiv_degree (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ) :
    (decomposeTensor (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e) S d).map (TensorModuleLocalization.GradedModules.awayModuleTensorEquiv R A M S a).toLinearMap =
      Localized.DegreePieces.GradedModules.localizedDegreePiece (decomposeTensor ℳ S) a e d := by
  let := TensorGradedAction.GradedModules.decomposeTensor_gradedSMul 𝒜 ℳ S
  apply le_antisymm
  · rintro x ⟨y, ⟨t, rfl⟩, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul m s =>
      obtain ⟨k, z, hz, hzm⟩ := (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 ℳ a e ha d m.val).mp m.property
      change TensorModuleLocalization.GradedModules.awayModuleTensorEquiv R A M S a (m.val ⊗ₜ[R] s) ∈ _
      rw [← hzm, TensorModuleLocalization.GradedModules.awayModuleTensorEquiv_fraction]
      exact Localized.DegreePieces.GradedModules.moduleFractionMap_mem_degree (decomposeTensor ℳ S) a e d k (z ⊗ₜ[R] s)
        ⟨(⟨z, hz⟩ : ℳ (d + (k : ℤ) * e)) ⊗ₜ[R] s, rfl⟩
    | add x y hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
  · intro x hx
    obtain ⟨k, z, ⟨t, rfl⟩, rfl⟩ :=
      (Localized.DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 (decomposeTensor ℳ S) a e ha d x).mp hx
    let F : ℳ (d + (k : ℤ) * e) →ₗ[R] Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e d :=
      ((Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k).comp (ℳ (d + (k : ℤ) * e)).subtype).codRestrict _
        (fun m => Localized.DegreePieces.GradedModules.moduleFractionMap_mem_degree ℳ a e d k m.val m.property)
    refine ⟨(Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e d).subtype.rTensor S (F.rTensor S t), ⟨F.rTensor S t, rfl⟩, ?_⟩
    clear hx
    induction t using TensorProduct.inductionOn with
    | tmul m s =>
      change TensorModuleLocalization.GradedModules.awayModuleTensorEquiv R A M S a (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m.val ⊗ₜ[R] s) =
        Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k (m.val ⊗ₜ[R] s)
      exact TensorModuleLocalization.GradedModules.awayModuleTensorEquiv_fraction R A M S a k m.val s
    | add x y hx hy => simp only [map_add, hx, hy]

variable [Decomposition ℳ]

def tensorLocalizedDegreeEquiv (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ) :
    Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e d ⊗[R] S ≃ₗ[R]
      Localized.DegreePieces.GradedModules.localizedDegreePiece (decomposeTensor ℳ S) a e d := by
  let := Localized.Grading.GradedModules.localizedDegreeDecomposition 𝒜 ℳ a e ha
  exact (decomposeTensorEquiv (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ a e) S d).trans
    ((TensorModuleLocalization.GradedModules.awayModuleTensorEquiv R A M S a).ofSubmodules _ _ (awayModuleTensorEquiv_degree 𝒜 ℳ S a e ha d))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorLocalizedDegrees.GradedModules
