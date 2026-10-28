import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedExactness

/-! # Module Equivalences -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.ModuleEquivalences.GradedModules

noncomputable section

/-! Actual principal localizations and their homogeneous degree pieces preserve module linear equivalences. -/

open DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

def awayModuleLinearEquiv (E : M ≃ₗ[A] N) (a : A) : Presentations.Module.Fractions.GradedModules.AwayModule a M ≃ₗ[R] Presentations.Module.Fractions.GradedModules.AwayModule a N :=
  LinearEquiv.ofBijective (GradedExactness.GradedModules.awayModuleMap (R := R) a E.toLinearMap) ⟨by
    intro x y hxy
    exact IsLocalizedModule.map_injective (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) N) E.toLinearMap E.injective hxy,
    GradedExactness.GradedModules.awayModuleMap_surjective a E.toLinearMap E.surjective⟩

theorem awayModuleLinearEquiv_fraction (E : M ≃ₗ[A] N) (a : A) (k : ℕ) (m : M) :
    awayModuleLinearEquiv (R := R) E a (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m) =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k (E m) := GradedExactness.GradedModules.awayModuleMap_fraction a E.toLinearMap k m

variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) (𝒩 : ℤ → Submodule R N) [Decomposition ℳ] [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩]

theorem awayModuleLinearEquiv_degree (E : M ≃ₗ[A] N)
    (hE : ∀ d m, m ∈ ℳ d → E m ∈ 𝒩 d) (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ) :
    (DegreePieces.GradedModules.localizedDegreePiece ℳ a e d).map (awayModuleLinearEquiv (R := R) E a).toLinearMap =
      DegreePieces.GradedModules.localizedDegreePiece 𝒩 a e d := by
  apply le_antisymm
  · rintro x ⟨m, hm, rfl⟩
    exact GradedExactness.GradedModules.awayModuleMap_homogeneous 𝒜 ℳ 𝒩 a e ha E.toLinearMap hE d m hm
  · intro x hx
    obtain ⟨m, hm⟩ := GradedExactness.GradedModules.localizedDegreeMap_surjective 𝒜 ℳ 𝒩 a e ha E.toLinearMap hE E.surjective d ⟨x, hx⟩
    exact ⟨m.val, m.property, congrArg Subtype.val hm⟩

def localizedDegreeLinearEquiv (E : M ≃ₗ[A] N)
    (hE : ∀ d m, m ∈ ℳ d → E m ∈ 𝒩 d) (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ) :
    DegreePieces.GradedModules.localizedDegreePiece ℳ a e d ≃ₗ[R] DegreePieces.GradedModules.localizedDegreePiece 𝒩 a e d :=
  (awayModuleLinearEquiv (R := R) E a).ofSubmodules _ _ (awayModuleLinearEquiv_degree 𝒜 ℳ 𝒩 E hE a e ha d)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.ModuleEquivalences.GradedModules
