import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.Grading
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Exactness

/-! # Graded Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedExactness.GradedModules

noncomputable section

/-! Localization and passage to a homogeneous degree preserve exact sequences. -/

open DirectSum

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type t} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

def awayModuleMap (a : A) (f : M →ₗ[A] N) : Presentations.Module.Fractions.GradedModules.AwayModule a M →ₗ[R] Presentations.Module.Fractions.GradedModules.AwayModule a N :=
  (IsLocalizedModule.map (Submonoid.powers a) (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) N) f).restrictScalars R

theorem awayModuleMap_fraction (a : A) (f : M →ₗ[A] N) (k : ℕ) (m : M) :
    awayModuleMap (R := R) a f (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m) =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k (f m) := by
  rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply, Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply]
  exact IsLocalizedModule.map_LocalizedModules _ _ _ _

theorem awayModuleMap_surjective (a : A) (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    Function.Surjective (awayModuleMap (R := R) a f) := by
  intro x
  obtain ⟨k, n, rfl⟩ := Presentations.Module.Fractions.GradedModules.moduleFractionMap_surj (R := R) a x
  obtain ⟨m, rfl⟩ := hf n
  exact ⟨Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m, awayModuleMap_fraction a f k m⟩

variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
variable (𝒩 : ℤ → Submodule R N) [SetLike.GradedSMul 𝒜 𝒩]

omit [SetLike.GradedSMul 𝒜 𝒩] in
theorem awayModuleMap_homogeneous (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (f : M →ₗ[A] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : ℤ) (x : Presentations.Module.Fractions.GradedModules.AwayModule a M)
    (hx : x ∈ DegreePieces.GradedModules.localizedDegreePiece ℳ a e d) :
    awayModuleMap (R := R) a f x ∈ DegreePieces.GradedModules.localizedDegreePiece 𝒩 a e d := by
  obtain ⟨k, m, hm, rfl⟩ := (DegreePieces.GradedModules.mem_localizedDegreePiece_iff 𝒜 ℳ a e ha d x).mp hx
  rw [awayModuleMap_fraction]
  exact DegreePieces.GradedModules.moduleFractionMap_mem_degree 𝒩 a e d k (f m) (hf _ m hm)

def localizedDegreeMap (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (f : M →ₗ[A] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (d : ℤ) :
    DegreePieces.GradedModules.localizedDegreePiece ℳ a e d →ₗ[R] DegreePieces.GradedModules.localizedDegreePiece 𝒩 a e d :=
  Graded.Exactness.GradedModules.degreeMap (DegreePieces.GradedModules.localizedDegreePiece ℳ a e) (DegreePieces.GradedModules.localizedDegreePiece 𝒩 a e)
    (awayModuleMap a f) (awayModuleMap_homogeneous 𝒜 ℳ 𝒩 a e ha f hf) d

variable [Decomposition ℳ] [Decomposition 𝒩]

theorem localizedDegreeMap_surjective (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) (f : M →ₗ[A] N)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hs : Function.Surjective f) (d : ℤ) :
    Function.Surjective (localizedDegreeMap 𝒜 ℳ 𝒩 a e ha f hf d) := by
  let := Grading.GradedModules.localizedDegreeDecomposition 𝒜 ℳ a e ha
  let := Grading.GradedModules.localizedDegreeDecomposition 𝒜 𝒩 a e ha
  exact Graded.Exactness.GradedModules.degreeMap_surjective _ _ _ _ (awayModuleMap_surjective a f hs) d

variable {P : Type*} [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
variable (ℙ : ℤ → Submodule R P) [SetLike.GradedSMul 𝒜 ℙ]

omit [SetLike.GradedSMul 𝒜 ℙ] in
theorem localizedDegreeMap_exact (a : A) (e : ℤ) (ha : a ∈ 𝒜 e)
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : ∀ d m, m ∈ ℳ d → f m ∈ 𝒩 d) (hg : ∀ d n, n ∈ 𝒩 d → g n ∈ ℙ d)
    (hex : Function.Exact f g) (d : ℤ) :
    Function.Exact (localizedDegreeMap 𝒜 ℳ 𝒩 a e ha f hf d)
      (localizedDegreeMap 𝒜 𝒩 ℙ a e ha g hg d) := by
  let := Grading.GradedModules.localizedDegreeDecomposition 𝒜 ℳ a e ha
  let := Grading.GradedModules.localizedDegreeDecomposition 𝒜 𝒩 a e ha
  have he : Function.Exact (awayModuleMap (R := R) a f) (awayModuleMap (R := R) a g) :=
    LocalizedModule.map_exact (Submonoid.powers a) f g hex
  exact Graded.Exactness.GradedModules.degreeMap_exact _ _ _ _ _ _ _ he d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedExactness.GradedModules
