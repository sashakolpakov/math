import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeShift

/-! # Graded Action -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedAction.GradedModules

noncomputable section

/-! The actual homogeneous localization grading is compatible with the original graded-ring action. -/

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]

theorem localizedDegree_gradedSMul (a : A) (e : ℤ) (ha : a ∈ 𝒜 e) :
    SetLike.GradedSMul 𝒜 (DegreePieces.GradedModules.localizedDegreePiece ℳ a e) where
  smul_mem := by
    intro i j b x hb hx
    have h := DegreeShift.GradedModules.localizedScalarEnd_homogeneous 𝒜 ℳ a e ha b i hb j x hx
    change b • x ∈ DegreePieces.GradedModules.localizedDegreePiece ℳ a e (j + i) at h
    simpa only [vadd_eq_add, add_comm j i] using h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.GradedAction.GradedModules
