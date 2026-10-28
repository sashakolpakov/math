import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeShift

/-! # Degree Power Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.DegreePowerFrames

noncomputable section

/-! Multiplication by a power of an inverted degree-one element gives an explicit frame between degree-zero and positive-degree localized modules. -/

open DirectSum
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeShift.GradedModules

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

def localizedDegreePowerEquiv (g : A) (e : ℤ) (hg : g ∈ 𝒜 e)
    (b c : A) (h : g = b * c) (hb : b ∈ 𝒜 1) (k : ℕ) :
    HilbertScheme.Presentations.Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ g e 0 ≃ₗ[R] HilbertScheme.Presentations.Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ g e (k : ℤ) := by
  let := HilbertScheme.Presentations.Localized.Grading.GradedModules.localizedDegreeDecomposition 𝒜 ℳ g e hg
  have hpow : b ^ k ∈ 𝒜 (k : ℤ) := by
    simpa only [nsmul_eq_mul, mul_one] using SetLike.pow_mem_graded k hb
  let F := HilbertScheme.Presentations.Localized.DegreeShift.GradedModules.localizedScalarPowerEquiv (R := R) (M := M) g b c h k
  have hF : ∀ d x, x ∈ HilbertScheme.Presentations.Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ g e d → F x ∈ HilbertScheme.Presentations.Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ g e (d + k) :=
    HilbertScheme.Presentations.Localized.DegreeShift.GradedModules.localizedScalarEnd_homogeneous 𝒜 ℳ g e hg (b ^ k) (k : ℤ) hpow
  exact (HilbertScheme.Presentations.Graded.ShiftEquiv.GradedModules.gradedShiftEquiv (HilbertScheme.Presentations.Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ g e) F (k : ℤ) hF 0).trans
    (LinearEquiv.ofEq _ _ (congrArg (HilbertScheme.Presentations.Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ g e) (zero_add (k : ℤ))))

theorem localizedDegreePowerEquiv_val (g : A) (e : ℤ) (hg : g ∈ 𝒜 e)
    (b c : A) (h : g = b * c) (hb : b ∈ 𝒜 1) (k : ℕ)
    (x : HilbertScheme.Presentations.Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ g e 0) :
    (localizedDegreePowerEquiv 𝒜 ℳ g e hg b c h hb k x).val = b ^ k • x.val := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.DegreePowerFrames
