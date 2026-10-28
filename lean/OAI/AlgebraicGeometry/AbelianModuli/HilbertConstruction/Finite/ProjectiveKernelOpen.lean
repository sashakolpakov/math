import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelMatrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelDimensionOpen

/-! # Projective Kernel Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelOpen

noncomputable section

/-! Kernel dimensions of finite projective module maps define actual opens on a scheme, with the expected criterion for every field-valued point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}
variable {M N : Type u} [AddCommGroup M] [Module Γ(X, ⊤) M]
variable [AddCommGroup N] [Module Γ(X, ⊤) N]
variable [Module.Finite Γ(X, ⊤) M] [Module.Projective Γ(X, ⊤) M]
variable [Module.Finite Γ(X, ⊤) N] [Module.Projective Γ(X, ⊤) N]

def finiteProjectiveKernelDimensionOpen (f : M →ₗ[Γ(X, ⊤)] N) (d : ℕ) : X.Opens :=
  Matrix.KernelDimensionOpen.matrixKernelDimensionOpen (ProjectiveKernelMatrix.finiteProjectiveKernelMatrix f) d

theorem finiteProjectiveKernelDimensionOpen_field_point {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ X) (f : M →ₗ[Γ(X, ⊤)] N) (d : ℕ) :
    (letI := c.appTop.hom.toAlgebra;
      Set.range c ⊆ (finiteProjectiveKernelDimensionOpen f d : Set X) ↔
        Module.finrank Γ(Spec (.of K), ⊤) (f.baseChange Γ(Spec (.of K), ⊤)).ker ≤ d) := by
  let := c.appTop.hom.toAlgebra
  have h := Matrix.KernelDimensionOpen.matrixKernelDimensionOpen_field_point c (ProjectiveKernelMatrix.finiteProjectiveKernelMatrix f) d
  have he := (ProjectiveKernelMatrix.finiteProjectiveKernelMatrixBaseChangeEquiv f Γ(Spec (.of K), ⊤)).finrank_eq
  exact h.trans (congrArg (fun n : ℕ => n ≤ d) he).to_iff.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelOpen
