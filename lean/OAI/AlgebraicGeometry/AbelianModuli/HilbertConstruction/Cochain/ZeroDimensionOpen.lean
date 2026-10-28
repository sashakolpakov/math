import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ScalarExtensionKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveKernelOpen

/-! # Zero Dimension Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroDimensionOpen

noncomputable section

/-! The degree-zero cohomology dimension of a nonnegative finite projective complex is bounded on a matrix-defined open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (C : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ)
variable [Module.Finite Γ(S, ⊤) (C.X 0)] [Module.Projective Γ(S, ⊤) (C.X 0)]
variable [Module.Finite Γ(S, ⊤) (C.X 1)] [Module.Projective Γ(S, ⊤) (C.X 1)]

def cochainZeroDimensionOpen (d : ℕ) : S.Opens :=
  HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen (C.d 0 1).hom d

theorem cochainZeroDimensionOpen_field_point {K : Type u} [Field K]
    (c : Spec (.of K) ⟶ S) (d : ℕ) :
    (letI := c.appTop.hom.toAlgebra;
      Set.range c ⊆ (cochainZeroDimensionOpen C d : Set S) ↔
        Module.finrank Γ(Spec (.of K), ⊤)
          ((ScalarExtensionKernel.cochainScalarExtension C Γ(Spec (.of K), ⊤)).homology 0) ≤ d) := by
  let := c.appTop.hom.toAlgebra
  exact (HilbertConstruction.Finite.ProjectiveKernelOpen.finiteProjectiveKernelDimensionOpen_field_point c (C.d 0 1).hom d).trans
    (congrArg (fun n : ℕ => n ≤ d)
      (ScalarExtensionKernel.cochainScalarExtensionZeroKernelEquiv C Γ(Spec (.of K), ⊤)).finrank_eq).to_iff.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.ZeroDimensionOpen
