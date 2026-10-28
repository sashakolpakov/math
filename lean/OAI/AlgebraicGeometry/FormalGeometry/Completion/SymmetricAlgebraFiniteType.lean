import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ProjectiveKernelAlgebra
import Mathlib.RingTheory.FiniteType

/-! # Symmetric Algebra Finite Type -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SymmetricAlgebraFiniteType.Construction

noncomputable section

/-! The affine algebras representing finite projective differential
kernels are of finite type over the original base ring. -/

universe u v t
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem symmetricAlgebra_finiteType : Algebra.FiniteType R (SymmetricAlgebra R M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let T := Algebra.adjoin R (↑(s.image (SymmetricAlgebra.ι R M)) : Set (SymmetricAlgebra R M))
  have hspan : Submodule.span R (s : Set M) ≤
      Submodule.comap (SymmetricAlgebra.ι R M) T.toSubmodule := by
    apply Submodule.span_le.mpr
    intro m hm
    exact Algebra.subset_adjoin (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  have hι (m : M) : SymmetricAlgebra.ι R M m ∈ T := by
    apply hspan
    rw [hs]
    trivial
  refine ⟨⟨s.image (SymmetricAlgebra.ι R M), ?_⟩⟩
  change T = ⊤
  apply top_unique
  intro a ha
  clear ha
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => exact T.algebraMap_mem r
  | ι m => exact hι m
  | mul a b ha hb => exact T.mul_mem ha hb
  | add a b ha hb => exact T.add_mem ha hb

variable (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  {Q : Type t} [AddCommGroup Q] [Module R Q] (d : P →ₗ[R] Q)

theorem finiteProjectiveKernelAlgebra_finiteType :
    Algebra.FiniteType R (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebra R P d) :=
  symmetricAlgebra_finiteType R (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelDualModule R P d)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SymmetricAlgebraFiniteType.Construction
