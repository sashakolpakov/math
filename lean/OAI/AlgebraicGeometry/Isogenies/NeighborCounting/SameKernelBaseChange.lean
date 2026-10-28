import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Same Kernel Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SameKernelBaseChange

noncomputable section

/-! Equality of complete isogeny kernels survives arbitrary base change,
using the actual all-test-scheme pullback point equivalences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientComparison

universe u

variable {S T : Scheme.{u}} {d : ℕ} {A B C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A C) (s : T ⟶ S)

theorem pullback_kernel_iff (U : Over T) (x : U ⟶ (A.pullback s).scheme) :
    x ≫ (f.pullback s).hom = 1 ↔ A.baseChangePointsEquiv s U x ≫ f.hom = 1 := by
  constructor
  · intro hx
    exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f.hom s U x).symm.trans
      ((congrArg (B.baseChangePointsEquiv s U) hx).trans
        (B.baseChangePointsMulEquiv s U).map_one)
  · intro hx
    apply (B.baseChangePointsMulEquiv s U).injective
    exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f.hom s U x).trans
      (hx.trans (B.baseChangePointsMulEquiv s U).map_one.symm)

theorem sameKernel_pullback (h : QuotientComparison.SameKernel f g) :
    QuotientComparison.SameKernel (f.pullback s) (g.pullback s) := by
  intro U x
  exact (pullback_kernel_iff f s U x).trans
    ((h ((Over.map s).obj U) (A.baseChangePointsEquiv s U x)).trans
      (pullback_kernel_iff g s U x).symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SameKernelBaseChange
