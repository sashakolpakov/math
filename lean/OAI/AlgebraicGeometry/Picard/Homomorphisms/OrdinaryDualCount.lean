import OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDivision
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusPoints
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricKernel

/-! # Ordinary Dual Count -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDualCount

noncomputable section

/-! The ordinary p-rank count transfers through the given isogeny to the
dual and determines the number of points of its Picard Frobenius kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
variable (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)

include ell in
theorem ordinary_dualFrobenius_kernelPointCount
    (hordinary : Nat.card (A.torsionPoints p (Over.mk (𝟙 (Spec (.of k))))) = p ^ g) :
    Nat.card {x : Over.mk (𝟙 (Spec (.of k))) ⟶
      (D.abelian.pullback (Frobenius.Construction.absoluteFrobenius p Fact.out (Spec (.of k))
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)))).scheme //
      x ≫ DualFrobenius.Construction.dualRelativeFrobenius D p Fact.out
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) = 1} = p ^ g := by
  rw [DualGroupComparison.Construction.dualRelativeFrobenius_eq_verschiebung D p]
  exact (FrobeniusPoints.Construction.verschiebungKernelPoints_card p k D.abelian.scheme).trans
    (OrdinaryDivision.Construction.isogeny_preserves_ordinary_torsion_count A D.abelian ell p Fact.out hordinary)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.OrdinaryDualCount
