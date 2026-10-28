import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPolarization

/-! # Unbundled Dual Group Comparison -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroupComparison

noncomputable section

/-! Geometric duality and Picard kernels without a global dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction.UnbundledPicard

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Over (Spec (.of k))} [GrpObj A]
variable (D : UnbundledDualData.Construction.UnbundledPicard.DualData A)

/-- Compatibility of the given dual group law is derived by rigidity. -/
theorem dualPicardGroup_eq_given : UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D = D.group :=
  DualGroupComparison.Construction.groupStructure_eq_of_origin D.abelian (UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D) D.group
    (UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D) (UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_origin D)

theorem frobenius_dual_givenGroupPow
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(Spec (.of k), ⊤)) = 0) :
    Frobenius.Construction.relativeFrobenius p hp hS D.abelian ≫ UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p hp hS =
      (𝟙 D.abelian) ^ p := by
  have h := UnbundledPolarization.Construction.UnbundledPicard.frobenius_dual_picardGroupPow D p hp hS
  rw [dualPicardGroup_eq_given D] at h
  exact h

/-- Picard pullback along Frobenius is the geometrically constructed Verschiebung. -/
theorem dualRelativeFrobenius_eq_verschiebung
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p Fact.out (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) =
      Verschiebung.Construction.verschiebung p k D.abelian := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Frobenius.Construction.relativeFrobenius p Fact.out hS D.abelian
  have : Flat F.left := Smooth.Construction.relativeFrobenius_smooth_flat p Fact.out hS D.abelian
  have : EffectiveEpi F := GroupDescent.Construction.effectiveEpi_over_of_fpqc F
  apply (cancel_epi F).mp
  exact (frobenius_dual_givenGroupPow D p Fact.out hS).trans
    (Verschiebung.Construction.frobenius_comp_verschiebung p k D.abelian).symm

theorem frobenius_pullback_givenGroupPow
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(Spec (.of k), ⊤)) = 0)
    (ell : A ⟶ D.abelian) :
    Frobenius.Construction.relativeFrobenius p hp hS A ≫
      (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp (Spec (.of k)) hS)).map ell ≫
        UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p hp hS = ell ^ p := by
  have h := UnbundledPolarization.Construction.UnbundledPicard.frobenius_pullback_picardGroupPow D p hp hS ell
  rw [dualPicardGroup_eq_given D] at h
  exact h

theorem frobenius_pullback_givenGroup_nsmul
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(Spec (.of k), ⊤)) = 0)
    (ell : A ⟶ D.abelian) :
    Additive.ofMul (Frobenius.Construction.relativeFrobenius p hp hS A ≫
      (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp (Spec (.of k)) hS)).map ell ≫
        UnbundledDualFrobenius.Construction.UnbundledPicard.dualRelativeFrobenius D p hp hS) = p • Additive.ofMul ell :=
  congrArg Additive.ofMul (frobenius_pullback_givenGroupPow D p hp hS ell)

end Construction.UnbundledPicard

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualGroupComparison
