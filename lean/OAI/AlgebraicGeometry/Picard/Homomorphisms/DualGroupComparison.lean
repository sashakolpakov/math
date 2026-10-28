import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupRigidity
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarization
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Verschiebung

/-! # Dual Group Comparison -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison

noncomputable section

/-! Over an algebraically closed field, rigidity identifies the given
dual group law with the one derived from Picard tensor product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem monObj_eq_of_operations {S : Scheme.{u}} {X : Over S} (G H : MonObj X)
    (hunit : G.one = H.one) (hmul : G.mul = H.mul) : G = H := by
  cases G
  cases H
  cases hunit
  cases hmul
  rfl

theorem groupStructure_eq_of_origin
    {k : Type u} [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    (G H : GrpObj X) (hcomm : letI := G; IsCommMonObj X)
    [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (hunit : G.toMonObj.one = H.toMonObj.one) : G = H := by
  have h := GroupRigidity.Construction.pointed_isMonHom (groupA := G) (commA := hcomm) (groupB := H) X X (𝟙 X)
    ((Category.comp_id G.toMonObj.one).trans hunit)
  have hm := @IsMonHom.mul_hom _ _ _ _ _ G.toMonObj H.toMonObj (𝟙 X) h
  have hmul : G.toMonObj.mul = H.toMonObj.mul := by
    simpa only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp] using hm
  exact GrpObj.ext G H (monObj_eq_of_operations G.toMonObj H.toMonObj hunit hmul)

variable {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

/-- Compatibility of the given dual group law is derived by rigidity. -/
theorem dualPicardGroup_eq_given : CanonicalDualGroup.Construction.dualPicardGroup D = D.abelian.group :=
  groupStructure_eq_of_origin D.abelian.scheme (CanonicalDualGroup.Construction.dualPicardGroup D) D.abelian.group
    (CanonicalDualGroup.Construction.dualPicardGroup_commutative D) (CanonicalDualGroup.Construction.dualPicardGroup_origin D)

theorem frobenius_dual_givenGroupPow
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(Spec (.of k), ⊤)) = 0) :
    Frobenius.Construction.relativeFrobenius p hp hS D.abelian.scheme ≫ DualFrobenius.Construction.dualRelativeFrobenius D p hp hS =
      (𝟙 D.abelian.scheme) ^ p := by
  have h := Polarization.Construction.frobenius_dual_picardGroupPow D p hp hS
  rw [dualPicardGroup_eq_given D] at h
  exact h

/-- Picard pullback along Frobenius is the geometrically constructed Verschiebung. -/
theorem dualRelativeFrobenius_eq_verschiebung
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    DualFrobenius.Construction.dualRelativeFrobenius D p Fact.out (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) =
      Verschiebung.Construction.verschiebung p k D.abelian.scheme := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let F := Frobenius.Construction.relativeFrobenius p Fact.out hS D.abelian.scheme
  have : Flat F.left := Homomorphisms.Smooth.Construction.relativeFrobenius_smooth_flat p Fact.out hS D.abelian.scheme
  have : EffectiveEpi F := GroupDescent.Construction.effectiveEpi_over_of_fpqc F
  apply (cancel_epi F).mp
  exact (frobenius_dual_givenGroupPow D p Fact.out hS).trans
    (Verschiebung.Construction.frobenius_comp_verschiebung p k D.abelian.scheme).symm

theorem frobenius_pullback_givenGroupPow
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(Spec (.of k), ⊤)) = 0)
    (ell : A.scheme ⟶ D.abelian.scheme) :
    Frobenius.Construction.relativeFrobenius p hp hS A.scheme ≫
      (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp (Spec (.of k)) hS)).map ell ≫
        DualFrobenius.Construction.dualRelativeFrobenius D p hp hS = ell ^ p := by
  have h := Polarization.Construction.frobenius_pullback_picardGroupPow D p hp hS ell
  rw [dualPicardGroup_eq_given D] at h
  exact h

theorem frobenius_pullback_givenGroup_nsmul
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(Spec (.of k), ⊤)) = 0)
    (ell : A.scheme ⟶ D.abelian.scheme) :
    Additive.ofMul (Frobenius.Construction.relativeFrobenius p hp hS A.scheme ≫
      (Over.pullback (Frobenius.Construction.absoluteFrobenius p hp (Spec (.of k)) hS)).map ell ≫
        DualFrobenius.Construction.dualRelativeFrobenius D p hp hS) = p • Additive.ofMul ell :=
  congrArg Additive.ofMul (frobenius_pullback_givenGroupPow D p hp hS ell)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
