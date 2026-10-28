import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationReduction
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies

/-! # Frobenius Reduction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FrobeniusReduction.Construction.Multiplication

noncomputable section

/-!
# CartierDuality: characteristic-p multiplication from the actual dual Frobenius kernel
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- Finiteness of the geometric kernel of the actual dual Frobenius
implies finiteness of multiplication by p on the actual dual abelian variety.
The kernel and both Frobenius maps retain their scheme structures. -/
theorem finite_dual_characteristic_power_of_finite_dual_kernel
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    [Finite (Over.mk (𝟙 (Spec (.of k))) ⟶
      Picard.Homomorphisms.Kernel.Construction.kernelScheme (Picard.Homomorphisms.DualFrobenius.Construction.dualRelativeFrobenius D p Fact.out
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))))] :
    IsFinite ((𝟙 D.abelian.scheme : D.abelian.scheme ⟶ D.abelian.scheme) ^ p).left := by
  let hS := Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  let V := Picard.Homomorphisms.DualFrobenius.Construction.dualRelativeFrobenius D p Fact.out hS
  have hV : V = Picard.Homomorphisms.Verschiebung.Construction.verschiebung p k D.abelian.scheme :=
    Picard.Homomorphisms.DualGroupComparison.Construction.dualRelativeFrobenius_eq_verschiebung D p
  let : IsMonHom V := hV.symm ▸ inferInstanceAs
    (IsMonHom (Picard.Homomorphisms.Verschiebung.Construction.verschiebung p k D.abelian.scheme))
  let : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme V).hom :=
    Picard.Homomorphisms.FiniteGeometricPoints.Construction.finite_morphism_of_proper_finite_rationalPoints (Picard.Homomorphisms.Kernel.Construction.kernelScheme V)
  let hfinV : IsFinite V.left := Picard.Homomorphisms.FiniteGroupMaps.Construction.groupHom_finite_of_finite_kernel V
  let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p Fact.out hS D.abelian.scheme
  let hfinF : IsFinite F.left := Picard.Homomorphisms.Properties.Construction.relativeFrobenius_finite p Fact.out hS D.abelian.scheme
  have hFV : F.left ≫ V.left = ((𝟙 D.abelian.scheme) ^ p).left :=
    congrArg (fun a => a.left) (Picard.Homomorphisms.DualGroupComparison.Construction.frobenius_dual_givenGroupPow D p Fact.out hS)
  exact hFV ▸ MorphismProperty.comp_mem (@IsFinite) F.left V.left hfinF hfinV

/-- Finiteness of the geometric kernel of the actual dual Frobenius
implies finiteness of multiplication by p on the polarized abelian variety.
The kernel and both Frobenius maps retain their scheme structures. -/
theorem finite_characteristic_power_of_finite_dual_kernel
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    [Finite (Over.mk (𝟙 (Spec (.of k))) ⟶
      Picard.Homomorphisms.Kernel.Construction.kernelScheme (Picard.Homomorphisms.DualFrobenius.Construction.dualRelativeFrobenius D p Fact.out
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))))] :
    IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ p).left := by
  let : IsFinite ((𝟙 D.abelian.scheme) ^ p).left :=
    finite_dual_characteristic_power_of_finite_dual_kernel p k A D
  exact MultiplicationReduction.Construction.Multiplication.finite_power_of_finite_hom ell.hom p

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FrobeniusReduction.Construction.Multiplication
