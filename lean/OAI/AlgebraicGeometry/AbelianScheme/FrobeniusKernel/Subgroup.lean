import OAI.AlgebraicGeometry.Picard.Homomorphisms.MultiplicativeSubgroup

/-! # Subgroup -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Subgroup.Construction

noncomputable section

/-! Actual relative Frobenius kernels over a field have singleton
underlying spaces. The same holds for a group whose relative Frobenius is trivial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.MultiplicativeSubgroup.Construction

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
variable {H : Over (Spec (.of k))} [GrpObj H]

theorem frobeniusKernel_subsingleton :
    Subsingleton (Picard.Homomorphisms.Kernel.Construction.kernelScheme (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) H)).left := by
  let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) H
  have : UniversallyInjective (Picard.Homomorphisms.Kernel.Construction.kernelScheme F).hom := Picard.Homomorphisms.KernelGeometry.Construction.kernelScheme_universallyInjective F
  exact (Picard.Homomorphisms.Kernel.Construction.kernelScheme F).hom.injective.subsingleton

theorem subsingleton_of_trivial_relativeFrobenius
    (h : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) H = 1) : Subsingleton H.left := by
  let F := Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) H
  have hi : Function.Injective F.left := F.left.injective
  constructor
  intro x y
  apply hi
  change (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) H).left x =
      (Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime)
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) H).left y
  rw [h]
  change η[(Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) H)].left (H.hom x) =
    η[(Picard.Homomorphisms.Frobenius.Construction.frobeniusTwist q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) H)].left (H.hom y)
  exact congrArg _ (Subsingleton.elim (H.hom x) (H.hom y))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Subgroup.Construction
