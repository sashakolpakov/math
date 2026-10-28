import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteFrobeniusTorsion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-! # Kernel Character Torsion -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterTorsion

noncomputable section

/-! Every character of the actual Frobenius kernel is killed by p,
using its height-one equation on the whole coordinate algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

theorem frobeniusKernel_coordinate_character_pow
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (A : Over (Spec (.of k))) [GrpObj A]
    (R : CommHopfAlgCat k) [Coalgebra.IsCocomm k R]
    (e : (hopfSpec (.of k)).obj (op R) ≅
      Grp.mk (Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p Fact.out
        (Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)) A)))
    (χ : GroupLike k R) : χ ^ p = 1 := by
  let hS := Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p)
  have hF := FiniteFrobeniusTorsion.Construction.trivialFrobenius_of_groupIso p Fact.out hS e
    (KernelGroup.Construction.relativeFrobenius_kernel_frobenius p Fact.out hS A)
  have hh := AbelianScheme.FrobeniusKernel.HeightOne.Construction.hopfHeightOne_of_trivial_frobenius p k R hF
  apply GroupLike.val_injective
  change χ.val ^ p = (1 : R)
  have h := hh χ.val
  simpa only [χ.isGroupLikeElem_val.counit_eq_one, one_pow, map_one] using h

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterTorsion
