import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Diagonalizable

/-! # Multiplicative -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Multiplicative.Construction

noncomputable section

/-!
The multiplicative factors in the native ordinary block models have
trivial relative Frobenius at level one, as an equality of scheme maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p]

theorem ordinaryMultiplicative_relativeFrobenius (d : ℕ) :
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius p (Fact.out : p.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec p k (CharP.cast_eq_zero k p))
        (OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k p 1 d).X = 1 := by
  apply Picard.Homomorphisms.Diagonalizable.Construction.diagonalizableGroup_relativeFrobenius p (Fact.out : p.Prime)
    k (OrdinaryBlocks.Construction.OrdinaryBlockLabels.{u} p 1 d) (CharP.cast_eq_zero k p)
  intro m
  apply ULift.ext
  change p • m.down.toAdd = 0
  ext i
  change p • m.down.toAdd i = 0
  have hp : (p : ZMod (p ^ 1)) = 0 :=
    (congrArg (fun n : ℕ => (n : ZMod (p ^ 1))) (pow_one p)).symm.trans (ZMod.natCast_self _)
  rw [nsmul_eq_mul, hp, zero_mul]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Multiplicative.Construction
