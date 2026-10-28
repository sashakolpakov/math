import OAI.AlgebraicGeometry.Picard.Homomorphisms.CharacterSpan
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.HopfAlgebra.GroupLike

/-! # Elementary Characters -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ElementaryCharacters

noncomputable section

/-! Finite p-torsion character groups of order p^g are the standard
elementary abelian group, giving the actual split multiplicative model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

def elementaryCharacterGroupEquiv (p : ℕ) [Fact p.Prime]
    (M : Type u) [CommGroup M] [Finite M] (g : ℕ)
    (hkill : ∀ x : M, x ^ p = 1) (hcard : Nat.card M = p ^ g) :
    M ≃* ULift.{u} (Multiplicative (Fin g → ZMod p)) := by
  let : Module (ZMod p) (Additive M) := AddCommGroup.zmodModule (n := p) (G := Additive M) (fun x =>
    congrArg Additive.ofMul (hkill x.toMul))
  have : Module.Finite (ZMod p) (Additive M) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod p) (Additive M) = g := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive M)
    have hc : Nat.card (Additive M) = p ^ g :=
      (Nat.card_congr (Additive.toMul : Additive M ≃ M)).trans hcard
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using h.symm.trans hc
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive M) hdim
  refine { toEquiv := ((Additive.ofMul.trans b.equivFun.toEquiv).trans
      Multiplicative.ofAdd).trans Equiv.ulift.symm, map_mul' := ?_ }
  intro x y
  apply ULift.ext
  change b.equivFun (Additive.ofMul (x * y)) =
    b.equivFun (Additive.ofMul x) + b.equivFun (Additive.ofMul y)
  exact b.equivFun.map_add (Additive.ofMul x) (Additive.ofMul y)

variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A] [Module.Finite k A]

def diagonalizableGroupIsoOfCharacterCard
    (hcard : Nat.card (GroupLike k A) = Module.finrank k A) :
    (hopfSpec (.of k)).obj (op (CommHopfAlgCat.of k A)) ≅
      (hopfSpec (.of k)).obj (op (CommHopfAlgCat.of k (MonoidAlgebra k (GroupLike k A)))) :=
  (hopfSpec (.of k)).mapIso (CommHopfAlgCat.isoMk (CharacterSpan.Construction.characterHopfEquivOfCard k A hcard)).op

def multiplicativeGroupIsoOfCharacterCard
    (p : ℕ) [Fact p.Prime] (g : ℕ)
    (hkill : ∀ x : GroupLike k A, x ^ p = 1)
    (hcard : Nat.card (GroupLike k A) = p ^ g) (hrank : Module.finrank k A = p ^ g) :
    (hopfSpec (.of k)).obj (op (CommHopfAlgCat.of k A)) ≅
      (hopfSpec (.of k)).obj (op (CommHopfAlgCat.of k
        (MonoidAlgebra k (ULift.{u} (Multiplicative (Fin g → ZMod p)))))) := by
  have : Finite (GroupLike k A) := CharacterSpan.Construction.finite_coordinateCharacters k A
  let e := elementaryCharacterGroupEquiv p (GroupLike k A) g hkill hcard
  exact diagonalizableGroupIsoOfCharacterCard k A (hcard.trans hrank.symm) ≪≫
    (hopfSpec (.of k)).mapIso (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k e.symm)).op

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ElementaryCharacters
