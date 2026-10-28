import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Permutations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTransportComposition

/-! # Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Transport

noncomputable section

/-!
# The actual Čech gluing maps under coordinate permutations
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Permutations
open OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTwist OAI.AlgebraicGeometry.Picard.PoincareBundle.ExtensionTransportComposition

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

/-- Swap the second and third coefficients of the first-coordinate module. -/
def swap23OnFirst : TripleGluing.slotModule R S M (TripleGluing.slot1 R S) ≃+ TripleGluing.slotModule R S M (TripleGluing.slot1 R S) :=
  ExtensionTwist.extensionEquiv (TripleGluing.slot1 R S) (TripleGluing.slot1 R S) (Permutations.swap23 R S).toRingEquiv (Permutations.swap23_slot1 R S) M

/-- Swap the second-coordinate pullback into the third-coordinate pullback. -/
def swap23OnSecond : TripleGluing.slotModule R S M (TripleGluing.slot2 R S) ≃+ TripleGluing.slotModule R S M (TripleGluing.slot3 R S) :=
  ExtensionTwist.extensionEquiv (TripleGluing.slot2 R S) (TripleGluing.slot3 R S) (Permutations.swap23 R S).toRingEquiv (Permutations.swap23_slot2 R S) M

/-- Swap the first-coordinate pullback into the second-coordinate pullback. -/
def swap12OnFirst : TripleGluing.slotModule R S M (TripleGluing.slot1 R S) ≃+ TripleGluing.slotModule R S M (TripleGluing.slot2 R S) :=
  ExtensionTwist.extensionEquiv (TripleGluing.slot1 R S) (TripleGluing.slot2 R S) (Permutations.swap12 R S).toRingEquiv (Permutations.swap12_slot1 R S) M

/-- Swap the first two coefficients of the third-coordinate pullback. -/
def swap12OnThird : TripleGluing.slotModule R S M (TripleGluing.slot3 R S) ≃+ TripleGluing.slotModule R S M (TripleGluing.slot3 R S) :=
  ExtensionTwist.extensionEquiv (TripleGluing.slot3 R S) (TripleGluing.slot3 R S) (Permutations.swap12 R S).toRingEquiv (Permutations.swap12_slot3 R S) M

/-- The gluing map from the first slot to the third is transported from first-to-second gluing. -/
theorem transport_gluing12 (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (z : TripleGluing.slotModule R S M (TripleGluing.slot1 R S)) :
    swap23OnSecond R S M (TripleGluing.gluing12 R S M σ z) =
      TripleGluing.gluing13 R S M σ (swap23OnFirst R S M z) := by
  exact ExtensionTransportComposition.transport_extendedMapTo (TripleGluing.pair12 R S) (TripleGluing.pair13 R S) (Permutations.swap23 R S).toRingEquiv
    (Permutations.swap23_pair12 R S) M (ModuleModels.firstMap R S) (ModuleModels.secondMap R S)
    (TripleGluing.slot1 R S) (TripleGluing.slot2 R S) (TripleGluing.slot1 R S) (TripleGluing.slot3 R S)
    rfl rfl (TripleGluing.pair13_first R S) (TripleGluing.pair13_second R S)
    (Permutations.swap23_slot1 R S) (Permutations.swap23_slot2 R S) σ.hom z

/-- The gluing map from the second slot to the third is transported from first-to-third gluing. -/
theorem transport_gluing13 (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (z : TripleGluing.slotModule R S M (TripleGluing.slot1 R S)) :
    swap12OnThird R S M (TripleGluing.gluing13 R S M σ z) =
      TripleGluing.gluing23 R S M σ (swap12OnFirst R S M z) := by
  exact ExtensionTransportComposition.transport_extendedMapTo (TripleGluing.pair13 R S) (TripleGluing.pair23 R S) (Permutations.swap12 R S).toRingEquiv
    (Permutations.swap12_pair13 R S) M (ModuleModels.firstMap R S) (ModuleModels.secondMap R S)
    (TripleGluing.slot1 R S) (TripleGluing.slot3 R S) (TripleGluing.slot2 R S) (TripleGluing.slot3 R S)
    (TripleGluing.pair13_first R S) (TripleGluing.pair13_second R S) (TripleGluing.pair23_first R S) (TripleGluing.pair23_second R S)
    (Permutations.swap12_slot1 R S) (Permutations.swap12_slot3 R S) σ.hom z

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Transport
