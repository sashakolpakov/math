import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing
import Mathlib.AlgebraicGeometry.Scheme

/-! # Cech Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCoordinates

noncomputable section

/-!
# The actual scheme-coordinate equations for the affine Čech overlap
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

/-- The scheme morphism associated to an unbundled coordinate-ring map. -/
abbrev specMap {A B : Type u} [CommRing A] [CommRing B] (i : A →+* B) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom i)

/-- Composition of coordinate-ring maps gives contravariant composition of the actual schemes. -/
theorem spec_comp_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (i : A →+* B) (j : B →+* C) (k : A →+* C) (h : j.comp i = k) :
    specMap j ≫ specMap i = specMap k := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def overlapBase : R →+* S ⊗[R] S := (Cech.ModuleModels.firstMap R S).comp (algebraMap R S)
def tripleBase : R →+* (S ⊗[R] S) ⊗[R] S := (Cech.TripleGluing.slot1 R S).comp (algebraMap R S)

theorem second_base : (Cech.ModuleModels.secondMap R S).comp (algebraMap R S) = overlapBase R S := by
  ext r
  exact (Cech.ModuleModels.projection_base_eq R S r).symm

theorem slot2_base : (Cech.TripleGluing.slot2 R S).comp (algebraMap R S) = tripleBase R S := by
  unfold Cech.TripleGluing.slot2 tripleBase Cech.TripleGluing.slot1
  rw [RingHom.comp_assoc, second_base]
  rfl

theorem slot3_base : (Cech.TripleGluing.slot3 R S).comp (algebraMap R S) = tripleBase R S := by
  rw [← Cech.TripleGluing.pair13_second R S, RingHom.comp_assoc, second_base]
  change (Cech.TripleGluing.pair13 R S).comp ((Cech.ModuleModels.firstMap R S).comp (algebraMap R S)) = _
  rw [← RingHom.comp_assoc, Cech.TripleGluing.pair13_first]
  rfl

theorem first_to_base : specMap (Cech.ModuleModels.firstMap R S) ≫ specMap (algebraMap R S) =
    specMap (overlapBase R S) := spec_comp_eq _ _ _ rfl

theorem second_to_base : specMap (Cech.ModuleModels.secondMap R S) ≫ specMap (algebraMap R S) =
    specMap (overlapBase R S) := spec_comp_eq _ _ _ (second_base R S)

theorem slot1_to_base : specMap (Cech.TripleGluing.slot1 R S) ≫ specMap (algebraMap R S) =
    specMap (tripleBase R S) := spec_comp_eq _ _ _ rfl

theorem slot2_to_base : specMap (Cech.TripleGluing.slot2 R S) ≫ specMap (algebraMap R S) =
    specMap (tripleBase R S) := spec_comp_eq _ _ _ (slot2_base R S)

theorem slot3_to_base : specMap (Cech.TripleGluing.slot3 R S) ≫ specMap (algebraMap R S) =
    specMap (tripleBase R S) := spec_comp_eq _ _ _ (slot3_base R S)

theorem pair12_to_first : specMap (Cech.TripleGluing.pair12 R S) ≫ specMap (Cech.ModuleModels.firstMap R S) =
    specMap (Cech.TripleGluing.slot1 R S) := spec_comp_eq _ _ _ rfl

theorem pair12_to_second : specMap (Cech.TripleGluing.pair12 R S) ≫ specMap (Cech.ModuleModels.secondMap R S) =
    specMap (Cech.TripleGluing.slot2 R S) := spec_comp_eq _ _ _ rfl

theorem pair13_to_first : specMap (Cech.TripleGluing.pair13 R S) ≫ specMap (Cech.ModuleModels.firstMap R S) =
    specMap (Cech.TripleGluing.slot1 R S) := spec_comp_eq _ _ _ (Cech.TripleGluing.pair13_first R S)

theorem pair13_to_second : specMap (Cech.TripleGluing.pair13 R S) ≫ specMap (Cech.ModuleModels.secondMap R S) =
    specMap (Cech.TripleGluing.slot3 R S) := spec_comp_eq _ _ _ (Cech.TripleGluing.pair13_second R S)

theorem pair23_to_first : specMap (Cech.TripleGluing.pair23 R S) ≫ specMap (Cech.ModuleModels.firstMap R S) =
    specMap (Cech.TripleGluing.slot2 R S) := spec_comp_eq _ _ _ (Cech.TripleGluing.pair23_first R S)

theorem pair23_to_second : specMap (Cech.TripleGluing.pair23 R S) ≫ specMap (Cech.ModuleModels.secondMap R S) =
    specMap (Cech.TripleGluing.slot3 R S) := spec_comp_eq _ _ _ (Cech.TripleGluing.pair23_second R S)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCoordinates
