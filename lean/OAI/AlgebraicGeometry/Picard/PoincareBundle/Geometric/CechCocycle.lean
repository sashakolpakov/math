import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing

/-! # Cech Cocycle -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCocycle

noncomputable section

/-!
# Geometric triple-overlap gluing gives the actual module Čech cocycle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.ModuleCat
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingPullback

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

local notation "U" => S ⊗[R] S
local notation "V" => (S ⊗[R] S) ⊗[R] S

variable (L : (Spec (CommRingCat.of S)).Modules)

/-- The two geometric affine pullbacks of the sheaf in the overlap. -/
abbrev pullbackAlong (i : S →+* U) :=
  (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom i))).obj L

/-- Pullback to one coordinate slot of the affine triple overlap. -/
abbrev geometricSlot (i : S →+* V) :=
  (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom i))).obj L

variable (σ : pullbackAlong R S L (Cech.ModuleModels.firstMap R S) ≅ pullbackAlong R S L (Cech.ModuleModels.secondMap R S))

/-- Pull back the gluing to a pair of coordinates in the triple overlap. -/
def geometricExtended (i : U →+* V) :
    geometricSlot R S L (i.comp (Cech.ModuleModels.firstMap R S)) ⟶
      geometricSlot R S L (i.comp (Cech.ModuleModels.secondMap R S)) :=
  Affine.GluingPullback.geometricHom (CommRingCat.ofHom (Cech.ModuleModels.firstMap R S)) (CommRingCat.ofHom (Cech.ModuleModels.secondMap R S))
    (CommRingCat.ofHom i) σ.hom

def geometric12 : geometricSlot R S L (Cech.TripleGluing.slot1 R S) ⟶ geometricSlot R S L (Cech.TripleGluing.slot2 R S) :=
  geometricExtended R S L σ (Cech.TripleGluing.pair12 R S)

def geometric13 : geometricSlot R S L (Cech.TripleGluing.slot1 R S) ⟶ geometricSlot R S L (Cech.TripleGluing.slot3 R S) :=
  eqToHom (congrArg (geometricSlot R S L) (Cech.TripleGluing.pair13_first R S).symm) ≫
    geometricExtended R S L σ (Cech.TripleGluing.pair13 R S) ≫
      eqToHom (congrArg (geometricSlot R S L) (Cech.TripleGluing.pair13_second R S))

def geometric23 : geometricSlot R S L (Cech.TripleGluing.slot2 R S) ⟶ geometricSlot R S L (Cech.TripleGluing.slot3 R S) :=
  eqToHom (congrArg (geometricSlot R S L) (Cech.TripleGluing.pair23_first R S).symm) ≫
    geometricExtended R S L σ (Cech.TripleGluing.pair23 R S) ≫
      eqToHom (congrArg (geometricSlot R S L) (Cech.TripleGluing.pair23_second R S))

/-- The ordinary triple-overlap equation, kept as a named geometric proposition. -/
def IsCocycle : Prop :=
  geometric12 R S L σ ≫ geometric23 R S L σ = geometric13 R S L σ

variable (M : ModuleCat.{u} S) (e : (tilde.functor (CommRingCat.of S)).obj M ≅ L)

/-- The actual affine module gluing recovered from the geometric isomorphism. -/
def moduleGluing : Cech.ModuleModels.firstPullback R S M ≅ Cech.ModuleModels.secondPullback R S M :=
  Affine.Gluing.moduleIso M e (CommRingCat.ofHom (Cech.ModuleModels.firstMap R S)) (CommRingCat.ofHom (Cech.ModuleModels.secondMap R S)) σ

theorem extendedGluing_transfer (i : U →+* V) :
    Cech.TripleGluing.extendedGluing R S M i (moduleGluing R S L σ M e) =
      Affine.Gluing.moduleHom M e (CommRingCat.ofHom (i.comp (Cech.ModuleModels.firstMap R S)))
        (CommRingCat.ofHom (i.comp (Cech.ModuleModels.secondMap R S))) (geometricExtended R S L σ i) := by
  unfold Cech.TripleGluing.extendedGluing moduleGluing
  rw [Affine.Gluing.moduleIso_hom]
  unfold geometricExtended
  convert Affine.GluingPullback.moduleHom_baseChange M e (CommRingCat.ofHom (Cech.ModuleModels.firstMap R S))
    (CommRingCat.ofHom (Cech.ModuleModels.secondMap R S)) (CommRingCat.ofHom i) σ.hom using 1

theorem gluing12_transfer :
    Cech.TripleGluing.gluing12 R S M (moduleGluing R S L σ M e) =
      Affine.Gluing.moduleHom M e (CommRingCat.ofHom (Cech.TripleGluing.slot1 R S)) (CommRingCat.ofHom (Cech.TripleGluing.slot2 R S))
        (geometric12 R S L σ) :=
  extendedGluing_transfer R S L σ M e (Cech.TripleGluing.pair12 R S)

theorem gluing13_transfer :
    Cech.TripleGluing.gluing13 R S M (moduleGluing R S L σ M e) =
      Affine.Gluing.moduleHom M e (CommRingCat.ofHom (Cech.TripleGluing.slot1 R S)) (CommRingCat.ofHom (Cech.TripleGluing.slot3 R S))
        (geometric13 R S L σ) := by
  have h := Affine.Gluing.moduleHom_congr M e (congrArg CommRingCat.ofHom (Cech.TripleGluing.pair13_first R S))
    (congrArg CommRingCat.ofHom (Cech.TripleGluing.pair13_second R S)) (geometricExtended R S L σ (Cech.TripleGluing.pair13 R S))
  rw [← extendedGluing_transfer] at h
  exact h.symm

theorem gluing23_transfer :
    Cech.TripleGluing.gluing23 R S M (moduleGluing R S L σ M e) =
      Affine.Gluing.moduleHom M e (CommRingCat.ofHom (Cech.TripleGluing.slot2 R S)) (CommRingCat.ofHom (Cech.TripleGluing.slot3 R S))
        (geometric23 R S L σ) := by
  have h := Affine.Gluing.moduleHom_congr M e (congrArg CommRingCat.ofHom (Cech.TripleGluing.pair23_first R S))
    (congrArg CommRingCat.ofHom (Cech.TripleGluing.pair23_second R S)) (geometricExtended R S L σ (Cech.TripleGluing.pair23 R S))
  rw [← extendedGluing_transfer] at h
  exact h.symm

/-- The actual geometric triple-overlap cocycle transfers to the actual tensor-extension cocycle. -/
theorem moduleGluing_cocycle
    (h : geometric12 R S L σ ≫ geometric23 R S L σ = geometric13 R S L σ) :
    Cech.TripleGluing.gluing12 R S M (moduleGluing R S L σ M e) ≫
        Cech.TripleGluing.gluing23 R S M (moduleGluing R S L σ M e) =
      Cech.TripleGluing.gluing13 R S M (moduleGluing R S L σ M e) := by
  rw [gluing12_transfer, gluing23_transfer, gluing13_transfer, Affine.Gluing.moduleHom_comp, h]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCocycle
