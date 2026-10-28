import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.IntrinsicComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.EndpointTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.TripleCondition

/-! # Intrinsic Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.IntrinsicGluing.Intrinsic

noncomputable section

/-!
# The affine Čech gluing maps are native scheme descent pullbacks
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCocycle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCoordinates

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (L : (Spec (CommRingCat.of S)).Modules)
  (σ : Geometric.CechCocycle.pullbackAlong R S L (Cech.ModuleModels.firstMap R S) ≅ Geometric.CechCocycle.pullbackAlong R S L (Cech.ModuleModels.secondMap R S))

local notation "U" => S ⊗[R] S
local notation "V" => (S ⊗[R] S) ⊗[R] S

theorem geometricExtended_native (i : U →+* V) :
    Geometric.CechCocycle.geometricExtended R S L σ i = Geometric.DescentEquations.nativePullback σ.hom (CechCoordinates.specMap i)
      (CechCoordinates.specMap (i.comp (Cech.ModuleModels.firstMap R S))) (CechCoordinates.specMap (i.comp (Cech.ModuleModels.secondMap R S)))
      (CechCoordinates.spec_comp_eq _ _ _ rfl) (CechCoordinates.spec_comp_eq _ _ _ rfl) := by
  unfold Geometric.CechCocycle.geometricExtended
  have h := IntrinsicComparison.Intrinsic.geometricHom_eq_native
    (CommRingCat.ofHom (Cech.ModuleModels.firstMap R S)) (CommRingCat.ofHom (Cech.ModuleModels.secondMap R S))
    (CommRingCat.ofHom i) σ.hom
  simpa only [← CommRingCat.ofHom_comp] using h

theorem geometric12_native :
    Geometric.CechCocycle.geometric12 R S L σ = Geometric.DescentEquations.nativePullback σ.hom (CechCoordinates.specMap (Cech.TripleGluing.pair12 R S))
      (CechCoordinates.specMap (Cech.TripleGluing.slot1 R S)) (CechCoordinates.specMap (Cech.TripleGluing.slot2 R S))
      (CechCoordinates.pair12_to_first R S) (CechCoordinates.pair12_to_second R S) :=
  geometricExtended_native R S L σ (Cech.TripleGluing.pair12 R S)

theorem geometric13_native :
    Geometric.CechCocycle.geometric13 R S L σ = Geometric.DescentEquations.nativePullback σ.hom (CechCoordinates.specMap (Cech.TripleGluing.pair13 R S))
      (CechCoordinates.specMap (Cech.TripleGluing.slot1 R S)) (CechCoordinates.specMap (Cech.TripleGluing.slot3 R S))
      (CechCoordinates.pair13_to_first R S) (CechCoordinates.pair13_to_second R S) := by
  exact Intrinsic.EndpointTransport.transported_eq_native (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S)
    (Cech.TripleGluing.pair13 R S) (Cech.TripleGluing.slot1 R S) (Cech.TripleGluing.slot3 R S) (Cech.TripleGluing.pair13_first R S) (Cech.TripleGluing.pair13_second R S) σ.hom

theorem geometric23_native :
    Geometric.CechCocycle.geometric23 R S L σ = Geometric.DescentEquations.nativePullback σ.hom (CechCoordinates.specMap (Cech.TripleGluing.pair23 R S))
      (CechCoordinates.specMap (Cech.TripleGluing.slot2 R S)) (CechCoordinates.specMap (Cech.TripleGluing.slot3 R S))
      (CechCoordinates.pair23_to_first R S) (CechCoordinates.pair23_to_second R S) := by
  exact Intrinsic.EndpointTransport.transported_eq_native (Cech.ModuleModels.firstMap R S) (Cech.ModuleModels.secondMap R S)
    (Cech.TripleGluing.pair23 R S) (Cech.TripleGluing.slot2 R S) (Cech.TripleGluing.slot3 R S) (Cech.TripleGluing.pair23_first R S) (Cech.TripleGluing.pair23_second R S) σ.hom

/-- The native triple-overlap equation for an actual geometric gluing morphism. -/
def NativeCocycleHom
    (a : Geometric.CechCocycle.pullbackAlong R S L (Cech.ModuleModels.firstMap R S) ⟶ Geometric.CechCocycle.pullbackAlong R S L (Cech.ModuleModels.secondMap R S)) : Prop :=
  Intrinsic.TripleCondition.NativeTriple a
    (CechCoordinates.specMap (Cech.TripleGluing.slot1 R S)) (CechCoordinates.specMap (Cech.TripleGluing.slot2 R S)) (CechCoordinates.specMap (Cech.TripleGluing.slot3 R S))
    (CechCoordinates.specMap (Cech.TripleGluing.pair12 R S)) (CechCoordinates.specMap (Cech.TripleGluing.pair13 R S)) (CechCoordinates.specMap (Cech.TripleGluing.pair23 R S))
    (CechCoordinates.pair12_to_first R S) (CechCoordinates.pair12_to_second R S)
    (CechCoordinates.pair13_to_first R S) (CechCoordinates.pair13_to_second R S)
    (CechCoordinates.pair23_to_first R S) (CechCoordinates.pair23_to_second R S)

/-- The affine native triple-overlap equation for an invertible gluing. -/
def HasNativeCocycle : Prop := NativeCocycleHom R S L σ.hom

/-- The native scheme cocycle is the geometric affine cocycle used by effective descent. -/
theorem isCocycle_of_native (h : HasNativeCocycle R S L σ) : Geometric.CechCocycle.IsCocycle R S L σ := by
  unfold Geometric.CechCocycle.IsCocycle
  rw [geometric12_native, geometric23_native, geometric13_native]
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.IntrinsicGluing.Intrinsic
