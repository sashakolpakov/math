import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.IntrinsicGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.CechCocycle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CocycleDescent

/-! # Affine Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineDescent

noncomputable section

/-!
# Ordinary scheme descent data give effective affine line-bundle descent
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

section

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.TripleGluing
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.IntrinsicGluing.Intrinsic OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechCocycle

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Ordinary scheme descent data for the actual affine covering morphism. -/
abbrev OrdinaryDatum :=
  Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Affine.CechCoordinates.specMap (algebraMap R S))

variable (D : OrdinaryDatum R S)

/-- Restrict the ordinary descent isomorphism to the actual affine overlap coordinates. -/
def overlapIso : Geometric.CechCocycle.pullbackAlong R S (D.obj PUnit.unit) (Cech.ModuleModels.firstMap R S) ≅
    Geometric.CechCocycle.pullbackAlong R S (D.obj PUnit.unit) (Cech.ModuleModels.secondMap R S) :=
  D.iso (Affine.CechCoordinates.specMap (Affine.CechCoordinates.overlapBase R S)) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    (Affine.CechCoordinates.specMap (Cech.ModuleModels.firstMap R S)) (Affine.CechCoordinates.specMap (Cech.ModuleModels.secondMap R S)) (Affine.CechCoordinates.first_to_base R S) (Affine.CechCoordinates.second_to_base R S)

theorem overlapIso_hom : (overlapIso R S D).hom =
    D.hom (Affine.CechCoordinates.specMap (Affine.CechCoordinates.overlapBase R S)) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (Affine.CechCoordinates.specMap (Cech.ModuleModels.firstMap R S)) (Affine.CechCoordinates.specMap (Cech.ModuleModels.secondMap R S))
      (Affine.CechCoordinates.first_to_base R S) (Affine.CechCoordinates.second_to_base R S) :=
  Pseudofunctor.DescentData.iso_hom D (Affine.CechCoordinates.specMap (Affine.CechCoordinates.overlapBase R S))
    (Affine.CechCoordinates.specMap (Cech.ModuleModels.firstMap R S)) (Affine.CechCoordinates.specMap (Cech.ModuleModels.secondMap R S)) (Affine.CechCoordinates.first_to_base R S) (Affine.CechCoordinates.second_to_base R S)

/-- The ordinary descent axioms imply the native geometric affine Čech cocycle. -/
theorem overlapIso_cocycle : Geometric.CechCocycle.IsCocycle R S (D.obj PUnit.unit) (overlapIso R S D) := by
  apply Affine.IntrinsicGluing.Intrinsic.isCocycle_of_native
  unfold Affine.IntrinsicGluing.Intrinsic.HasNativeCocycle
  rw [overlapIso_hom]
  exact Intrinsic.TripleCondition.hasTripleCocycle (Affine.CechCoordinates.specMap (algebraMap R S)) D
    (Affine.CechCoordinates.specMap (Affine.CechCoordinates.overlapBase R S)) (Affine.CechCoordinates.specMap (Affine.CechCoordinates.tripleBase R S))
    (Affine.CechCoordinates.specMap (Cech.ModuleModels.firstMap R S)) (Affine.CechCoordinates.specMap (Cech.ModuleModels.secondMap R S)) (Affine.CechCoordinates.first_to_base R S) (Affine.CechCoordinates.second_to_base R S)
    (Affine.CechCoordinates.specMap (Cech.TripleGluing.slot1 R S)) (Affine.CechCoordinates.specMap (Cech.TripleGluing.slot2 R S)) (Affine.CechCoordinates.specMap (Cech.TripleGluing.slot3 R S))
    (Affine.CechCoordinates.slot1_to_base R S) (Affine.CechCoordinates.slot2_to_base R S) (Affine.CechCoordinates.slot3_to_base R S)
    (Affine.CechCoordinates.specMap (Cech.TripleGluing.pair12 R S)) (Affine.CechCoordinates.specMap (Cech.TripleGluing.pair13 R S)) (Affine.CechCoordinates.specMap (Cech.TripleGluing.pair23 R S))
    (Affine.CechCoordinates.pair12_to_first R S) (Affine.CechCoordinates.pair12_to_second R S)
    (Affine.CechCoordinates.pair13_to_first R S) (Affine.CechCoordinates.pair13_to_second R S)
    (Affine.CechCoordinates.pair23_to_first R S) (Affine.CechCoordinates.pair23_to_second R S)

/-- When the object on the cover is a line bundle, ordinary descent supplies the geometric input. -/
def geometricDatum (hline : Line.Bundles.IsLine (D.obj PUnit.unit)) :
    Geometric.CocycleDescent.GeometricDatum R S where
  line := ⟨D.obj PUnit.unit, hline⟩
  gluing := overlapIso R S D
  cocycle := overlapIso_cocycle R S D

end

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {R S : CommRingCat.{u}} (f : R ⟶ S)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Spec.map f))
  (hline : Line.Bundles.IsLine (D.obj PUnit.unit))

/-- The affine ring map supplies all coordinate scalar structures in ordinary geometric descent. -/
def ringMapGeometricDatum : Geometric.CocycleDescent.RingMapDatum f := by
  letI := f.hom.toAlgebra
  exact geometricDatum R S D hline

/-- A faithfully flat affine morphism effectively descends ordinary line-bundle descent data. -/
def descendedLine [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) :
    Line.Bundles.LineBundle (Spec R) :=
  Geometric.CocycleDescent.descendedLine f hf (ringMapGeometricDatum f D hline)

/-- The geometric pullback recovers the actual object of the ordinary descent datum. -/
def descendedLinePullbackIso [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) :
    (Scheme.Modules.pullback (Spec.map f)).obj (descendedLine f D hline hf).sheaf ≅
      D.obj PUnit.unit := by
  letI := f.hom.toAlgebra
  exact Geometric.CocycleDescent.descendedLinePullbackIso f hf
    (ringMapGeometricDatum f D hline)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineDescent
