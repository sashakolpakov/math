import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.SheafRestrictionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleReductionCoordinates

/-! # Witt Resolution Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionCoordinates

noncomputable section

/-! Native Witt source-resolution restriction acts in tuple coordinates by the original structure-sheaf restriction map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittPresentationReduction.inclusion p k X n m hnm
local notation "LowerSite" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n
local notation "UpperSite" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) m
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n m hnm

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p k X) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance continuous : (G).IsContinuous LowerSite UpperSite :=
  BoundedCrystalline.LevelMaps.continuous (Witt.Crystalline.wittStructureMap p k X) n m hnm

local instance cocontinuous : (G).IsCocontinuous LowerSite UpperSite :=
  BoundedCrystalline.LevelMaps.cocontinuous (Witt.Crystalline.wittStructureMap p k X) n m hnm

def tupleMap (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) :
    (G).obj (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t) ⟶
      Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X m) a t :=
  ObjectProperty.homMk (WittTupleReduction.morphism p k X n m hnm a t)

theorem projection (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X) (j : Fin (a + 1)) :
    tupleMap p k X n m hnm a t ≫ Pi.π (fun j => WittFrameFamily.Family.frame p k X m (t j)) j =
      (G).map (Pi.π (fun j => WittFrameFamily.Family.frame p k X n (t j)) j) ≫ WittPresentationReduction.frameMap p k X n m hnm (t j) := by
  apply (BoundedCrystalline.Site.inclusion (Witt.Crystalline.wittStructureMap p k X) m).map_injective
  exact WittTupleReductionCoordinates.morphism_projection p k X n m hnm a t j

theorem coordinate (a : ℕ) (t : Fin (a + 1) → StandardCover.Index k X)
    (f : (WittPresentationResolution.complex p k X m).X a ⟶
      BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) m) :
    Presentation.ResolutionCoordinates.sheaf.{u + 1, u} (WittFrameFamily.Family.frame p k X n) R a LowerSite
      (BoundedCrystalline.CrystallineCohomology.structureSheaf (Witt.Crystalline.wittStructureMap p k X) n)
      ((WittResolutionReduction.map p k X n m hnm).f a ≫ (T).map f) t =
        (BigCrystallineCohomology.structureSheaf (Witt.Crystalline.wittStructureMap p k X)).obj.map
          (WittTupleReduction.morphism p k X n m hnm a t).op
            (Presentation.ResolutionCoordinates.sheaf.{u + 1, u} (WittFrameFamily.Family.frame p k X m) R a UpperSite
              (BoundedCrystalline.CrystallineCohomology.structureSheaf (Witt.Crystalline.wittStructureMap p k X) m) f t) :=
  Presentation.SheafRestrictionCoordinates.coordinate.{u + 1, u} G (WittFrameFamily.Family.frame p k X n) (WittFrameFamily.Family.frame p k X m)
    (WittPresentationReduction.frameMap p k X n m hnm) R LowerSite UpperSite a t
    (tupleMap p k X n m hnm a t) (projection p k X n m hnm a t)
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (Witt.Crystalline.wittStructureMap p k X) m) f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionCoordinates
