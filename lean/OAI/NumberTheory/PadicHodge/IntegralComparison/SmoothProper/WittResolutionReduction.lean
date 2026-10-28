import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittPresentationReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittPresentationResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresentationSheafAugmentationNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionAcyclicity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition

/-! # Witt Resolution Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionReduction

noncomputable section

/-! The original global Witt source resolutions commute with level restriction, preserving their augmentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittPresentationResolution

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

def map : WittPresentationResolution.complex p k X n ⟶ ((T).mapHomologicalComplex (.down ℕ)).obj (WittPresentationResolution.complex p k X m) :=
  Cech.PresentationSheafRestriction.map R G LowerSite UpperSite (WittPresentationReduction.map p k X n m hnm)

instance map_isIso : IsIso (WittResolutionReduction.map p k X n m hnm) := by
  let h : IsIso (WittPresentationReduction.map p k X n m hnm) :=
    WittPresentationReduction.map_isIso p k X n m hnm
  exact Cech.PresentationSheafRestriction.map_isIso R G LowerSite UpperSite
    (WittPresentationReduction.map p k X n m hnm)

def iso : WittPresentationResolution.complex p k X n ≅ ((T).mapHomologicalComplex (.down ℕ)).obj (WittPresentationResolution.complex p k X m) :=
  asIso (WittResolutionReduction.map p k X n m hnm)

theorem augmentation_zero : (WittResolutionReduction.map p k X n m hnm).f 0 ≫ (T).map ((WittPresentationResolution.augmentation p k X m).f 0) =
    (WittPresentationResolution.augmentation p k X n).f 0 ≫ (Bounded.CohomologyTransition.constantUnitIso (Witt.Crystalline.wittStructureMap p k X) n m hnm).inv :=
  Cech.PresentationSheafAugmentationNaturality.zero R G LowerSite UpperSite (WittPresentationReduction.map p k X n m hnm)

theorem restricted_acyclic (a q : ℕ) : Subsingleton (Abelian.Ext.{u + 2}
    ((T).obj ((WittPresentationResolution.complex p k X m).X a)) (BoundedCrystalline.CrystallineCohomology.structureSheaf
      (p := p) (J := Ideal.span {(p : WittVector p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n) (q + 1)) := by
  let : Subsingleton (Abelian.Ext.{u + 2} ((WittPresentationResolution.complex p k X n).X a)
      (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : WittVector p k)})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) n) (q + 1)) :=
    BoundedFrame.ResolutionAcyclicity.subsingleton p k (Witt.Crystalline.wittStructureMap p k X) n (WittFrameFamily.Family.frame p k X n) a q
  let e : (T).obj ((WittPresentationResolution.complex p k X m).X a) ≅ (WittPresentationResolution.complex p k X n).X a :=
    (HomologicalComplex.eval _ (.down ℕ) a).mapIso (iso p k X n m hnm).symm
  exact (Etale.Frobenius.extIsoCongr R e (Iso.refl _) (q + 1)).toEquiv.subsingleton

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittResolutionReduction
