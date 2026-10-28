import OAI.NumberTheory.PadicHodge.IntegralComparison.Presentation.FamilyMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ReductionFrameHomEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameReduction
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittTupleFlatness
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps

/-! # Witt Presentation Reduction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittPresentationReduction

noncomputable section

/-! The native presentation presheaf at a lower Witt level is the restriction of the higher-level presentation presheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (n m : ℕ) (hnm : n ≤ m)

def inclusion : WittTupleFlatness.Objects p k X n ⥤ WittTupleFlatness.Objects p k X m :=
  BoundedCrystalline.LevelMaps.inclusion (Witt.Crystalline.wittStructureMap p k X) n m hnm

def frameMap (i : StandardCover.Index k X) : (inclusion p k X n m hnm).obj (WittFrameFamily.Family.frame p k X n i) ⟶ WittFrameFamily.Family.frame p k X m i :=
  ObjectProperty.homMk (WittFrameReduction.morphism p k X n m hnm i)

theorem hom_bijective (U : WittTupleFlatness.Objects p k X n) (i : StandardCover.Index k X) :
    Function.Bijective (fun a : U ⟶ WittFrameFamily.Family.frame p k X n i => (inclusion p k X n m hnm).map a ≫ frameMap p k X n m hnm i) := by
  have h := ReductionFrameHomEquiv.bijective (Witt.Crystalline.wittStructureMap p k X) n U (WittFrameFamily.Family.frame p k X n i)
    (WittFrameFamily.Family.frame p k X m i).obj (WittFrameReduction.iso p k X n m hnm i)
    (WittFrameReduction.morphism p k X n m hnm i)
    (WittFrameReduction.iso_hom p k X n m hnm i)
  constructor
  · intro a b hab
    apply h.1
    exact congrArg (fun c => c.hom) hab
  · intro b
    obtain ⟨a, ha⟩ := h.2 b.hom
    refine ⟨a, ?_⟩
    apply (BoundedCrystalline.Site.inclusion (Witt.Crystalline.wittStructureMap p k X) m).map_injective
    exact ha

def map : CoveringPresentationPresheaf.presentations.{u + 1, u} (WittFrameFamily.Family.frame p k X n) ⟶
    (inclusion p k X n m hnm).op ⋙ CoveringPresentationPresheaf.presentations.{u + 1, u} (WittFrameFamily.Family.frame p k X m) :=
  Presentation.FamilyMap.Family.map.{u + 1, u} (inclusion p k X n m hnm) (WittFrameFamily.Family.frame p k X n) (WittFrameFamily.Family.frame p k X m)
    (frameMap p k X n m hnm)

instance map_isIso : IsIso (WittPresentationReduction.map p k X n m hnm) :=
  Presentation.FamilyMap.Family.isIso.{u + 1, u} (inclusion p k X n m hnm) (WittFrameFamily.Family.frame p k X n) (WittFrameFamily.Family.frame p k X m)
    (frameMap p k X n m hnm) (hom_bijective p k X n m hnm)

def iso : CoveringPresentationPresheaf.presentations.{u + 1, u} (WittFrameFamily.Family.frame p k X n) ≅
    (inclusion p k X n m hnm).op ⋙ CoveringPresentationPresheaf.presentations.{u + 1, u} (WittFrameFamily.Family.frame p k X m) :=
  asIso (WittPresentationReduction.map p k X n m hnm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittPresentationReduction
