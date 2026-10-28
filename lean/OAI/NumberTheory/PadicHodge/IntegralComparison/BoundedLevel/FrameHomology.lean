import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePulledMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Homotopy

/-! # Frame Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameHomology

noncomputable section

/-! Frame comparison between bounded levels yields the original coefficient-linear restriction identity on homology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m) (FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f m FY)]
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))
  (FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n FX)]
  (α : (BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm).obj FX ⟶ FY)

local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
  (BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n) 0

def globalComparison :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (.up ℕ)).obj
      (BoundedFrame.DeRhamSections.frameComplex f m FY) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj (IX).cocomplex :=
  ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (BoundedFrame.DeRhamSections.frameComplex f m FY) (IX).cocomplex
    (FramePulledMap.map f n m hnm (FY := FY) ≫
      FrameHomotopy.globalMap f n m hnm FY I)

def localComparison :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (.up ℕ)).obj
      (BoundedFrame.DeRhamSections.frameComplex f m FY) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj (IX).cocomplex :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (.up ℕ)).map
    (BoundedFrame.SectionChange.frameMap α) ≫ BoundedFrame.DeRhamSections.sectionsMap f n FX ≫
      ((S).mapHomologicalComplex (.up ℕ)).map (BoundedFrame.Injective.Comparison.map f n FX IX)

omit [QuasiIso (Bounded.RelativeSheafComplex.augmentation f m FY)] in
theorem local_component (i : ℕ) :
    (ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
      (BoundedFrame.DeRhamSections.frameComplex f m FY) (IX).cocomplex
      (FramePulledMap.map f n m hnm (FY := FY) ≫
        FrameHomotopy.localMap f n m hnm FY I FX α)).f i =
          (localComparison f n m hnm FY I FX α).f i := by
  let T := S
  have h := ConstantSection.ComplexComposition.component.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (BoundedFrame.DeRhamSections.frameComplex f m FY)
    (FramePulledMap.map f n m hnm (FY := FY))
    (FrameHomotopy.localMap f n m hnm FY I FX α) i
  exact h.trans
    ((congrArg (fun a =>
      (ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
        (BoundedFrame.DeRhamSections.frameComplex f m FY) _
        (FramePulledMap.map f n m hnm (FY := FY))).f i ≫ a)
      (T.map_comp ((FrameMap.map f n m hnm α).f i)
        ((BoundedFrame.Injective.Comparison.map f n FX IX).f i))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ T.map ((BoundedFrame.Injective.Comparison.map f n FX IX).f i))
          (FramePulledMap.sections_component f n m hnm α i)).trans (Category.assoc _ _ _))))

omit [QuasiIso (Bounded.RelativeSheafComplex.augmentation f m FY)] in
theorem local_eq : ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (BoundedFrame.DeRhamSections.frameComplex f m FY) (IX).cocomplex
    (FramePulledMap.map f n m hnm (FY := FY) ≫
      FrameHomotopy.localMap f n m hnm FY I FX α) = localComparison f n m hnm FY I FX α := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact local_component f n m hnm FY I FX α i

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (globalComparison f n m hnm FY I) i =
    HomologicalComplex.homologyMap (localComparison f n m hnm FY I FX α) i :=
  (ConstantSection.Homotopy.homology.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (BoundedFrame.DeRhamSections.frameComplex f m FY) (FramePulledMap.map f n m hnm (FY := FY))
    (FrameHomotopy.globalMap f n m hnm FY I)
    (FrameHomotopy.localMap f n m hnm FY I FX α)
    (FrameHomotopy.homotopy f n m hnm FY I FX α) i).trans
      (congrArg (fun a => HomologicalComplex.homologyMap a i) (local_eq f n m hnm FY I FX α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameHomology
