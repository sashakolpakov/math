import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelDiagramNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameRestriction

/-! # Level Presheaf Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelPresheafNaturality.BoundedLevelPresheafNaturality

noncomputable section

/-! The actual presheaf-complex comparison between bounded levels is
natural in the frame, including its canonical product isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.LevelFrameComparison
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "Qm" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction.restriction (B := B) G

variable {F F' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n} (α : F ⟶ F')

def sourceOverMap : Over.mk (IntegralComparison.BoundedLevel.LevelFrameComparison.sourceProjection f n m hnm F) ⟶
    Over.mk (IntegralComparison.BoundedLevel.LevelFrameComparison.sourceProjection f n m hnm F') :=
  Over.homMk (IntegralComparison.BoundedFrame.Change.diagramMap α) (IntegralComparison.BoundedFrame.Change.projection α)

def targetOverMap : Over.mk (IntegralComparison.BoundedLevel.LevelFrameComparison.targetProjection f n m hnm F) ⟶
    Over.mk (IntegralComparison.BoundedLevel.LevelFrameComparison.targetProjection f n m hnm F') :=
  Over.homMk (Functor.whiskerLeft G (IntegralComparison.BoundedFrame.Change.diagramMap ((G).map α)))
    (RelativeComplex.RelativeComplexRestrictionNaturality.projection G _ _ _ _ _ _
      (IntegralComparison.BoundedFrame.Change.projection ((G).map α)))

theorem diagram_natural :
    (IntegralComparison.Relative.ResolutionFunctor.functor (G ⋙ Qm)).map (targetOverMap f n m hnm α).op ≫
      (IntegralComparison.BoundedLevel.FrameRestriction.diagramIso f n m hnm F).hom =
    (IntegralComparison.BoundedLevel.FrameRestriction.diagramIso f n m hnm F').hom ≫
      IntegralComparison.BoundedFrame.Change.presheafMap α := by
  let T := IntegralComparison.Relative.ResolutionFunctor.functor (G ⋙ Qm)
  let cF := IntegralComparison.Relative.ResolutionFunctor.overIso (G ⋙ Qm) (IntegralComparison.BoundedLevel.LevelFrameComparison.sourceProjection f n m hnm F)
    (IntegralComparison.BoundedLevel.LevelFrameComparison.targetProjection f n m hnm F) (asIso (IntegralComparison.BoundedLevel.LevelFrameComparison.comparison f n m hnm F)) (IntegralComparison.BoundedLevel.LevelFrameComparison.projection f n m hnm F)
  let cF' := IntegralComparison.Relative.ResolutionFunctor.overIso (G ⋙ Qm) (IntegralComparison.BoundedLevel.LevelFrameComparison.sourceProjection f n m hnm F')
    (IntegralComparison.BoundedLevel.LevelFrameComparison.targetProjection f n m hnm F') (asIso (IntegralComparison.BoundedLevel.LevelFrameComparison.comparison f n m hnm F')) (IntegralComparison.BoundedLevel.LevelFrameComparison.projection f n m hnm F')
  change T.map (targetOverMap f n m hnm α).op ≫ T.map cF.hom.op =
    T.map cF'.hom.op ≫ T.map (sourceOverMap f n m hnm α).op
  rw [← T.map_comp, ← T.map_comp]
  apply congrArg T.map
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  exact (LevelDiagramNaturality.BoundedLevelDiagramNaturality.natural f n m hnm α).symm

theorem natural :
    ((R).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.BoundedFrame.Change.presheafMap ((G).map α)) ≫
      (IntegralComparison.BoundedLevel.FrameRestriction.presheafIso f n m hnm F).hom =
    (IntegralComparison.BoundedLevel.FrameRestriction.presheafIso f n m hnm F').hom ≫
      IntegralComparison.BoundedFrame.Change.presheafMap α := by
  have h₁ := RelativeComplex.RelativeComplexRestrictionNaturality.natural G _ _ _ _ _ _
    (IntegralComparison.BoundedFrame.Change.projection ((G).map α))
  have h₂ := diagram_natural f n m hnm α
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (IntegralComparison.BoundedLevel.FrameRestriction.diagramIso f n m hnm F).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => (IntegralComparison.BoundedLevel.FrameRestriction.restrictionIso f n m hnm F').hom ≫ a) h₂).trans
          (Category.assoc _ _ _).symm)))

def iso : (G).op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor f m ⋙
    (R).mapHomologicalComplex (.up ℕ) ≅ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.presheafFunctor f n :=
  NatIso.ofComponents (fun F => IntegralComparison.BoundedLevel.FrameRestriction.presheafIso f n m hnm F.unop)
    (fun α => natural f n m hnm α.unop)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelPresheafNaturality.BoundedLevelPresheafNaturality
