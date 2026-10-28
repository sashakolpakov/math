import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagramNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeDiagram

/-! # Pullback Presheaf Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackPresheafNaturality.BoundedFramePullbackPresheafNaturality

noncomputable section

/-! Arbitrary geometric pullback of the actual relative presheaf
complexes commutes with compatible changes of crystalline frames. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagram.BoundedFramePullbackDiagram
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {FX FX' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY FY' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (a : FX ⟶ FX') (b : FY ⟶ FY')
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)
  (α' : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX' ⟶ FY')

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction.restriction (B := B) G

def sourceOverMap : Over.mk (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) ⟶ Over.mk (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX') :=
  Over.homMk (Functor.whiskerRight (IntegralComparison.BoundedFrame.Change.diagramMap a) T) (by
    apply NatTrans.ext
    funext U
    change (T).map ((IntegralComparison.BoundedFrame.Change.diagramMap a).app U) ≫
        (T).map ((IntegralComparison.BoundedFrame.Diagram.projection FX').app U) =
      (T).map ((IntegralComparison.BoundedFrame.Diagram.projection FX).app U)
    rw [← Functor.map_comp]
    exact congrArg (T).map (congrArg (fun z => z.app U) (IntegralComparison.BoundedFrame.Change.projection a)))

def targetOverMap : Over.mk (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY) ⟶ Over.mk (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY') :=
  Over.homMk (Functor.whiskerLeft G (IntegralComparison.BoundedFrame.Change.diagramMap b))
    (RelativeComplex.RelativeComplexRestrictionNaturality.projection G _ _ _ _ _ _ (IntegralComparison.BoundedFrame.Change.projection b))

def comparisonOverMap : Over.mk (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) ⟶ Over.mk (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY) :=
  Over.homMk (PullbackDiagram.BoundedFramePullbackDiagram.comparison g hg n FX FY α) (PullbackDiagram.BoundedFramePullbackDiagram.projection g hg n FX FY α)

def sourceMap : IntegralComparison.RelativeCrystalline.ModuleComplex.complex (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX')
    (G ⋙ QY) (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX') ⟶
      IntegralComparison.RelativeCrystalline.ModuleComplex.complex (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX) (G ⋙ QY) (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) :=
  IntegralComparison.Relative.DiagramComplexMap.map (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX) (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX') (G ⋙ QY)
    (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX')
    (Functor.whiskerRight (IntegralComparison.BoundedFrame.Change.diagramMap a) T) (Over.w (sourceOverMap g hg n a))

def targetMap : IntegralComparison.RelativeCrystalline.ModuleComplex.complex (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY')
    (G ⋙ QY) (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY') ⟶
      IntegralComparison.RelativeCrystalline.ModuleComplex.complex (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY) (G ⋙ QY) (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY) :=
  IntegralComparison.Relative.DiagramComplexMap.map (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY) (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY') (G ⋙ QY)
    (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY) (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY')
    (Functor.whiskerLeft G (IntegralComparison.BoundedFrame.Change.diagramMap b)) (Over.w (targetOverMap g hg n b))

omit [IsSeparated fY] in
theorem source_map : sourceMap g hg n a ≫
    (PullbackComplex.BoundedFramePullbackComplex.postcomposeIso g hg n FX).hom =
      (PullbackComplex.BoundedFramePullbackComplex.postcomposeIso g hg n FX').hom ≫ IntegralComparison.BoundedFrame.Change.presheafMap a := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem diagram_natural (h : (G).map a ≫ α' = α ≫ b) :
    targetMap g hg n b ≫
      PullbackComplex.BoundedFramePullbackComplex.diagramMap g hg n FX FY α =
    PullbackComplex.BoundedFramePullbackComplex.diagramMap g hg n FX' FY' α' ≫
      sourceMap g hg n a :=
  RelativeDiagram.RelativeDiagramSquare.square (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX) (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX')
    (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY) (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY') (G ⋙ QY)
    (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX')
    (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY) (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY')
    (Functor.whiskerRight (IntegralComparison.BoundedFrame.Change.diagramMap a) T)
    (Functor.whiskerLeft G (IntegralComparison.BoundedFrame.Change.diagramMap b))
    (PullbackDiagram.BoundedFramePullbackDiagram.comparison g hg n FX FY α) (PullbackDiagram.BoundedFramePullbackDiagram.comparison g hg n FX' FY' α')
    (Over.w (sourceOverMap g hg n a)) (Over.w (targetOverMap g hg n b))
    (PullbackDiagram.BoundedFramePullbackDiagram.projection g hg n FX FY α) (PullbackDiagram.BoundedFramePullbackDiagram.projection g hg n FX' FY' α')
    (PullbackDiagramNaturality.BoundedFramePullbackDiagramNaturality.natural g hg n a b α α' h)

theorem natural (h : (G).map a ≫ α' = α ≫ b) :
    ((R).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.BoundedFrame.Change.presheafMap b) ≫
      PullbackComplex.BoundedFramePullbackComplex.map g hg n FX FY α =
    PullbackComplex.BoundedFramePullbackComplex.map g hg n FX' FY' α' ≫ IntegralComparison.BoundedFrame.Change.presheafMap a := by
  have h₁ := RelativeComplex.RelativeComplexRestrictionNaturality.natural G _ _ _ _ _ _
    (IntegralComparison.BoundedFrame.Change.projection b)
  have h₂ := diagram_natural g hg n a b α α' h
  have h₃ := source_map g hg n a
  have h₂₃ := ExactHomology.ExactHomologyComparison.compose
    (targetMap g hg n b)
    (PullbackComplex.BoundedFramePullbackComplex.diagramMap g hg n FX FY α)
    (PullbackComplex.BoundedFramePullbackComplex.postcomposeIso g hg n FX).hom
    (PullbackComplex.BoundedFramePullbackComplex.diagramMap g hg n FX' FY' α')
    (sourceMap g hg n a)
    (PullbackComplex.BoundedFramePullbackComplex.postcomposeIso g hg n FX').hom
    (IntegralComparison.BoundedFrame.Change.presheafMap a) h₂ h₃
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂₃

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackPresheafNaturality.BoundedFramePullbackPresheafNaturality
