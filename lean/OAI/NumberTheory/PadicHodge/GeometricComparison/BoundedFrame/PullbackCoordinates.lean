import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheafNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameGeometricMap

/-! # Pullback Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackCoordinates.BoundedFramePullbackCoordinates

noncomputable section

/-! The natural combined product-map construction is the original
general geometric frame sheaf map, including for non-monomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (F : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "SX" => Functor.mapHomologicalComplex
  (IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n) (ComplexShape.up ℕ)

theorem comparison_refl : PullbackDiagram.BoundedFramePullbackDiagram.comparison g hg n F ((G).obj F) (𝟙 _) =
    IntegralComparison.BoundedGeneral.GeneralFrameComparison.comparison g hg n F := by
  apply NatTrans.ext
  funext U
  change (QY).map (prod.lift ((G).map prod.fst ≫ 𝟙 _) ((G).map prod.snd)) =
    (QY).map (prodComparison G F U)
  rw [Category.comp_id]
  rfl

theorem diagram_refl : PullbackComplex.BoundedFramePullbackComplex.diagramMap g hg n F ((G).obj F) (𝟙 _) =
    IntegralComparison.BoundedGeneral.FrameRestriction.diagramMap g hg n F := by
  unfold PullbackComplex.BoundedFramePullbackComplex.diagramMap IntegralComparison.BoundedGeneral.FrameRestriction.diagramMap
  congr 1

theorem presheaf_refl : PullbackComplex.BoundedFramePullbackComplex.map g hg n F ((G).obj F) (𝟙 _) =
    IntegralComparison.BoundedGeneral.FrameRestriction.presheafMap g hg n F :=
  congrArg (fun a => (IntegralComparison.BoundedGeneral.FrameRestriction.restrictionIso g hg n F).hom ≫ a ≫
    (IntegralComparison.BoundedGeneral.FrameRestriction.postcomposeIso g hg n F).hom) (diagram_refl g hg n F)

theorem sheaf_refl : PullbackSheaf.BoundedFramePullbackSheaf.map g hg n F ((G).obj F) (𝟙 _) =
    IntegralComparison.BoundedGeneral.FrameSheafMap.map g hg n F :=
  congrArg (fun a => ((NatIso.mapHomologicalComplex
    (IntegralComparison.BoundedFrame.SheafRestriction.sheafificationIso g hg n) (.up ℕ)).app
      (IntegralComparison.BoundedFrame.Diagram.complex ((G).obj F))).hom ≫ (SX).map a) (presheaf_refl g hg n F)

variable {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj F ⟶ FY)

theorem factor : ((R).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.BoundedFrame.Change.sheafMap α) ≫
    PullbackSheaf.BoundedFramePullbackSheaf.map g hg n F ((G).obj F) (𝟙 _) =
      PullbackSheaf.BoundedFramePullbackSheaf.map g hg n F FY α := by
  have h := PullbackSheafNaturality.BoundedFramePullbackSheafNaturality.natural g hg n (𝟙 F) α (𝟙 _) α
    (by
      exact (congrArg (fun a => a ≫ α) ((G).map_id F)).trans (Category.id_comp α))
  have hi : IntegralComparison.BoundedFrame.Change.sheafMap (𝟙 F) = 𝟙 _ :=
    (ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n).map_id (op F)
  exact h.trans ((congrArg (fun a => PullbackSheaf.BoundedFramePullbackSheaf.map g hg n F FY α ≫ a) hi).trans
    (Category.comp_id _))

theorem map_eq : PullbackSheaf.BoundedFramePullbackSheaf.map g hg n F FY α =
    IntegralComparison.BoundedGeneral.FrameGeometricMap.map g hg n α :=
  (factor g hg n F α).symm.trans
    (congrArg (fun a => ((R).mapHomologicalComplex (.up ℕ)).map (IntegralComparison.BoundedFrame.Change.sheafMap α) ≫ a)
      (sheaf_refl g hg n F))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackCoordinates.BoundedFramePullbackCoordinates
