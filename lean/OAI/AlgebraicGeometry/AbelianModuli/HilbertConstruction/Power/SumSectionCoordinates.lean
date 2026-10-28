import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Addition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.SectionCoordinates

/-! # Sum Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumSectionCoordinates

noncomputable section

/-! The glued addition isomorphism preserves section-power frames. Ratios
of product numerators are therefore products of the two lower-degree ratios. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

theorem relativePowerFrame_of_section (L : Line.Bundles.LineBundle X) (U : X.Opens)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [IsIso (Ample.LineBundles.pullbackSection U.ι s)] (n : ℕ) :
    (Relative.PowerFrames.relativePowerFrame U.ι L (asIso (Ample.LineBundles.pullbackSection U.ι s)) n).hom =
      Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s n) := by
  have : IsIso (PullbackComparison.powerPullbackComparison U.ι L.sheaf n) :=
    LineBundle.PowerBaseChange.lineBundle_powerPullbackComparison_isIso U.ι L n
  apply (cancel_mono (PullbackComparison.powerPullbackComparison U.ι L.sheaf n)).mp
  rw [Relative.PowerFrames.relativePowerFrame_spec, SectionBaseChange.powerPullbackComparison_section]
  rfl

theorem tensorPowerAddIso_pullback_section_frame
    (L : Line.Bundles.LineBundle X) (U : X.Opens) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    [IsIso (Ample.LineBundles.pullbackSection U.ι s)] (a b : ℕ) :
    Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s (a + b)) ≫
        (Scheme.Modules.pullback U.ι).map (L.tensorPowerAddIso a b).hom ≫
        Tensor.PullbackComparison.tensorPullbackComparison U.ι (L.tensorPower a).sheaf (L.tensorPower b).sheaf =
      Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s a))
        (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s b)) := by
  let i : LineBundle.EndGluing.LineEndFrameOpen L := ⟨U, asIso (Ample.LineBundles.pullbackSection U.ι s)⟩
  have hm : (Scheme.Modules.pullback U.ι).map (L.tensorPowerAddIso a b).hom =
      (SumFrames.localPowerSumIso U.ι L i.frame a b).hom := TensorPower.Addition.powerSumGluingMap_pullback L a b i
  rw [← relativePowerFrame_of_section L U s (a + b), hm]
  change (Relative.PowerFrames.relativePowerFrame U.ι L i.frame (a + b)).hom ≫
    ((Relative.PowerFrames.relativePowerFrame U.ι L i.frame (a + b)).inv ≫ (SumFrames.powerSumFrame U.ι L i.frame a b).hom) ≫ _ = _
  rw [← Category.assoc, Iso.hom_inv_id_assoc]
  change (Relative.TensorFrames.relativeTensorFrame U.ι (L.tensorPower a) (L.tensorPower b)
    (Relative.PowerFrames.relativePowerFrame U.ι L i.frame a) (Relative.PowerFrames.relativePowerFrame U.ι L i.frame b)).hom ≫ _ = _
  rw [Relative.TensorFrames.relativeTensorFrame_spec, relativePowerFrame_of_section, relativePowerFrame_of_section]

local instance powerSectionPullback_isIso (L : Line.Bundles.LineBundle X) (U : X.Opens)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [IsIso (Ample.LineBundles.pullbackSection U.ι s)] (n : ℕ) :
    IsIso (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s n)) := by
  rw [← relativePowerFrame_of_section L U s n]
  infer_instance

theorem tensorPowerAddIso_product_coordinate
    (L : Line.Bundles.LineBundle X) (U : X.Opens) (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    [IsIso (Ample.LineBundles.pullbackSection U.ι s)] (a b : ℕ)
    (t : Line.Bundles.structureModule X ⟶ (L.tensorPower a).sheaf)
    (v : Line.Bundles.structureModule X ⟶ (L.tensorPower b).sheaf) :
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s (a + b)))
      (Ample.LineBundles.pullbackSection U.ι (Tensor.ProductSections.tensorProductSection t v ≫ (L.tensorPowerAddIso a b).inv)) =
      Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s a)) (Ample.LineBundles.pullbackSection U.ι t) *
        Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s b)) (Ample.LineBundles.pullbackSection U.ι v) := by
  let F := Scheme.Modules.pullback U.ι
  let e : F.obj (L.tensorPower (a + b)).sheaf ≅
      Tensor.ProductSheaf.tensorModule (F.obj (L.tensorPower a).sheaf) (F.obj (L.tensorPower b).sheaf) :=
    F.mapIso (L.tensorPowerAddIso a b) ≪≫
      asIso (Tensor.PullbackComparison.tensorPullbackComparison U.ι (L.tensorPower a).sheaf (L.tensorPower b).sheaf)
  have hd : Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s (a + b)) ≫ e.hom =
      Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s a))
        (Ample.LineBundles.pullbackSection U.ι (TensorPower.Maps.tensorPowerSection s b)) :=
    tensorPowerAddIso_pullback_section_frame L U s a b
  have ht : Ample.LineBundles.pullbackSection U.ι (Tensor.ProductSections.tensorProductSection t v ≫ (L.tensorPowerAddIso a b).inv) ≫
      e.hom = Tensor.ProductSections.tensorProductSection (Ample.LineBundles.pullbackSection U.ι t) (Ample.LineBundles.pullbackSection U.ι v) := by
    rw [SectionTransitions.pullbackSection_postcomp]
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [Category.assoc, ← Category.assoc (F.map (L.tensorPowerAddIso a b).inv),
      ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.id_comp,
      Tensor.SectionBaseChange.tensorPullbackComparison_section]
  exact (Frame.FrameRestriction.frameCoordinate_targetIso _ _ e).symm.trans
    ((Frame.FrameRestriction.frameCoordinate_congr hd ht).trans (Tensor.SectionCoordinates.frameCoordinate_tensorProduct _ _ _ _))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumSectionCoordinates
