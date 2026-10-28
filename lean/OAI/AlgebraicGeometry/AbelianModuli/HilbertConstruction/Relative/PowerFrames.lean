import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.ProductPullbacks

/-! # Power Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.PowerFrames

noncomputable section

/-! Frames of pulled-back tensor powers and their compatibility with composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

def relativePowerFrame (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) (n : ℕ) :
    Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) := by
  let : IsIso (Power.PullbackComparison.powerPullbackComparison f L.sheaf n) := LineBundle.PowerBaseChange.lineBundle_powerPullbackComparison_isIso f L n
  exact asIso (TensorPower.Maps.tensorPowerSection e.hom n) ≪≫ (asIso (Power.PullbackComparison.powerPullbackComparison f L.sheaf n)).symm

theorem relativePowerFrame_spec (f : X ⟶ Y) (L : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf) (n : ℕ) :
    (relativePowerFrame f L e n).hom ≫ Power.PullbackComparison.powerPullbackComparison f L.sheaf n =
      TensorPower.Maps.tensorPowerSection e.hom n := by
  let : IsIso (Power.PullbackComparison.powerPullbackComparison f L.sheaf n) := LineBundle.PowerBaseChange.lineBundle_powerPullbackComparison_isIso f L n
  change (TensorPower.Maps.tensorPowerSection e.hom n ≫ inv (Power.PullbackComparison.powerPullbackComparison f L.sheaf n)) ≫
    Power.PullbackComparison.powerPullbackComparison f L.sheaf n = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

def compositeBundleFrame (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line.Bundles.LineBundle Z)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj L.sheaf) :
    Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback (f ≫ g)).obj L.sheaf :=
  (Line.Bundles.structureModulePullbackIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫
    (Scheme.Modules.pullbackComp f g).app L.sheaf

theorem relativePowerFrame_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line.Bundles.LineBundle Z)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj L.sheaf) (n : ℕ) :
    Ample.LineBundles.pullbackSection f (relativePowerFrame g L e n).hom ≫
      (Scheme.Modules.pullbackComp f g).hom.app (TensorPower.PowerSheaf.tensorPowerModule L.sheaf n) =
      (relativePowerFrame (f ≫ g) L (compositeBundleFrame f g L e) n).hom := by
  let : IsIso (Power.PullbackComparison.powerPullbackComparison (f ≫ g) L.sheaf n) :=
    LineBundle.PowerBaseChange.lineBundle_powerPullbackComparison_isIso (f ≫ g) L n
  apply (cancel_mono (Power.PullbackComparison.powerPullbackComparison (f ≫ g) L.sheaf n)).mp
  rw [relativePowerFrame_spec, Category.assoc, ← Power.PullbackComposition.powerPullbackComparison_comp]
  rw [← Category.assoc, ← Power.SectionTransitions.pullbackSection_postcomp, relativePowerFrame_spec,
    ← Category.assoc, Power.SectionBaseChange.powerPullbackComparison_section, TensorPower.ProductPullbacks.tensorPowerSection_postcomp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.PowerFrames
