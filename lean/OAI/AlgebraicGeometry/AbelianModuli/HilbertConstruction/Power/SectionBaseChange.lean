import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # Section Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionBaseChange

noncomputable section

/-! Taking tensor powers of sections commutes with the canonical arbitrary-pullback comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem powerPullbackComparison_unit_inverse (f : X ⟶ Y) (n : ℕ) :
    (Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map (TensorPower.Maps.tensorPowerUnitIso Y n).inv ≫
      PullbackComparison.powerPullbackComparison f (Line.Bundles.structureModule Y) n =
      (TensorPower.Maps.tensorPowerUnitIso X n).inv ≫ TensorPower.Maps.tensorPowerMap (Line.Bundles.structureModulePullbackIso f).inv n := by
  let u : (Scheme.Modules.pullback f).obj (TensorPower.PowerSheaf.tensorPowerModule (Line.Bundles.structureModule Y) n) ≅
      Line.Bundles.structureModule X := (Scheme.Modules.pullback f).mapIso (TensorPower.Maps.tensorPowerUnitIso Y n) ≪≫
    Line.Bundles.structureModulePullbackIso f
  let v : TensorPower.PowerSheaf.tensorPowerModule ((Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y)) n ≅
      Line.Bundles.structureModule X := (TensorPower.Maps.tensorPowerFunctor X n).mapIso (Line.Bundles.structureModulePullbackIso f) ≪≫
    TensorPower.Maps.tensorPowerUnitIso X n
  have h : PullbackComparison.powerPullbackComparison f (Line.Bundles.structureModule Y) n ≫ v.hom = u.hom :=
    PullbackUnits.powerPullbackComparison_unit_formula f n
  have hi : u.inv ≫ PullbackComparison.powerPullbackComparison f (Line.Bundles.structureModule Y) n = v.inv := by
    apply (cancel_mono v.hom).mp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => u.inv ≫ a) h).trans
        (u.inv_hom_id.trans v.inv_hom_id.symm))
  exact (Category.assoc _ _ _).symm.trans hi

theorem powerPullbackComparison_section (f : X ⟶ Y) {L : Y.Modules}
    (s : Line.Bundles.structureModule Y ⟶ L) (n : ℕ) :
    Ample.LineBundles.pullbackSection f (TensorPower.Maps.tensorPowerSection s n) ≫ PullbackComparison.powerPullbackComparison f L n =
      TensorPower.Maps.tensorPowerSection (Ample.LineBundles.pullbackSection f s) n := by
  change ((Line.Bundles.structureModulePullbackIso f).inv ≫
    (Scheme.Modules.pullback f).map ((TensorPower.Maps.tensorPowerUnitIso Y n).inv ≫ TensorPower.Maps.tensorPowerMap s n)) ≫
      PullbackComparison.powerPullbackComparison f L n =
    (TensorPower.Maps.tensorPowerUnitIso X n).inv ≫
      TensorPower.Maps.tensorPowerMap ((Line.Bundles.structureModulePullbackIso f).inv ≫ (Scheme.Modules.pullback f).map s) n
  rw [Functor.map_comp, TensorPower.Maps.tensorPowerMap_comp]
  simp only [Category.assoc]
  rw [PullbackComparison.powerPullbackComparison_natural]
  exact (congrArg (fun a => a ≫ TensorPower.Maps.tensorPowerMap ((Scheme.Modules.pullback f).map s) n)
    (powerPullbackComparison_unit_inverse f n)).trans (Category.assoc _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionBaseChange
