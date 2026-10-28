import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyPullbackMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyInverseImageLaws
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageIdentity

/-! # Cohomology Pullback Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyPullbackLaws

noncomputable section

/-! Actual Zariski cohomology pullback respects identities and composition of scheme maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false

namespace ZariskiCohomology

variable {X Y Z : Scheme.{u}}

theorem pullbackMap_id (M : X.Modules) (n : ℕ) (x : Cohomology.ZariskiCohomology.H M n) :
    (Cohomology.ZariskiCohomology.zariskiFunctor X n).map ((Scheme.Modules.pullbackId X).hom.app M)
      (CohomologyPullbackMap.ZariskiCohomology.pullbackMap (𝟙 X) M n x) = x := by
  change CategoryTheory.Sheaf.H.map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pullbackId X).hom.app M)) n
      (CategoryTheory.Sheaf.H.map (Module.InverseImageComparison.moduleInverseImageComparison (𝟙 X) M) n
        (HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage (𝟙 X.carrier) _ n x)) = x
  rw [← CategoryTheory.Sheaf.H.map_comp_apply, Module.InverseImageIdentity.moduleInverseImageComparison_id]
  exact HilbertConstruction.Sheaf.CohomologyInverseImageLaws.additiveSheafCohomologyInverseImage_id _ n x

theorem pullbackMap_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (n : ℕ) (x : Cohomology.ZariskiCohomology.H M n) :
    (Cohomology.ZariskiCohomology.zariskiFunctor X n).map ((Scheme.Modules.pullbackComp f g).inv.app M)
      (CohomologyPullbackMap.ZariskiCohomology.pullbackMap (f ≫ g) M n x) =
    CohomologyPullbackMap.ZariskiCohomology.pullbackMap f ((Scheme.Modules.pullback g).obj M) n (CohomologyPullbackMap.ZariskiCohomology.pullbackMap g M n x) := by
  let FX : X.carrier.Sheaf AddCommGrpCat.{u} :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M))
  let FY : Y.carrier.Sheaf AddCommGrpCat.{u} :=
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback g).obj M)
  let FZ : Z.carrier.Sheaf AddCommGrpCat.{u} := (SheafOfModules.toSheaf Z.ringCatSheaf).obj M
  let FC : X.carrier.Sheaf AddCommGrpCat.{u} :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj ((Scheme.Modules.pullback (f ≫ g)).obj M)
  let Lf : Y.carrier.Sheaf AddCommGrpCat.{u} ⥤ X.carrier.Sheaf AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base
  let Lg : Z.carrier.Sheaf AddCommGrpCat.{u} ⥤ Y.carrier.Sheaf AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} g.base
  let Lc : Z.carrier.Sheaf AddCommGrpCat.{u} ⥤ X.carrier.Sheaf AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} (f.base ≫ g.base)
  let e : Lg ⋙ Lf ≅ Lc := Additive.SheafInverseImageComposition.additiveSheafInverseImageCompIso f.base g.base
  let a : Lg.obj FZ ⟶ FY := Module.InverseImageComparison.moduleInverseImageComparison g M
  let b : Lf.obj FY ⟶ FX := Module.InverseImageComparison.moduleInverseImageComparison f ((Scheme.Modules.pullback g).obj M)
  let d : Lc.obj FZ ⟶ FC := Module.InverseImageComparison.moduleInverseImageComparison (f ≫ g) M
  let c : FC ⟶ FX := (SheafOfModules.toSheaf X.ringCatSheaf).map
    ((Scheme.Modules.pullbackComp f g).inv.app M)
  let HX : X.carrier.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    CategoryTheory.Sheaf.functorH _ n
  let y : HX.obj (Lc.obj FZ) := HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage (f.base ≫ g.base) FZ n x
  let z : HX.obj (Lf.obj (Lg.obj FZ)) := HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage f.base _ n
    (HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage g.base FZ n x)
  have hc : HX.map (e.hom.app FZ) z = y :=
    HilbertConstruction.Sheaf.CohomologyInverseImageLaws.additiveSheafCohomologyInverseImage_comp f.base g.base FZ n x
  have hz : HX.map (e.inv.app FZ) y = z := by
    rw [← hc, ← ConcreteCategory.comp_apply, ← HX.map_comp, e.hom_inv_id_app, HX.map_id]
    rfl
  have hm : d ≫ c = e.inv.app FZ ≫ Lf.map a ≫ b := Module.InverseImageComposition.moduleInverseImageComparison_comp_inv f g M
  have hn : HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage f.base FY n
      (CategoryTheory.Sheaf.H.map a n (HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage g.base FZ n x)) =
        HX.map (Lf.map a) z :=
    HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage_naturality f.base a n
      (HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage g.base FZ n x)
  change HX.map c (HX.map d y) = HX.map b
    (HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage f.base FY n
      (CategoryTheory.Sheaf.H.map a n (HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage g.base FZ n x)))
  calc
    _ = HX.map (d ≫ c) y := (ConcreteCategory.congr_hom (HX.map_comp d c) y).symm
    _ = HX.map (e.inv.app FZ ≫ Lf.map a ≫ b) y :=
      congrArg (fun k : Lc.obj FZ ⟶ FX => HX.map k y) hm
    _ = HX.map b (HX.map (Lf.map a) (HX.map (e.inv.app FZ) y)) := by
      rw [HX.map_comp, HX.map_comp]
      rfl
    _ = HX.map b (HX.map (Lf.map a) z) := congrArg (fun w => HX.map b (HX.map (Lf.map a) w)) hz
    _ = _ := congrArg (fun w => HX.map b w) hn.symm

theorem pullbackMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (n : ℕ) (x : Cohomology.ZariskiCohomology.H M n) :
    CohomologyPullbackMap.ZariskiCohomology.pullbackMap (f ≫ g) M n x =
      (Cohomology.ZariskiCohomology.zariskiFunctor X n).map ((Scheme.Modules.pullbackComp f g).hom.app M)
        (CohomologyPullbackMap.ZariskiCohomology.pullbackMap f ((Scheme.Modules.pullback g).obj M) n (CohomologyPullbackMap.ZariskiCohomology.pullbackMap g M n x)) := by
  let e := (Cohomology.ZariskiCohomology.zariskiFunctor X n).mapIso ((Scheme.Modules.pullbackComp f g).app M)
  calc
    _ = e.hom (e.inv (CohomologyPullbackMap.ZariskiCohomology.pullbackMap (f ≫ g) M n x)) := by
      rw [← ConcreteCategory.comp_apply, e.inv_hom_id]
      rfl
    _ = _ := congrArg e.hom (pullbackMap_comp_inv f g M n x)

end ZariskiCohomology

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyPullbackLaws
