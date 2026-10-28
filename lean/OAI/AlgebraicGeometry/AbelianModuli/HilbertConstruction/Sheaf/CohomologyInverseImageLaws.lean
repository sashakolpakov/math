import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.InverseImageCoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExtCohomologyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyInverseImage
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Topology.Sheaves.Abelian

/-! # Cohomology Inverse Image Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyInverseImageLaws

noncomputable section

/-! The actual inverse-image maps on sheaf cohomology satisfy identity and composition after transport by the canonical sheaf isomorphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
universe u

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {X Y Z : TopCat.{u}}

theorem additiveSheafCohomologyInverseImage_id
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (x : CategoryTheory.Sheaf.H F n) :
    CategoryTheory.Sheaf.H.map ((HilbertConstruction.Additive.SheafInverseImageComposition.additiveSheafInverseImageIdIso X).hom.app F) n
      (CohomologyInverseImage.additiveSheafCohomologyInverseImage (𝟙 X) F n x) = x := by
  let Z₀ := AddCommGrpCat.of (ULift.{u} ℤ)
  let C₀ := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj Z₀
  let L : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} (𝟙 X)
  have : L.Additive := Constant.SheafInverseImage.additiveSheafInverseImage_additive (𝟙 X)
  have : PreservesFiniteLimits L := Constant.SheafInverseImage.additiveSheafInverseImage_preservesFiniteLimits (𝟙 X)
  have : PreservesFiniteColimits L :=
    inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} (𝟙 X)))
  let e : L ≅ 𝟭 (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HilbertConstruction.Additive.SheafInverseImageComposition.additiveSheafInverseImageIdIso X
  let a := (Constant.SheafInverseImage.constantSheafInverseImageIso (𝟙 X)).inv.app Z₀
  have ha : a ≫ e.hom.app C₀ = 𝟙 C₀ := by
    dsimp only [a]
    rw [Constant.InverseImageCoherence.constantSheafInverseImage_id]
    change e.inv.app C₀ ≫ e.hom.app C₀ = 𝟙 C₀
    exact e.inv_hom_id_app C₀
  have h := ExtCohomologyTransport.extCohomologyTransport_naturality L
    (𝟭 (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    e.hom a (𝟙 C₀) ha F n x
  exact h.trans (ExtCohomologyTransport.extCohomologyTransport_id C₀ F n x)

theorem additiveSheafCohomologyInverseImage_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (n : ℕ) (x : CategoryTheory.Sheaf.H F n) :
    CategoryTheory.Sheaf.H.map ((HilbertConstruction.Additive.SheafInverseImageComposition.additiveSheafInverseImageCompIso f g).hom.app F) n
      (CohomologyInverseImage.additiveSheafCohomologyInverseImage f _ n
        (CohomologyInverseImage.additiveSheafCohomologyInverseImage g F n x)) =
      CohomologyInverseImage.additiveSheafCohomologyInverseImage (f ≫ g) F n x := by
  let Z₀ := AddCommGrpCat.of (ULift.{u} ℤ)
  let C₀ := (constantSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj Z₀
  let CY := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj Z₀
  let CX := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj Z₀
  let Lg : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} g
  let Lf : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} f
  let Lc : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} (f ≫ g)
  have : Lg.Additive := Constant.SheafInverseImage.additiveSheafInverseImage_additive g
  have : Lf.Additive := Constant.SheafInverseImage.additiveSheafInverseImage_additive f
  have : Lc.Additive := Constant.SheafInverseImage.additiveSheafInverseImage_additive (f ≫ g)
  have : PreservesFiniteLimits Lg := Constant.SheafInverseImage.additiveSheafInverseImage_preservesFiniteLimits g
  have : PreservesFiniteLimits Lf := Constant.SheafInverseImage.additiveSheafInverseImage_preservesFiniteLimits f
  have : PreservesFiniteLimits Lc := Constant.SheafInverseImage.additiveSheafInverseImage_preservesFiniteLimits (f ≫ g)
  have : PreservesFiniteColimits Lg :=
    inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} g))
  have : PreservesFiniteColimits Lf :=
    inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f))
  have : PreservesFiniteColimits Lc :=
    inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} (f ≫ g)))
  let eg : Lg.obj C₀ ≅ CY := (Constant.SheafInverseImage.constantSheafInverseImageIso g).app Z₀
  let ef : Lf.obj CY ≅ CX := (Constant.SheafInverseImage.constantSheafInverseImageIso f).app Z₀
  let ec : Lc.obj C₀ ≅ CX := (Constant.SheafInverseImage.constantSheafInverseImageIso (f ≫ g)).app Z₀
  let e : Lg ⋙ Lf ≅ Lc := HilbertConstruction.Additive.SheafInverseImageComposition.additiveSheafInverseImageCompIso f g
  have hu : (ef.inv ≫ Lf.map eg.inv) ≫ e.hom.app C₀ = ec.inv := by
    have hh := congr_app (congrArg Iso.inv (Constant.InverseImageCoherence.constantSheafInverseImage_comp f g)) Z₀
    change ec.inv ≫ (e.app C₀).inv = (ef.inv ≫ Lf.map eg.inv) ≫ 𝟙 _ at hh
    rw [Category.comp_id] at hh
    change ec.inv ≫ e.inv.app C₀ = ef.inv ≫ Lf.map eg.inv at hh
    exact (congrArg (fun k => k ≫ e.hom.app C₀) hh.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => ec.inv ≫ k) (e.inv_hom_id_app C₀)).trans
          (Category.comp_id _)))
  have hc := ExtCohomologyTransport.extCohomologyTransport_comp Lg Lf eg.inv ef.inv F n x
  have hn := ExtCohomologyTransport.extCohomologyTransport_naturality (Lg ⋙ Lf) Lc e.hom
    (ef.inv ≫ Lf.map eg.inv) ec.inv hu F n x
  change (ExtCohomologyTransport.extCohomologyTransport Lf ef.inv (Lg.obj F) n
      (ExtCohomologyTransport.extCohomologyTransport Lg eg.inv F n x)).comp (Ext.mk₀ (e.hom.app F)) (add_zero n) =
    ExtCohomologyTransport.extCohomologyTransport Lc ec.inv F n x
  exact (congrArg (fun z : Ext.{u} CX ((Lg ⋙ Lf).obj F) n =>
    z.comp (Ext.mk₀ (e.hom.app F)) (add_zero n)) hc).trans hn

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyInverseImageLaws
