import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyInverseImage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology

/-! # Cohomology Pullback Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyPullbackMap.ZariskiCohomology

noncomputable section

/-! Arbitrary scheme morphisms induce additive maps from actual Zariski cohomology to the cohomology of the actual pulled-back module sheaf. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem additivePullback_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    {F G : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {F' G' : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : F ⟶ G) (b : F' ⟶ G')
    (u : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ F')
    (v : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G ⟶ G')
    (h : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map a ≫ v = u ≫ b)
    (n : ℕ) (x : (CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology Y) n : _ ⥤ AddCommGrpCat.{u}).obj F) :
    HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyPullbackMap f v n (CategoryTheory.Sheaf.H.map a n x) =
      CategoryTheory.Sheaf.H.map b n (HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyPullbackMap f u n x) := by
  let L : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} f
  let HX : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} := CategoryTheory.Sheaf.functorH _ n
  let y : HX.obj (L.obj F) := HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage f F n x
  have hn := HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage_naturality f a n x
  have h₁ : HX.map v (HX.map (L.map a) y) = HX.map (L.map a ≫ v) y :=
    (ConcreteCategory.congr_hom (HX.map_comp (L.map a) v) y).symm
  have h₂ : HX.map (u ≫ b) y = HX.map b (HX.map u y) :=
    ConcreteCategory.congr_hom (HX.map_comp u b) y
  change HX.map v (HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyInverseImage f G n
    (CategoryTheory.Sheaf.H.map a n x)) = HX.map b (HX.map u y)
  exact (congrArg (fun w : HX.obj (L.obj G) => HX.map v w) hn).trans
    (h₁.trans ((congrArg (fun w : L.obj F ⟶ G' => HX.map w y) h).trans h₂))

variable {X Y : Scheme.{u}}

def pullbackMap (f : X ⟶ Y) (M : Y.Modules) (n : ℕ) :
    Cohomology.ZariskiCohomology.H M n →+ Cohomology.ZariskiCohomology.H ((Scheme.Modules.pullback f).obj M) n :=
  HilbertConstruction.Sheaf.CohomologyInverseImage.additiveSheafCohomologyPullbackMap f.base (Module.InverseImageComparison.moduleInverseImageComparison f M) n

theorem pullbackMap_naturality (f : X ⟶ Y) {M N : Y.Modules}
    (a : M ⟶ N) (n : ℕ) (x : Cohomology.ZariskiCohomology.H M n) :
    pullbackMap f N n ((Cohomology.ZariskiCohomology.zariskiFunctor Y n).map a x) =
      (Cohomology.ZariskiCohomology.zariskiFunctor X n).map ((Scheme.Modules.pullback f).map a)
        (pullbackMap f M n x) := by
  let FY : Y.Modules ⥤ CategoryTheory.Sheaf
      (_root_.Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf Y.ringCatSheaf
  let FX : X.Modules ⥤ CategoryTheory.Sheaf
      (_root_.Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf X.ringCatSheaf
  let P := Scheme.Modules.pullback f
  exact additivePullback_naturality f.base (FY.map a) (FX.map (P.map a))
    (Module.InverseImageComparison.moduleInverseImageComparison f M) (Module.InverseImageComparison.moduleInverseImageComparison f N)
    (Module.InverseImageComparison.moduleInverseImageComparison_naturality f a) n x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.CohomologyPullbackMap.ZariskiCohomology
