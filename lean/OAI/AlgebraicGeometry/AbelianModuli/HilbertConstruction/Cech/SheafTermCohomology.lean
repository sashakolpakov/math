import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.FirstCohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.Differential
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CechFunctorComparison

/-! # Sheaf Term Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafTermCohomology.IntrinsicCech

noncomputable section

/-! Applying genuine cohomology to the sheaf Cech resolution gives the Cech complex of the cohomology of its open factors. Finiteness of the cover supplies preservation of the required products, and the comparison respects every differential. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u

private def cohomologySheafSiteEquivalence (X : TopCat.{u}) :
    X.Sheaf AddCommGrpCat.{u} ≌
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  functor := { obj F := F, map a := a }
  inverse := { obj F := F, map a := a }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

private instance (X : TopCat.{u}) : (cohomologySheafSiteEquivalence X).functor.Additive where
  map_add := by intros; rfl

def nativeSheafCohomologyFunctor (X : TopCat.{u}) (q : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (cohomologySheafSiteEquivalence X).functor ⋙
    CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) q

instance (X : TopCat.{u}) (q : ℕ) : (nativeSheafCohomologyFunctor X q).Additive := by
  dsimp only [nativeSheafCohomologyFunctor]
  infer_instance

instance (X : TopCat.{u}) (q : ℕ) : PreservesFiniteProducts (nativeSheafCohomologyFunctor X q) := by
  dsimp only [nativeSheafCohomologyFunctor]
  infer_instance

variable {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u})
variable {ι : Type u} [Finite ι] (U : ι → Opens X) (q : ℕ)

def cechFactorCohomologyPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  IntrinsicCech.SheafComplex.cechFactorPresheaf F ⋙ nativeSheafCohomologyFunctor X q

def cechTermCohomologyIso (n : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) q).obj (IntrinsicCech.SheafTerms.cechTerm F U n) ≅
      ((cechComplexFunctor U).obj (cechFactorCohomologyPresheaf F q)).X n :=
  PreservesProduct.iso (nativeSheafCohomologyFunctor X q)
    (IntrinsicCech.SheafTerms.cechTermFactor F U n)

@[reassoc]
theorem cechTermCohomologyIso_hom_π (n : ℕ) (i : Fin (n + 1) → ι) :
    (cechTermCohomologyIso F U q n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) q).obj
            (IntrinsicCech.SheafTerms.cechTermFactor F U n j)) i =
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) q).map
        (Pi.π (IntrinsicCech.SheafTerms.cechTermFactor F U n) i) :=
  piComparison_comp_π _ _ i

theorem cechTermCohomologyIso_coface (n : ℕ) (k : Fin (n + 2)) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) q).map (SheafCofaces.IntrinsicCech.cechCoface F U n k) ≫
        (cechTermCohomologyIso F U q (n + 1)).hom =
      (cechTermCohomologyIso F U q n).hom ≫
        ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj
          (cechFactorCohomologyPresheaf F q)).δ k := by
  let T := nativeSheafCohomologyFunctor X q
  let E := HilbertConstruction.Finite.CechFunctorComparison.finiteCechCosimplicialFunctorIso T (IntrinsicCech.SheafComplex.cechFactorPresheaf F) U
  have hn := E.hom.naturality (SimplexCategory.δ k)
  have hd := IntrinsicCech.SheafComplex.nativeCoface_eq_cechCoface F U n k
  exact (congrArg (fun z : IntrinsicCech.SheafTerms.cechTerm F U n ⟶ IntrinsicCech.SheafTerms.cechTerm F U (n + 1) =>
    T.map z ≫ (cechTermCohomologyIso F U q (n + 1)).hom) hd).symm.trans hn

def cechSheafCohomologyComplexIso :
    ((nativeSheafCohomologyFunctor X q).mapHomologicalComplex (.up ℕ)).obj
        (IntrinsicCech.SheafComplex.cechComplex F U) ≅
      (cechComplexFunctor U).obj (cechFactorCohomologyPresheaf F q) :=
  HilbertConstruction.Finite.CechFunctorComparison.finiteCechFunctorIso (nativeSheafCohomologyFunctor X q) (IntrinsicCech.SheafComplex.cechFactorPresheaf F) U

theorem cechTermCohomologyIso_differential (n : ℕ) :
    (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) q).map
        (SheafDifferential.IntrinsicCech.cechDifferential F U n) ≫ (cechTermCohomologyIso F U q (n + 1)).hom =
      (cechTermCohomologyIso F U q n).hom ≫
        ((cechComplexFunctor U).obj (cechFactorCohomologyPresheaf F q)).d n (n + 1) := by
  let T := nativeSheafCohomologyFunctor X q
  let E := cechSheafCohomologyComplexIso F U q
  have hd : T.map ((IntrinsicCech.SheafComplex.cechComplex F U).d n (n + 1)) = T.map (SheafDifferential.IntrinsicCech.cechDifferential F U n) :=
    congrArg (fun z : IntrinsicCech.SheafTerms.cechTerm F U n ⟶ IntrinsicCech.SheafTerms.cechTerm F U (n + 1) => T.map z) (IntrinsicCech.SheafComplex.cechComplex_d F U n)
  exact (congrArg (fun z => z ≫ E.hom.f (n + 1)) hd).symm.trans (E.hom.comm n (n + 1)).symm

private theorem firstDifferential_injective_of_complexIso
    {K L : CochainComplex AddCommGrpCat.{u} ℕ} (e : K ≅ L)
    (hd : Function.Injective (L.d 0 1)) : Function.Injective (K.d 0 1) := by
  let e₀ : K.X 0 ≅ L.X 0 := (HomologicalComplex.eval _ _ 0).mapIso e
  have he : Function.Injective (e.hom.f 0) :=
    (ConcreteCategory.bijective_of_isIso e₀.hom).injective
  intro x y hxy
  apply he
  apply hd
  have hx := ConcreteCategory.congr_hom (e.hom.comm 0 1) x
  have hy := ConcreteCategory.congr_hom (e.hom.comm 0 1) y
  exact hx.trans ((congrArg (e.hom.f 1) hxy).trans hy.symm)

theorem cechCohomology_firstDifferential_injective
    (hd : Function.Injective
      (((cechComplexFunctor U).obj (cechFactorCohomologyPresheaf F q)).d 0 1)) :
    Function.Injective (CategoryTheory.Sheaf.H.map (SheafDifferential.IntrinsicCech.cechDifferential F U 0) q) := by
  let T := nativeSheafCohomologyFunctor X q
  have h : Function.Injective (T.map ((IntrinsicCech.SheafComplex.cechComplex F U).d 0 1)) :=
    firstDifferential_injective_of_complexIso (cechSheafCohomologyComplexIso F U q) hd
  have he : T.map ((IntrinsicCech.SheafComplex.cechComplex F U).d 0 1) = T.map (SheafDifferential.IntrinsicCech.cechDifferential F U 0) :=
    congrArg (fun z : IntrinsicCech.SheafTerms.cechTerm F U 0 ⟶ IntrinsicCech.SheafTerms.cechTerm F U 1 => T.map z) (IntrinsicCech.SheafComplex.cechComplex_d F U 0)
  change Function.Injective (T.map (SheafDifferential.IntrinsicCech.cechDifferential F U 0))
  exact (congrArg (fun z : T.obj (IntrinsicCech.SheafTerms.cechTerm F U 0) ⟶ T.obj (IntrinsicCech.SheafTerms.cechTerm F U 1) =>
    Function.Injective z) he).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.SheafTermCohomology.IntrinsicCech
