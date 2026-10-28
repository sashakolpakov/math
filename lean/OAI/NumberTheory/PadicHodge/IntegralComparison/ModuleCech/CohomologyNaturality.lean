import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.DimensionBound
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechNaturality

/-! # Cohomology Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality

noncomputable section

/-! Naturality of the native coefficient Čech comparison with
genuine Zariski cohomology of quasicoherent modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R)))
  {ι : Type u} (U : ι → X.left.Opens)

abbrev forgetCoefficients : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} := forget₂ _ _
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R

def map {M N : X.left.Modules} (f : M ⟶ N) :
    DimensionBound.complex R X M U ⟶
      DimensionBound.complex R X N U :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).map
    ((Affine.HomologyPresheaf.functor R X).map f)

theorem forget_natural {M N : X.left.Modules} (f : M ⟶ N) :
    ((G).mapHomologicalComplex (.up ℕ)).map (CohomologyNaturality.map R X U f) ≫
      (DimensionBound.forgetIso R X N U).hom =
    (DimensionBound.forgetIso R X M U).hom ≫
      (cechComplexFunctor U).map ((SheafOfModules.toSheaf X.left.ringCatSheaf).map f).hom :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.naturality G (FormalCoproduct.mk ι U).cech
    ((Affine.HomologyPresheaf.functor R X).map f)

def forgetHomologyIso (M : X.left.Modules) (n : ℕ) :
    (G).obj ((DimensionBound.complex R X M U).homology n) ≅
      ((cechComplexFunctor U).obj M.presheaf).homology n :=
  (((DimensionBound.complex R X M U).sc n).mapHomologyIso G).symm ≪≫
    HomologicalComplex.homologyMapIso (DimensionBound.forgetIso R X M U) n

theorem forget_homology_natural {M N : X.left.Modules} (f : M ⟶ N) (n : ℕ) :
    (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X U f) n) ≫
      (forgetHomologyIso R X U N n).hom =
    (forgetHomologyIso R X U M n).hom ≫
      HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((SheafOfModules.toSheaf X.left.ringCatSheaf).map f).hom) n := by
  have h₁ :
      (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X U f) n) ≫
          (((DimensionBound.complex R X N U).sc n).mapHomologyIso G).inv =
        (((DimensionBound.complex R X M U).sc n).mapHomologyIso G).inv ≫
          HomologicalComplex.homologyMap
            (((G).mapHomologicalComplex (.up ℕ)).map (CohomologyNaturality.map R X U f)) n :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map (CohomologyNaturality.map R X U f)) G
  have h₂ := congrArg (fun a => HomologicalComplex.homologyMap a n) (forget_natural R X U f)
  simp only [HomologicalComplex.homologyMap_comp] at h₂
  change (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X U f) n) ≫
      ((((DimensionBound.complex R X N U).sc n).mapHomologyIso G).inv ≫
        HomologicalComplex.homologyMap (DimensionBound.forgetIso R X N U).hom n) =
    ((((DimensionBound.complex R X M U).sc n).mapHomologyIso G).inv ≫
        HomologicalComplex.homologyMap (DimensionBound.forgetIso R X M U).hom n) ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ HomologicalComplex.homologyMap
      (DimensionBound.forgetIso R X N U).hom n) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          (((DimensionBound.complex R X M U).sc n).mapHomologyIso G).inv ≫ a) h₂).trans
            (Category.assoc _ _ _).symm)))

variable [X.left.IsSeparated]
  (hU : ⨆ i, U i = ⊤) (haffine : ∀ i, IsAffineOpen (U i))

@[reassoc]
theorem naturality {M N : X.left.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (n : ℕ) :
    (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X U f) (n + 1)) ≫
      (DimensionBound.cohomologyIso R X N U hU haffine n).hom =
    (DimensionBound.cohomologyIso R X M U hU haffine n).hom ≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X.left (n + 1)).map f := by
  change (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X U f) (n + 1)) ≫
      ((forgetHomologyIso R X U N (n + 1)).hom ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso N U hU haffine n).hom) =
    ((forgetHomologyIso R X U M (n + 1)).hom ≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso M U hU haffine n).hom) ≫ _
  rw [← Category.assoc, forget_homology_natural, Category.assoc,
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechNaturality.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso_naturality,
    ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality
