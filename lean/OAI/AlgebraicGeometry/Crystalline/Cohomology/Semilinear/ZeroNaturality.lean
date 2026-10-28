import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ResolutionNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentedHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.AugmentationZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Zero Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ZeroNaturality.SemilinearZeroNaturality

noncomputable section

/-! # Original degree-zero comparison under exact semilinear transport -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian

universe u v u' v' z t t'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) (S : Type t') [CommRing R] [CommRing S] [Linear R C] [Linear S D]
  (σ : R →+* S) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (hF : ∀ (Y : C) (r : R), F.map (r • 𝟙 Y) = σ r • 𝟙 (F.obj Y)) (X : C)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)

local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.AcyclicHomologyData.SemilinearAcyclicHomologyData.coefficients R S σ
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor S (F.obj X) 0
local notation "KR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K
local notation "LS" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex S (F.obj X) L
local notation "α" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X K ι
local notation "β" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation S (F.obj X) L κ
local notation "g" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ResolutionNaturality.SemilinearResolutionNaturality.sectionMap R S σ F hF X f

def augmentationMap : (G).obj Z ⟶ (Q).obj ((H).obj Z') := ExtSections.SemilinearExtSections.map R S σ F hF X a 0

local notation "m" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ZeroNaturality.SemilinearZeroNaturality.augmentationMap R S σ F hF X a

include ha in
omit [QuasiIso ι] [QuasiIso κ] in
theorem augmentation_square : α ≫ g = (CochainComplex.single₀ _).map m ≫
    Mapped.AugmentedHomology.MappedAugmentedHomology.augmentation Q β := by
  apply HomologicalComplex.from_single_hom_ext
  have hb : (Mapped.AugmentedHomology.MappedAugmentedHomology.augmentation Q β).f 0 = (Q).map ((β).f 0) :=
    Mapped.AugmentationZero.MappedAugmentationZero.mapped Q β
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero, hb,
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation_zero]
  exact ExtSections.SemilinearExtSections.square R S σ F hF X (ι.f 0) (κ.f 0) a (f.f 0) ha 0

include ha in
theorem naturality : HomologicalComplex.homologyMap g 0 ≫ (Mapped.ComplexHomology.MappedComplexHomology.iso Q LS 0).hom ≫
      (Q).map (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso S (F.obj X) L κ).hom =
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R X K ι).hom ≫ m := by
  let H₀ := HomologicalComplex.homologyFunctor (ModuleCat.{z} R) (.up ℕ) 0
  let eK : H₀.obj ((CochainComplex.single₀ _).obj ((G).obj Z)) ≅ H₀.obj KR := isoOfQuasiIsoAt α 0
  let sK : H₀.obj ((CochainComplex.single₀ _).obj ((G).obj Z)) ≅ (G).obj Z :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((G).obj Z)
  let sL : H₀.obj ((CochainComplex.single₀ _).obj ((Q).obj ((H).obj Z'))) ≅ (Q).obj ((H).obj Z') :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((Q).obj ((H).obj Z'))
  let t := (Mapped.ComplexHomology.MappedComplexHomology.iso Q LS 0).hom
  let c := (Q).map (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso S (F.obj X) L κ).hom
  have hl : H₀.map (Mapped.AugmentedHomology.MappedAugmentedHomology.augmentation Q β) ≫ t ≫ c = sL.hom :=
    Mapped.AugmentedHomology.MappedAugmentedHomology.comparison Q β
  have hh := congrArg H₀.map (augmentation_square R S σ F hF X f ι κ a ha)
  rw [Functor.map_comp, Functor.map_comp] at hh
  have hsq : eK.hom ≫ H₀.map g = H₀.map ((CochainComplex.single₀ _).map m) ≫
      H₀.map (Mapped.AugmentedHomology.MappedAugmentedHomology.augmentation Q β) := hh
  have hs := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (.up ℕ) 0 m
  have he : eK.hom ≫ eK.inv ≫ sK.hom ≫ m = sK.hom ≫ m := eK.hom_inv_id_assoc _
  change H₀.map g ≫ t ≫ c = (eK.inv ≫ sK.hom) ≫ m
  apply (cancel_epi eK.hom).mp
  simp only [← Category.assoc]
  rw [hsq]
  simp only [Category.assoc]
  rw [hl]
  exact hs.trans he.symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.ZeroNaturality.SemilinearZeroNaturality
