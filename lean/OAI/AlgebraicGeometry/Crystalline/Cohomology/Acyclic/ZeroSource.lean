import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Zero Source -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroSource.AcyclicZeroSource

noncomputable section

/-! # Source naturality of the original degree-zero resolution comparison -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (u : X' ⟶ X)
  (K : CochainComplex C ℕ) {Z : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X' 0

def augmentationMap (Y : C) : (F).obj Y ⟶ (G).obj Y := (ExtSource.ExtSourceSections.transformation R u 0).app Y

def sectionMap : NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K ⟶
    NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X' K := ExtSource.ExtSourceSections.complexMap R u K

local notation "m" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroSource.AcyclicZeroSource.augmentationMap R u Z
local notation "α" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X K ι
local notation "β" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X' K ι
local notation "g" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroSource.AcyclicZeroSource.sectionMap R u K

omit [QuasiIso ι] in
theorem augmentation_square : α ≫ g = (CochainComplex.single₀ _).map m ≫ β := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation_zero]
  exact (ExtSource.ExtSourceSections.transformation R u 0).naturality (ι.f 0)

theorem naturality : HomologicalComplex.homologyMap g 0 ≫
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R X' K ι).hom =
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R X K ι).hom ≫ m := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{z} R) (.up ℕ) 0
  let eX : H.obj ((CochainComplex.single₀ _).obj ((F).obj Z)) ≅
      H.obj (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K) := isoOfQuasiIsoAt α 0
  let eX' : H.obj ((CochainComplex.single₀ _).obj ((G).obj Z)) ≅
      H.obj (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X' K) := isoOfQuasiIsoAt β 0
  let sX : H.obj ((CochainComplex.single₀ _).obj ((F).obj Z)) ≅ (F).obj Z :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((F).obj Z)
  let sX' : H.obj ((CochainComplex.single₀ _).obj ((G).obj Z)) ≅ (G).obj Z :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((G).obj Z)
  have hh := congrArg H.map (augmentation_square R u K ι)
  rw [Functor.map_comp, Functor.map_comp] at hh
  have hs := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (.up ℕ) 0 m
  have hsq : eX.hom ≫ H.map g = H.map ((CochainComplex.single₀ _).map m) ≫ eX'.hom := hh
  change H.map g ≫ (eX'.inv ≫ sX'.hom) = (eX.inv ≫ sX.hom) ≫ m
  apply (cancel_epi eX.hom).mp
  simp only [← Category.assoc]
  rw [hsq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroSource.AcyclicZeroSource
