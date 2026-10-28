import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Zero Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroNaturality.AcyclicZeroNaturality

noncomputable section

/-! # Degree-zero naturality for the original augmented resolution comparison -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  {K L : CochainComplex C ℕ} (f : K ⟶ L) {Z Z' : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ C).obj Z' ⟶ L) [QuasiIso κ]
  (a : Z ⟶ Z') (ha : ι ≫ f = (CochainComplex.single₀ C).map a ≫ κ)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "α" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X K ι
local notation "β" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X L κ
local notation "g" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionNaturality.AcyclicResolutionNaturality.sectionMap R X f

include ha in
omit [QuasiIso ι] [QuasiIso κ] in
theorem augmentation_square : α ≫ g = (CochainComplex.single₀ _).map ((F).map a) ≫ β := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation_zero,
    CochainComplex.single₀_map_f_zero]
  change (F).map (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation K ι) ≫ (F).map (f.f 0) =
    (F).map a ≫ (F).map (NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles.augmentation L κ)
  rw [← (F).map_comp, ← (F).map_comp, AugmentedResolution.AugmentedResolutionMaps.augmentation_square f ι κ a ha]

include ha in
theorem naturality : HomologicalComplex.homologyMap g 0 ≫
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R X L κ).hom =
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R X K ι).hom ≫ (F).map a := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{z} R) (.up ℕ) 0
  let eK : H.obj ((CochainComplex.single₀ _).obj ((F).obj Z)) ≅
      H.obj (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K) := isoOfQuasiIsoAt α 0
  let eL : H.obj ((CochainComplex.single₀ _).obj ((F).obj Z')) ≅
      H.obj (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X L) := isoOfQuasiIsoAt β 0
  let sK : H.obj ((CochainComplex.single₀ _).obj ((F).obj Z)) ≅ (F).obj Z :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((F).obj Z)
  let sL : H.obj ((CochainComplex.single₀ _).obj ((F).obj Z')) ≅ (F).obj Z' :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((F).obj Z')
  have hh := congrArg H.map (augmentation_square R X f ι κ a ha)
  rw [Functor.map_comp, Functor.map_comp] at hh
  have hs := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (.up ℕ) 0 ((F).map a)
  have hsq : eK.hom ≫ H.map g = H.map ((CochainComplex.single₀ _).map ((F).map a)) ≫ eL.hom := hh
  change H.map g ≫ (eL.inv ≫ sL.hom) = (eK.inv ≫ sK.hom) ≫ (F).map a
  apply (cancel_epi eK.hom).mp
  simp only [← Category.assoc]
  rw [hsq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroNaturality.AcyclicZeroNaturality
