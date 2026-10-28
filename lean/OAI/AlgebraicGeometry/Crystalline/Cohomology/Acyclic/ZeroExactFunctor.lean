import OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionExactFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Zero Exact Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroExactFunctor.AcyclicZeroExactFunctor

noncomputable section

/-! # Exact-functor compatibility of the original degree-zero comparison -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Linear R] (X : C)
  {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L) {Z : C} {Z' : D}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (κ : (CochainComplex.single₀ D).obj Z' ⟶ L) [QuasiIso κ]
  (a : F.obj Z ⟶ Z') (ha : F.map (ι.f 0) ≫ f.f 0 = a ≫ κ.f 0)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "G'" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (F.obj X) 0

def augmentationMap : (G).obj Z ⟶ (G').obj Z' := ExactFunctor.ExactFunctorExtSections.map R F X a 0

local notation "m" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroExactFunctor.AcyclicZeroExactFunctor.augmentationMap R F X a
local notation "α" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X K ι
local notation "β" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R (F.obj X) L κ
local notation "g" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ResolutionExactFunctor.AcyclicResolutionExactFunctor.sectionMap R F X f

include ha in
omit [QuasiIso ι] [QuasiIso κ] in
theorem augmentation_square : α ≫ g = (CochainComplex.single₀ _).map m ≫ β := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation_zero]
  exact ExactFunctor.ExactFunctorExtSections.square R F X (ι.f 0) (κ.f 0) a (f.f 0) ha 0

include ha in
theorem naturality : HomologicalComplex.homologyMap g 0 ≫
    (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R (F.obj X) L κ).hom =
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.homologyIso R X K ι).hom ≫ m := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{z} R) (.up ℕ) 0
  let eK : H.obj ((CochainComplex.single₀ _).obj ((G).obj Z)) ≅
      H.obj (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K) := isoOfQuasiIsoAt α 0
  let eL : H.obj ((CochainComplex.single₀ _).obj ((G').obj Z')) ≅
      H.obj (NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R (F.obj X) L) := isoOfQuasiIsoAt β 0
  let sK : H.obj ((CochainComplex.single₀ _).obj ((G).obj Z)) ≅ (G).obj Z :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((G).obj Z)
  let sL : H.obj ((CochainComplex.single₀ _).obj ((G').obj Z')) ≅ (G').obj Z' :=
    HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((G').obj Z')
  have hh := congrArg H.map (augmentation_square R F X f ι κ a ha)
  rw [Functor.map_comp, Functor.map_comp] at hh
  have hs := HomologicalComplex.singleObjHomologySelfIso_hom_naturality (.up ℕ) 0 m
  have hsq : eK.hom ≫ H.map g = H.map ((CochainComplex.single₀ _).map m) ≫ eL.hom := hh
  change H.map g ≫ (eL.inv ≫ sL.hom) = (eK.inv ≫ sK.hom) ≫ m
  apply (cancel_epi eK.hom).mp
  simp only [← Category.assoc]
  rw [hsq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hs

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.ZeroExactFunctor.AcyclicZeroExactFunctor
