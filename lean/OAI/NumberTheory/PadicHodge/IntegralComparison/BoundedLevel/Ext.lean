import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExtPullbackComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveExactFunctorAugmentation

/-! # Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Ext.Comparison

noncomputable section

/-! Restricting a common original crystalline injective resolution realizes the original bounded-level Ext map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f m
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition.constantUnitIso (p := p) (J := J) (δ := δ) f n m hnm

theorem component (i : ℕ) : IntegralComparison.Ext.ExtPullbackComparison.component T R A (e).inv i
    (BoundedCrystalline.CrystallineCohomology.structureSheaf f m) =
      ModuleCat.ofHom (Bounded.CohomologyTransition.map f n m hnm i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact (Ext.comp_mk₀_id _).symm

variable (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f m I

def complexMap : InjectiveSectionCohomology.complex R A Im ⟶
    InjectiveSectionCohomology.complex R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In :=
  IntegralComparison.Ext.ExtPullbackComparison.complexMap T R A (e).inv (Im).cocomplex

theorem augmentation_zero : (In).ι.f 0 = (T).map ((Im).ι.f 0) :=
  (ExactInjectiveResolution.map_ι_zero (BoundedCrystalline.Site.restriction f n) I).trans
    (congrArg (T).map (ExactInjectiveResolution.map_ι_zero
      (BoundedCrystalline.Site.restriction f m) I)).symm

theorem exact_homology (i : ℕ) :
    HomologicalComplex.homologyMap (Acyclic.ExactFunctorComplex.map T R A (Im).cocomplex) i ≫
      (InjectiveSectionCohomology.homologyIso R ((T).obj A) In i).hom =
    (InjectiveSectionCohomology.homologyIso R A Im i).hom ≫
      IntegralComparison.Ext.ExactFunctorModule.component T R A i (BoundedCrystalline.CrystallineCohomology.structureSheaf f m) := by
  let κ : (CochainComplex.single₀ (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n)).obj
      ((T).obj (BoundedCrystalline.CrystallineCohomology.structureSheaf f m)) ⟶
    ((T).mapHomologicalComplex (ComplexShape.up ℕ)).obj (Im).cocomplex := (In).ι
  let : QuasiIso κ := (In).quasiIso
  exact InjectiveExactFunctorAugmentation.homology T R A Im κ
    (fun a => (In).injective a) (augmentation_zero f n m hnm I) i

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (complexMap f n m hnm I) i ≫
    (InjectiveSectionCohomology.homologyIso R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In i).hom =
      (InjectiveSectionCohomology.homologyIso R A Im i).hom ≫
        ModuleCat.ofHom (Bounded.CohomologyTransition.map f n m hnm i) := by
  have h₁ := exact_homology f n m hnm I i
  have h₂ := InjectiveSource.Comparison.homology R (e).inv In i
  have hm := HomologicalComplex.homologyMap_comp (Acyclic.ExactFunctorComplex.map T R A (Im).cocomplex)
    (IntegralComparison.Ext.SourceModule.complexMap R (e).inv (In).cocomplex) i
  have h := (congrArg (fun a => a ≫
    (InjectiveSectionCohomology.homologyIso R (BoundedCrystalline.CrystallineCohomology.constantUnit f n) In i).hom) hm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => HomologicalComplex.homologyMap
          (Acyclic.ExactFunctorComplex.map T R A (Im).cocomplex) i ≫ a) h₂).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun a => a ≫ IntegralComparison.Ext.SourceModule.component R (e).inv i
                (BoundedCrystalline.CrystallineCohomology.structureSheaf f n)) h₁).trans
                  (Category.assoc _ _ _)))))
  exact h.trans (congrArg (fun a => (InjectiveSectionCohomology.homologyIso R A Im i).hom ≫ a)
    (component f n m hnm i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Ext.Comparison
