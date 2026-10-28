import OAI.AlgebraicGeometry.ComplexMultiplication.SingularSheafBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.SingularDualMap
import OAI.AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains
import OAI.AlgebraicTopology.Singular.GlobalRestriction

/-! # Intrinsic Reference Global Cohomology -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceGlobalCohomology

noncomputable section

section

/-! # Actual native and original global singular units agree

The maps are evaluation on genuine singular chains, restriction to the top
open subset, and the genuine presheaf-to-sheaf units.
-/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicTopology.Singular

variable (R : Type) [Field R] (Y : TopCat.{0})

local notation "F" => forget₂ (ModuleCat R) AddCommGrpCat
local notation "FN" => Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ)
local notation "Γ" => OAI.AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
local notation "ΓN" => Functor.mapHomologicalComplex (Γ) (ComplexShape.up ℕ)
local notation "A" => ModuleCat.of R R

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation and top-open restriction identify the actual ambient and raw complexes. -/
def nativeSingularRawGlobalBridgeIso :
    Functor.obj (FN) (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains A Y) ≅
      AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R Y :=
  (FN).mapIso (SingularCochainBridge.singularCochainBridgeIso R Y) ≪≫ (SingularDualMap.rawSingularCochainIso R Y).symm

set_option backward.isDefEq.respectTransparency false in
/-- Taking top-open sections of the actual evaluation/sheafification bridge. -/
def nativeSingularGlobalSheafBridgeIso :
    Functor.obj (FN) (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularSheafGlobalSections A Y) ≅
      AlgebraicTopology.Singular.SheafSubdivisionCochain.globalSingularCochainSheafComplex R Y :=
  (ΓN).mapIso (SingularSheafBridge.singularSheafComplexBridgeIso R Y)

/-- The top-open dual comparison is the actual inclusion pullback. -/
theorem singularCochainComplexIsoTopOpen_hom_eq :
    (AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).hom =
      AlgebraicTopology.Singular.CohomologyTo.singularCochainComplexMap R (Opens.inclusion' (⊤ : Opens Y)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Each component of the raw bridge is actual evaluation followed by top-open restriction. -/
theorem nativeSingularRawGlobalBridgeIso_hom_f (n : ℕ) :
    (nativeSingularRawGlobalBridgeIso R Y).hom.f n =
      (F).map ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A
        (Opens.inclusion' (⊤ : Opens Y))).f n) ≫
          (F).map ((SingularCochainBridge.singularCochainBridgeIso R (TopCat.of (⊤ : Opens Y))).hom.f n) ≫
            (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).inv.f n := by
  have hn := congrArg (fun f => (F).map (f.f n))
    (SingularCochainBridge.singularCochainBridgeIso_naturality R (Opens.inclusion' (⊤ : Opens Y)))
  change (F).map ((SingularCochainBridge.singularCochainBridgeIso R Y).hom.f n) ≫
      ((F).map ((AlgebraicTopology.Singular.SheafSubdivisionCochain.singularCochainComplexIsoTopOpen R Y).hom.f n) ≫
        (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).inv.f n) = _
  rw [singularCochainComplexIsoTopOpen_hom_eq]
  simpa only [HomologicalComplex.comp_f, Functor.map_comp, Category.assoc] using!
    congrArg (fun f => f ≫ (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplexIso R Y).inv.f n) hn.symm

set_option backward.isDefEq.respectTransparency false in
/-- Ambient native cochains and original raw cochains enter the same actual sheaf sections. -/
theorem nativeOriginalSingularGlobalUnit_square :
    (FN).map (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections A Y) ≫
        (nativeSingularGlobalSheafBridgeIso R Y).hom =
      (nativeSingularRawGlobalBridgeIso R Y).hom ≫
        AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R Y := by
  apply HomologicalComplex.hom_ext
  intro n
  have hu := NatTrans.congr_app (SingularSheafBridge.singularSheafComplexBridgeIso_unit R Y n) (Opposite.op ⊤)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    nativeSingularRawGlobalBridgeIso_hom_f,
    AlgebraicTopology.Singular.GlobalRestriction.topOpenToGlobalSingularCochainSheafComplex_f]
  change (F).map ((AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections A Y).f n) ≫
      ((SingularSheafBridge.singularSheafComplexBridgeIso R Y).hom.f n).hom.app (Opposite.op ⊤) = _
  rw [AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections_f, Functor.map_comp,
    Category.assoc]
  change (F).map ((AlgebraicTopology.Cohomology.Singular.Functor.singularPullback A
      (Opens.inclusion' (⊤ : Opens Y))).f n) ≫
    ((Functor.whiskerRight (toSheafify (Opens.grothendieckTopology Y)
      (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCochainDegreePresheaf A Y n)) (F)).app (Opposite.op ⊤) ≫
        ((SingularSheafBridge.singularSheafComplexBridgeIso R Y).hom.f n).hom.app (Opposite.op ⊤)) = _
  rw [← NatTrans.comp_app, hu]
  apply AddCommGrpCat.hom_ext
  ext c
  rfl

end

/-! # Global singular cohomology keeps the actual chain-evaluation normalization -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Singular

variable (R : Type) [Field R] (Y : TopCat.{0}) (n : ℕ)

local notation "F" => forget₂ (ModuleCat R) AddCommGrpCat
local notation "FN" => Functor.mapHomologicalComplex (F) (ComplexShape.up ℕ)
local notation "A" => ModuleCat.of R R
local notation "K" => OAI.AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) Y

/-- Both genuine global units give the same map on actual cohomology. -/
theorem nativeOriginalSingularGlobalUnit_homology_square :
    HomologicalComplex.homologyMap
        ((FN).map (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections A Y)) n ≫
      HomologicalComplex.homologyMap (nativeSingularGlobalSheafBridgeIso R Y).hom n =
    HomologicalComplex.homologyMap (nativeSingularRawGlobalBridgeIso R Y).hom n ≫
      HomologicalComplex.homologyMap (AlgebraicTopology.Singular.SheafSubdivisionCochain.topOpenToGlobalSingularCochainSheafComplex R Y) n := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    nativeOriginalSingularGlobalUnit_square]

set_option backward.isDefEq.respectTransparency false in
/-- The raw comparison induces exactly the actual native chain-evaluation map. -/
theorem nativeSingularRawGlobalBridgeIso_homology_normalization :
    HomologicalComplex.homologyMap (nativeSingularRawGlobalBridgeIso R Y).hom n ≫
        (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom =
      (((K).sc n).mapHomologyIso (F)).hom ≫
        (F).map (HomologicalComplex.homologyMap (SingularCochainBridge.singularCochainBridgeIso R Y).hom n) := by
  change HomologicalComplex.homologyMap
      ((FN).map (SingularCochainBridge.singularCochainBridgeIso R Y).hom ≫ (SingularDualMap.rawSingularCochainIso R Y).inv) n ≫
    (HomologicalComplex.homologyMap (SingularDualMap.rawSingularCochainIso R Y).hom n ≫ _) = _
  rw [HomologicalComplex.homologyMap_comp, Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (SingularDualMap.rawSingularCochainIso R Y).inv n),
    ← HomologicalComplex.homologyMap_comp, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]
  exact SingularDualMap.forgottenModuleComplex_homology_naturality R (SingularCochainBridge.singularCochainBridgeIso R Y).hom n

set_option backward.isDefEq.respectTransparency false in
/-- Every actual native class has the raw representative used by the original comparison. -/
theorem nativeSingularRawGlobalBridgeIso_homology_apply
    (z : ((FN).obj (K)).homology n) :
    HomologicalComplex.homologyMap (nativeSingularRawGlobalBridgeIso R Y).hom n z =
      (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).inv
        (SingularCochainBridge.singularCohomologyBridgeEquiv R Y n
          ((((K).sc n).mapHomologyIso (F)).hom z)) := by
  apply (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).addCommGroupIsoToAddEquiv.injective
  change (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom
      (HomologicalComplex.homologyMap (nativeSingularRawGlobalBridgeIso R Y).hom n z) =
    (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).hom ((Coefficient.SheafComparison.rawSingularHomologyIso R Y n).inv _)
  exact (ConcreteCategory.congr_hom
    (nativeSingularRawGlobalBridgeIso_homology_normalization R Y n) z).trans
      (ConcreteCategory.congr_hom (Coefficient.SheafComparison.rawSingularHomologyIso R Y n).inv_hom_id _).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.IntrinsicReferenceGlobalCohomology
