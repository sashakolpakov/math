import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ModuleCupAlgebra
import Mathlib.Algebra.Category.AlgCat.Limits

/-! # Module Cech Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ModuleCechCup

noncomputable section

/-! Base-linear cup products on the actual crystalline module Čech
complex. The algebra coefficient forgets to the original enlarged
structure-module presheaf, and the comparison uses canonical products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site.AffineThickening.CoefficientRing (B := B)

local instance : HasBinaryProducts (Site.AffineThickening p B J δ f) :=
  Small.CrystallineSeparatedProduct.hasBinaryProducts f (Fact.out : p.Prime).pos

def liftedBase (U : Site.AffineThickening p B J δ f) : R →+* ULift.{u + 1} U.ring :=
  ULift.ringEquiv.symm.toRingHom.comp (U.base.comp ULift.ringEquiv.toRingHom)

def structureAlgebraPresheaf : (Site.AffineThickening p B J δ f)ᵒᵖ ⥤ CommAlgCat.{u + 1} R where
  obj U :=
    letI := (liftedBase f U.unop).toAlgebra
    CommAlgCat.of R (ULift.{u + 1} U.unop.ring)
  map {U V} α :=
    letI := (liftedBase f U.unop).toAlgebra
    letI := (liftedBase f V.unop).toAlgebra
    CommAlgCat.ofHom
      { (CechCup.structureRingPresheaf f).map α |>.hom with
        commutes' := fun b => by
          apply ULift.ext
          exact DFunLike.congr_fun α.unop.overBase b.down }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

abbrev forgetModule : CommAlgCat.{u + 1} R ⥤ ModuleCat.{u + 1} R :=
  forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)

local instance forgetRing_preservesLimits :
    PreservesLimits (forget₂ (CommAlgCat.{u + 1} R) CommRingCat.{u + 1}) := by
  change PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
    Under.forget (CommRingCat.of R))
  infer_instance

local instance forgetModule_preservesLimits : PreservesLimits (forgetModule (B := B)) := by
  have : PreservesLimits (forgetModule (B := B) ⋙ forget (ModuleCat.{u + 1} R)) := by
    change PreservesLimits (forget₂ (CommAlgCat.{u + 1} R) CommRingCat.{u + 1} ⋙
      forget CommRingCat.{u + 1})
    infer_instance
  exact preservesLimits_of_reflects_of_preserves (forgetModule (B := B))
    (forget (ModuleCat.{u + 1} R))

def structureForgetIso : structureAlgebraPresheaf (p := p) (J := J) (δ := δ) f ⋙
    forgetModule ≅
      Site.AffineThickening.structureModulePresheafLarge
        (p := p) (B := B) (J := J) (δB := δ) (f := f) :=
  Iso.refl _

variable {ι : Type (u + 1)} (U : ι → Site.AffineThickening p B J δ f)

def cochainAlgebra : CosimplicialObject (CommAlgCat.{u + 1} R) :=
  (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve U)).obj
    (structureAlgebraPresheaf f)

def complex : CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  (NonemptyCechNerve.complexFunctor U).obj
    (Site.AffineThickening.structureModulePresheafLarge
      (p := p) (B := B) (J := J) (δB := δ) (f := f))

def comparison : Cosimplicial.ModuleComplex.complex (cochainAlgebra f U) ≅ complex f U :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).mapIso
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.cosimplicialIso forgetModule
      (NonemptyCechNerve.nerve U) (structureAlgebraPresheaf f)) ≪≫
    (NonemptyCechNerve.complexFunctor U).mapIso (structureForgetIso f)

def cohomologyEquiv (n : ℕ) :
    (Cosimplicial.ModuleComplex.complex (cochainAlgebra f U)).homology n ≃ₗ[R]
      (complex f U).homology n :=
  (HomologicalComplex.homologyMapIso (comparison f U) n).toLinearEquiv

def cohomologyCup (m n : ℕ) :
    (complex f U).homology m →ₗ[R] (complex f U).homology n →ₗ[R]
      (complex f U).homology (m + n) :=
  (((Cosimplicial.ModuleCup.cohomologyCup (cochainAlgebra f U) m n).comp
    (cohomologyEquiv f U m).symm.toLinearMap).compl₂
      (cohomologyEquiv f U n).symm.toLinearMap).compr₂
        (cohomologyEquiv f U (m + n)).toLinearMap

theorem cohomologyCup_comparison (m n : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (cochainAlgebra f U)).homology m)
    (y : (Cosimplicial.ModuleComplex.complex (cochainAlgebra f U)).homology n) :
    cohomologyCup f U m n (cohomologyEquiv f U m x) (cohomologyEquiv f U n y) =
      cohomologyEquiv f U (m + n)
        (Cosimplicial.ModuleCup.cohomologyCup (cochainAlgebra f U) m n x y) := by
  simp only [cohomologyCup, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ModuleCechCup
