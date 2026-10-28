import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ModuleCechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechPresheafCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.HomologyCoordinates

/-! # Cech Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup

noncomputable section

/-! The native bounded crystalline ring Čech product on the original Ext groups.
The only cover hypothesis is that the chosen bounded frame family covers the
site; the source acyclicity needed for the Ext comparison is already proved
for every bounded affine crystalline object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

section

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

def liftedBase (U : BigCrystallineSite.Object p B J δ f) : R →+* ULift.{u + 1} U.ring :=
  ULift.ringEquiv.symm.toRingHom.comp (U.base.comp ULift.ringEquiv.toRingHom)

def structureAlgebraPresheaf : (BigCrystallineSite.Object p B J δ f)ᵒᵖ ⥤ CommAlgCat.{u + 1} R where
  obj U :=
    letI := (liftedBase f U.unop).toAlgebra
    CommAlgCat.of R (ULift.{u + 1} U.unop.ring)
  map {U V} α :=
    letI := (liftedBase f U.unop).toAlgebra
    letI := (liftedBase f V.unop).toAlgebra
    CommAlgCat.ofHom
      { toFun := fun x => ULift.up (α.unop.ringMap x.down)
        map_one' := congrArg ULift.up (map_one α.unop.ringMap.toRingHom)
        map_mul' := fun x y => congrArg ULift.up (map_mul α.unop.ringMap.toRingHom x.down y.down)
        map_zero' := congrArg ULift.up (map_zero α.unop.ringMap.toRingHom)
        map_add' := fun x y => congrArg ULift.up (map_add α.unop.ringMap.toRingHom x.down y.down)
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
    forgetModule ≅ BigCrystallineCohomology.largePresheaf f := Iso.refl _

variable [IsSeparated f] (n : ℕ) {ι : Type u}
  (F : ι → Site.Objects (p := p) (J := J) (δ := δ) f n)

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

local instance algebraProducts : HasProducts.{u} (CommAlgCat.{u + 1} R) := by
  have h : HasLimitsOfSize.{u, u} (CommAlgCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  exact fun I => h.has_limits_of_shape (Discrete I)

local instance forgetModule_preservesSmallLimits :
    PreservesLimitsOfSize.{u, u} (forgetModule (B := B)) :=
  preservesLimitsOfSize_shrink.{u, u + 1, u, u + 1} (forgetModule (B := B))

def cochainAlgebra : CosimplicialObject (CommAlgCat.{u + 1} R) :=
  (FormalCoproduct.cosimplicialObjectFunctor (NonemptyCechNerve.nerve F)).obj
    ((Site.inclusion f n).op ⋙ structureAlgebraPresheaf f)

def comparison : Cosimplicial.ModuleComplex.complex (cochainAlgebra f n F) ≅
    BoundedFrame.CechComplex.presheafComplex f n F :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).mapIso
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.cosimplicialIso forgetModule
      (NonemptyCechNerve.nerve F) ((Site.inclusion f n).op ⋙ structureAlgebraPresheaf f)) ≪≫
    (NonemptyCechNerve.complexFunctor F).mapIso
      (Functor.isoWhiskerLeft (Site.inclusion f n).op (structureForgetIso f))

end

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → Site.Objects (p := p) (J := J) (δ := δ) f n)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ Site.topology f n U)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n

def cohomologyEquiv (i : ℕ) :
    (Cosimplicial.ModuleComplex.complex (cochainAlgebra f n F)).homology i ≃ₗ[R] H i :=
  (HomologicalComplex.homologyMapIso (comparison f n F) i).toLinearEquiv |>.trans
    ((Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (BoundedFrame.CechComplex.presheafComplex f n F) i).trans
        (BoundedFrame.CechPresheafCohomology.homologyIso p k f n F hcover i).toLinearEquiv)

/-- The actual bounded crystalline Ext groups carry the native frame cup product. -/
def cup (i j : ℕ) : H i →ₗ[R] H j →ₗ[R] H (i + j) :=
  (((Cosimplicial.ModuleCup.cohomologyCup (cochainAlgebra f n F) i j).comp
    (cohomologyEquiv p k f n F hcover i).symm.toLinearMap).compl₂
      (cohomologyEquiv p k f n F hcover j).symm.toLinearMap).compr₂
        (cohomologyEquiv p k f n F hcover (i + j)).toLinearMap

theorem cup_comparison (i j : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (cochainAlgebra f n F)).homology i)
    (y : (Cosimplicial.ModuleComplex.complex (cochainAlgebra f n F)).homology j) :
    cup p k f n F hcover i j
      (cohomologyEquiv p k f n F hcover i x) (cohomologyEquiv p k f n F hcover j y) =
        cohomologyEquiv p k f n F hcover (i + j)
          (Cosimplicial.ModuleCup.cohomologyCup (cochainAlgebra f n F) i j x y) := by
  simp only [cup, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup
