/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechHomology.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget

/-! # Base Cech Homology -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomology.Scheme.Modules

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-!
# Low-degree homology of base-linear Cech complexes

This is the isomorphism-only slice of AINTLIB's base-Cech homology module.
It transports homology in every degree through the reviewed forgetful complex
isomorphism and applies the affine-cover native-Cech comparison in degree one.
The general forgetful comparison is public because the project-level
degree-zero comparison is its named downstream consumer.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

open OAI.AlgebraicGeometry.SheafCohomology.Module.ProjectiveAffine.ModuleSheaf

/-- Forgetting the base-module structure on Cech homology recovers the
homology of the native additive Cech complex. -/
noncomputable def baseCechComplexHomologyForgetIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (BaseCechForget.Scheme.Modules.baseModuleForget S).obj ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology n) ≅
      ((cechComplexFunctor U).obj (Module.ProjectiveAffine.ModuleSheaf.sheaf M).obj).homology n :=
  (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).sc n).mapHomologyIso
    (BaseCechForget.Scheme.Modules.baseModuleForget S)).symm ≪≫
      HomologicalComplex.homologyMapIso
        (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π M U) n

/-- The forward map of the forgetful homology comparison is the mapped-homology
comparison followed by the homology map of the degreewise forgetful isomorphism. -/
@[simp]
theorem baseCechComplexHomologyForgetIso_hom
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplexHomologyForgetIso π M U n).hom =
      (((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).sc n).mapHomologyIso
          (BaseCechForget.Scheme.Modules.baseModuleForget S)).inv ≫
        HomologicalComplex.homologyMap
          (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π M U).hom n :=
  rfl

/-- The comparison between forgotten base-linear Cech homology and native
additive Cech homology is natural in the coefficient module. -/
@[reassoc]
theorem baseCechComplexHomologyForgetIso_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (BaseCechForget.Scheme.Modules.baseModuleForget S).map
          (HomologicalComplex.homologyMap
            ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map f) n) ≫
        (baseCechComplexHomologyForgetIso π N U n).hom =
      (baseCechComplexHomologyForgetIso π M U n).hom ≫
        HomologicalComplex.homologyMap
          ((cechComplexFunctor U).map (Module.ProjectiveAffine.ModuleSheaf.Hom.sheafHom f).hom) n := by
  let a := (((BaseCechForget.Scheme.Modules.baseModuleForget S).mapHomologicalComplex (.up ℕ)).map
    ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map f))
  let b := (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π N U).hom
  let c := (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π M U).hom
  let d := (cechComplexFunctor U).map (Module.ProjectiveAffine.ModuleSheaf.Hom.sheafHom f).hom
  have hcomp : a ≫ b = c ≫ d :=
    BaseCechForget.Scheme.Modules.baseCechComplexForgetIso_naturality π f U
  have hcomplex :
      HomologicalComplex.homologyMap a n ≫
          HomologicalComplex.homologyMap b n =
        HomologicalComplex.homologyMap c n ≫
          HomologicalComplex.homologyMap d n :=
    (HomologicalComplex.homologyMap_comp a b n).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g n) hcomp).trans
        (HomologicalComplex.homologyMap_comp c d n))
  let φ := (HomologicalComplex.shortComplexFunctor
    (ModuleCat.{u} Γ(S, (⊤ : S.Opens))) (.up ℕ) n).map
      ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map f)
  let β := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π N U).hom
  let γ := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      (BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π M U).hom
  let δ := (HomologicalComplex.shortComplexFunctor
    AddCommGrpCat.{u} (.up ℕ) n).map
      ((cechComplexFunctor U).map (Module.ProjectiveAffine.ModuleSheaf.Hom.sheafHom f).hom)
  let iN := ((((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).obj N).sc n).mapHomologyIso
    (BaseCechForget.Scheme.Modules.baseModuleForget S)).inv
  let iM := ((((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).obj M).sc n).mapHomologyIso
    (BaseCechForget.Scheme.Modules.baseModuleForget S)).inv
  dsimp only [a, b, c, d, HomologicalComplex.homologyMap] at hcomplex
  change ShortComplex.homologyMap
        ((BaseCechForget.Scheme.Modules.baseModuleForget S).mapShortComplex.map φ) ≫
      ShortComplex.homologyMap β =
    ShortComplex.homologyMap γ ≫
      ShortComplex.homologyMap δ at hcomplex
  rw [baseCechComplexHomologyForgetIso_hom,
    baseCechComplexHomologyForgetIso_hom]
  dsimp only [HomologicalComplex.homologyMap]
  change (BaseCechForget.Scheme.Modules.baseModuleForget S).map (ShortComplex.homologyMap φ) ≫
      (iN ≫ ShortComplex.homologyMap β) =
    iM ≫ (ShortComplex.homologyMap γ ≫
      ShortComplex.homologyMap δ)
  have hnat :
      (BaseCechForget.Scheme.Modules.baseModuleForget S).map (ShortComplex.homologyMap φ) ≫ iN =
        iM ≫ ShortComplex.homologyMap
          ((BaseCechForget.Scheme.Modules.baseModuleForget S).mapShortComplex.map φ) :=
    ShortComplex.mapHomologyIso_inv_naturality φ (BaseCechForget.Scheme.Modules.baseModuleForget S)
  calc
    _ = ((BaseCechForget.Scheme.Modules.baseModuleForget S).map (ShortComplex.homologyMap φ) ≫ iN) ≫
        ShortComplex.homologyMap β :=
      (Category.assoc _ _ _).symm
    _ = (iM ≫ ShortComplex.homologyMap
          ((BaseCechForget.Scheme.Modules.baseModuleForget S).mapShortComplex.map φ)) ≫
        ShortComplex.homologyMap β :=
      congrArg (fun q => q ≫ ShortComplex.homologyMap β) hnat
    _ = iM ≫
        (ShortComplex.homologyMap
            ((BaseCechForget.Scheme.Modules.baseModuleForget S).mapShortComplex.map φ) ≫
          ShortComplex.homologyMap β) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun q => iM ≫ q) hcomplex

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomology.Scheme.Modules
