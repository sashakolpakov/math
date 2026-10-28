import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Base Cech Total Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechTotalForget

noncomputable section

/-! Forgetting base scalars in the original Čech total complex of scheme modules. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) {ι : Type u} (U : ι → X.Opens)

local instance cech_additive : (cechComplexFunctor (A := AddCommGrpCat.{u}) U).Additive :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits.CechCochainLimits.cochain_additive (FormalCoproduct.mk ι U).cech

local instance moduleBiproducts : HasFiniteBiproducts (ModuleCat.{u} Γ(S, ⊤)) :=
  Abelian.hasFiniteBiproducts

def presheaves : X.Modules ⥤ X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

instance presheaves_additive : (presheaves (X := X)).Additive where
  map_add := rfl

variable (A : CochainComplex X.Modules ℕ)

def baseBicomplex : HomologicalComplex₂ (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) (.up ℕ) :=
  ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).mapHomologicalComplex (.up ℕ)).obj A

def abBicomplex : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) :=
  ((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj
    (((presheaves (X := X)).mapHomologicalComplex (.up ℕ)).obj A)

def bicomplexIso :
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget S) (baseBicomplex π U A) ≅ abBicomplex U A :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso π (A.X n) U)
    (fun n m _ => (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseCechComplexForgetIso_naturality π (A.d n m) U).symm)

def totalIso :
    ((AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget S).mapHomologicalComplex (.up ℕ)).obj
      ((baseBicomplex π U A).total (.up ℕ)) ≅ (abBicomplex U A).total (.up ℕ) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget S)
    (baseBicomplex π U A)).symm ≪≫ HomologicalComplex₂.total.mapIso (bicomplexIso π U A) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BaseCechTotalForget
