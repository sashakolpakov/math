import OAI.AlgebraicGeometry.Comparison.Betti.Module.CechFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Functor
import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Forget Modules -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.ForgetModules

noncomputable section

/-! Forgetting complex scalars identifies the categorical additive and ordinary module Čech complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X ι : Type} [TopologicalSpace X] (U : ι → Opens X)

abbrev modulePresheafForget :
    ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) :=
  (Functor.whiskeringRight (Opens X)ᵒᵖ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).obj
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})

def additiveModuleCechFunctorIso :
    modulePresheafForget ⋙ cechComplexFunctor U ≅
      AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U ⋙
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ) :=
  (Cech.Functor.cechComplexFunctorComparison (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}) U).symm ≪≫
    Functor.isoWhiskerRight (Module.CechFunctor.moduleCechFunctorIso U)
      ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ))

instance additiveModuleCechFunctor_additive :
    (modulePresheafForget ⋙ cechComplexFunctor U).Additive :=
  Functor.additive_of_iso (additiveModuleCechFunctorIso U).symm

def additiveModuleCechBicomplexIso
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{0} ℂ) ℕ) :
    ((modulePresheafForget ⋙ cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K ≅
      (((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)).mapHomologicalComplex
        (.up ℕ)).obj (((AlgebraicTopology.DeRham.Comparison.CechDoubleComplexFunctor.cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K) :=
  (NatIso.mapHomologicalComplex (additiveModuleCechFunctorIso U) (.up ℕ)).app K

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.ForgetModules
