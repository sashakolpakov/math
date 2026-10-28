import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechHomology
import OAI.AlgebraicGeometry.SheafCohomology.CechScalars
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Base Cech Linear Bridge -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechLinearBridge

noncomputable section

/-! The native base-module Čech action agrees with the action by global regular functions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

/-- Scalar multiplication of cochain maps induces scalar multiplication on homology. -/
theorem homologyMap_smul {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (r : R) (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (r • f) n = r • HomologicalComplex.homologyMap f n := by
  change ShortComplex.homologyMap
    (r • (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map f) = _
  exact ShortComplex.homologyMap_smul (R := R) (C := ModuleCat.{u} R)
    (S₁ := K.sc n) (S₂ := L.sc n)
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (.up ℕ) n).map f) r

/-- Multiplication by a base function induces its ordinary scalar action on the
base-module Čech complex. -/
theorem baseCech_globalSmul_map {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤)) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map (AffineH.Projective.globalSmulHom M (π.appTop r)) =
      r • 𝟙 (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U) := by
  apply BaseCechForget.Scheme.Modules.baseCechComplexFunctor_map_eq_smul_id
  intro V
  ext x
  rfl

/-- The base ring acts on additive Čech cohomology through the actual structure map. -/
@[instance_reducible]
def nativeCechBaseModule {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    Module Γ(S, ⊤) ((CechScalars.Projective.moduleCechCohomologyFunctor U n).obj M) := by
  letI := CechScalars.Projective.cechGlobalFunctionsModule M U n
  exact Module.compHom _ π.appTop.hom

/-- Forgetting from base-module Čech cohomology preserves its actual scalar action. -/
def baseCechHomologyNativeLinearEquiv {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    letI := nativeCechBaseModule π M U n
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology n ≃ₗ[Γ(S, ⊤)]
      (CechScalars.Projective.moduleCechCohomologyFunctor U n).obj M := by
  letI := nativeCechBaseModule π M U n
  let e := (BaseCechHomology.Scheme.Modules.baseCechComplexHomologyForgetIso π M U n).addCommGroupIsoToAddEquiv
  refine { e with map_smul' := ?_ }
  intro r x
  have h := BaseCechHomology.Scheme.Modules.baseCechComplexHomologyForgetIso_naturality π
    (AffineH.Projective.globalSmulHom M (π.appTop r)) U n
  have hmap : HomologicalComplex.homologyMap
      ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor π U).map (AffineH.Projective.globalSmulHom M (π.appTop r))) n =
      r • 𝟙 ((Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U).homology n) := by
    exact (congrArg (fun f : Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U ⟶ Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U =>
      HomologicalComplex.homologyMap f n) (baseCech_globalSmul_map π M U r)).trans
      ((BaseCechLinearBridge.homologyMap_smul r (𝟙 (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U)) n).trans
        (congrArg (fun k => r • k) (HomologicalComplex.homologyMap_id (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplex π M U) n)))
  rw [hmap] at h
  exact ConcreteCategory.congr_hom h x

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseCechLinearBridge
