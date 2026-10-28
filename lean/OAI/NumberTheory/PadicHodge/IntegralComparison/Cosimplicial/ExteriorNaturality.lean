import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ExteriorCup

/-! # Exterior Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ExteriorNaturality.Cup

noncomputable section

/-! A map of cosimplicial algebras acts on the exterior cup product by
the exterior power of its original degree-one cohomology map. -/

open _root_.CategoryTheory
open scoped Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
  ModuleComplex CohomologyRing

universe u v

variable {R : Type u} [CommRing R] {A B : CosimplicialObject (CommAlgCat.{v} R)}

theorem cohomologyOne_natural (f : A ⟶ B) :
    HomologicalComplex.homologyMap (ModuleCup.complexMap f) 0 (ModuleCupAlgebra.cohomologyOne A) = ModuleCupAlgebra.cohomologyOne B := by
  have h : Module.CochainClassNaturality.cycleMap (ModuleCup.complexMap f) 0 (ModuleCupAlgebra.cycleOne A) = ModuleCupAlgebra.cycleOne B := by
    apply Subtype.ext
    exact (f.app ⦋0⦌).hom.map_one
  exact (Module.CochainClassNaturality.naturality_apply (ModuleCup.complexMap f) 0 (ModuleCupAlgebra.cycleOne A)).symm.trans
    (congrArg (Module.CochainClasses.classMap (ModuleComplex.complex B) 0) h)

theorem iteratedCup_natural (f : A ⟶ B) (n : ℕ) (x : Fin n → CohomologyRing.cohomology A 1) :
    HomologicalComplex.homologyMap (ModuleCup.complexMap f) n (ExteriorCup.iteratedCup A n x) =
      ExteriorCup.iteratedCup B n (fun i => HomologicalComplex.homologyMap (ModuleCup.complexMap f) 1 (x i)) := by
  induction n with
  | zero => exact cohomologyOne_natural f
  | succ n ih => simp only [ExteriorCup.iteratedCup, ModuleCup.cohomologyCup_natural, ih]

variable [Invertible (2 : A.obj ⦋1⦌)] [Invertible (2 : A.obj ⦋2⦌)]
  [Invertible (2 : B.obj ⦋1⦌)] [Invertible (2 : B.obj ⦋2⦌)]

theorem exteriorPowerCup_natural (f : A ⟶ B) (n : ℕ) :
    (HomologicalComplex.homologyMap (ModuleCup.complexMap f) n).hom.comp (ExteriorCup.exteriorPowerCup A n) =
      (ExteriorCup.exteriorPowerCup B n).comp
        (exteriorPower.map n (HomologicalComplex.homologyMap (ModuleCup.complexMap f) 1).hom) := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R n (CohomologyRing.cohomology A 1))
  rintro w ⟨x, rfl⟩
  simp only [LinearMap.comp_apply, exteriorPower.map_apply_ιMulti, ExteriorCup.exteriorPowerCup_multi]
  exact iteratedCup_natural f n x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ExteriorNaturality.Cup
