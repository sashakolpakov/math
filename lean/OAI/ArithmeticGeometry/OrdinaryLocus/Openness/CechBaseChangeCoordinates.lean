import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechShortComplex
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Cech Base Change Coordinates -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechBaseChangeCoordinates.Construction

noncomputable section

/-! Finite-product coordinates for tensoring the first three actual Cech terms. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped TensorProduct

universe u

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {X : TopCat.{u}} (F : TopCat.Sheaf (ModuleCat.{u} R) X)
    {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → Opens X)

abbrev tensorCechC0 := ∀ i, K ⊗[R] F.obj.obj (op (U i))
abbrev tensorCechC1 := ∀ i j, K ⊗[R] F.obj.obj (op (U i ⊓ U j))
abbrev tensorCechC2 := ∀ i j k, K ⊗[R] F.obj.obj (op ((U i ⊓ U j) ⊓ U k))

def cechBaseChangeCoordinates0 : (K ⊗[R] OpenCechDegreeZero.Construction.openModuleCechC0 F U) ≃ₗ[K] tensorCechC0 (K := K) F U :=
  TensorProduct.piRight R K K _

def cechBaseChangeCoordinates1 : (K ⊗[R] OpenCechDegreeZero.Construction.openModuleCechC1 F U) ≃ₗ[K] tensorCechC1 (K := K) F U :=
  (TensorProduct.piRight R K K (fun i ↦ ∀ j, F.obj.obj (op (U i ⊓ U j)))).trans
    (LinearEquiv.piCongrRight fun _ ↦ TensorProduct.piRight R K K _)

def cechBaseChangeCoordinates2 : (K ⊗[R] OpenCechShortComplex.Construction.openModuleCechC2 F U) ≃ₗ[K] tensorCechC2 (K := K) F U :=
  (TensorProduct.piRight R K K (fun i ↦ ∀ j k, F.obj.obj (op ((U i ⊓ U j) ⊓ U k)))).trans
    (LinearEquiv.piCongrRight fun i ↦
      (TensorProduct.piRight R K K (fun j ↦ ∀ k, F.obj.obj (op ((U i ⊓ U j) ⊓ U k)))).trans
        (LinearEquiv.piCongrRight fun _ ↦ TensorProduct.piRight R K K _))

theorem cechBaseChangeCoordinates0_tmul (a : K) (z : OpenCechDegreeZero.Construction.openModuleCechC0 F U) (i : ι) :
    cechBaseChangeCoordinates0 F U (a ⊗ₜ[R] z) i = a ⊗ₜ[R] z i := rfl

theorem cechBaseChangeCoordinates1_tmul (a : K) (z : OpenCechDegreeZero.Construction.openModuleCechC1 F U) (i j : ι) :
    cechBaseChangeCoordinates1 F U (a ⊗ₜ[R] z) i j = a ⊗ₜ[R] z i j := rfl

theorem cechBaseChangeCoordinates2_tmul (a : K) (z : OpenCechShortComplex.Construction.openModuleCechC2 F U) (i j k : ι) :
    cechBaseChangeCoordinates2 F U (a ⊗ₜ[R] z) i j k = a ⊗ₜ[R] z i j k := rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CechBaseChangeCoordinates.Construction
