import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleTracePresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.TransferCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.TopEdgeTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality

/-! # Module Cech Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleCechTrace

noncomputable section

/-! The original native top-row transfer agrees, on actual Čech
complexes, with the actual module-sheaf trace. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]
  {ι : Type u} (U : ι → Y.left.Opens) (q : ℕ)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R
local notation "F" => Opens.map f.left.base
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic.inverseCover R X Y f U
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X q
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R Y q

local instance opens_finiteLimits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

def trace : ModuleCech.DimensionBound.complex R X M V ⟶
    ModuleCech.DimensionBound.complex R Y N U :=
  (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R X V q).hom ≫
    (IntrinsicDeRham.CechTransfer.Intrinsic.trace R X Y f U).f q ≫
      (IntrinsicDeRham.TopEdge.Intrinsic.rowIso R Y U q).inv

theorem trace_eq : trace R X Y f U q =
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U ((Affine.HomologyPresheaf.functor R X).obj M)).inv ≫
      (cechComplexFunctor U).map (ModuleTracePresheaf.transfer R X Y f q) :=
  Cech.TransferCoefficients.conjugate (F) U
    ((FiniteEtale.DeRhamSheafTrace.trace R X Y f).f q).hom
    (ModuleTracePresheaf.coefficientIso R q X)
    (ModuleTracePresheaf.coefficientIso R q Y)

theorem comparison :
    ((G).mapHomologicalComplex (.up ℕ)).map (trace R X Y f U q) ≫
      (ModuleCech.DimensionBound.forgetIso R Y N U).hom =
    (ModuleCech.DimensionBound.forgetIso R X M V).hom ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso (F) U (M).presheaf).inv ≫
        (cechComplexFunctor U).map
          ((SheafOfModules.toSheaf Y.left.ringCatSheaf).map
            (FiniteEtale.ModuleTrace.trace R X Y f q)).hom := by
  rw [trace_eq]
  have h := Cech.TransferCoefficients.naturality (G) (F) U
    (ModuleTracePresheaf.transfer R X Y f q)
  rw [ModuleTracePresheaf.forget_transfer] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.ModuleCechTrace
