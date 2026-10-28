import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamHomologyCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafExactness
import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondFiniteness

/-! # De Rham Second Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamSecondFiniteness

noncomputable section

/-! The actual second-stage cohomology of the original de Rham Cech bicomplex is finite. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamCechUnit

def iso (n : ℕ) :
    IntegralComparison.Module.TotalSecondClasses.horizontal (DeRhamCechUnit.bicomplex k X).flip n ≅
      DeRhamHomologyCech.complex k X n :=
  BicomplexHomology.iso (DeRhamCechUnit.bicomplex k X) n ≪≫
    Cech.PresheafExactness.homologyIso k (DeRhamCechUnit.nerve k X) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex k X) n

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n q : ℕ) :
    Module.Finite k ((IntegralComparison.Module.TotalSecondClasses.horizontal (DeRhamCechUnit.bicomplex k X).flip n).homology q) := by
  let : Module.Finite k ((DeRhamHomologyCech.complex k X n).homology q) :=
    DeRhamHomologyCech.finite k X hprojective n q
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso (iso k X n) q).symm.toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamSecondFiniteness
