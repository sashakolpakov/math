import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeRhamCechTotal
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # De Rham Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamFiniteness

noncomputable section

/-! Finite-dimensional cohomology of the original de Rham sheaf Čech total over a finite field. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

abbrev total := DeRhamCechTotal.total k X (FrobeniusCharts.opens k X)

def abHomologyIso (n : ℕ) :
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of k))).obj
      ((FrobeniusTotal.total k X).homology n) ≅
    (DeRhamCechTotal.abTotal k X (FrobeniusCharts.opens k X)).homology n :=
  (((FrobeniusTotal.total k X).sc n).mapHomologyIso
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of k)))).symm ≪≫
      HomologicalComplex.homologyMapIso
        (DeRhamCechTotal.frobeniusTotalIso k X (FrobeniusCharts.opens k X)) n

def homologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).obj ((total k X).homology n) ≅
    (AlgebraicGeometry.SheafCohomology.Projective.BaseCechForget.Scheme.Modules.baseModuleForget (Spec (CommRingCat.of k))).obj
      ((FrobeniusTotal.total k X).homology n) :=
  (((total k X).sc n).mapHomologyIso (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})).symm ≪≫
    HomologicalComplex.homologyMapIso
      (DeRhamCechTotal.forgetTotalIso k X (FrobeniusCharts.opens k X)) n ≪≫
        (abHomologyIso k X n).symm

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n : ℕ) :
    Module.Finite k ((total k X).homology n) := by
  let : Finite Γ(Spec (CommRingCat.of k), ⊤) := Finite.of_equiv k
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.toEquiv
  let : Module.Finite Γ(Spec (CommRingCat.of k), ⊤)
      ((FrobeniusTotal.total k X).homology n) :=
    FrobeniusTotal.finite k X hprojective n
  let : Finite ((FrobeniusTotal.total k X).homology n) :=
    Module.finite_of_finite Γ(Spec (CommRingCat.of k), ⊤)
  let : Finite ((total k X).homology n) := Finite.of_equiv
    ((FrobeniusTotal.total k X).homology n)
      (homologyIso k X n).symm.addCommGroupIsoToAddEquiv.toEquiv
  exact Module.Finite.of_finite

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamFiniteness
