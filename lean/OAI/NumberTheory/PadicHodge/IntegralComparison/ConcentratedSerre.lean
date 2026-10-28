import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechConcentration

/-! # Concentrated Serre -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentratedSerre.Comparison

noncomputable section

/-! A comparison for the total of a pure internal Hom complex descends
to the Čech cohomology of its actual surviving cohomology sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (N : X.Modules) (K : CochainComplex X.Modulesᵒᵖ ℕ)
  [∀ q, ((InternalHomCechTotal.internalComplex N K).X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N K).ExactAt q)

def CechIso (n : ℕ) (D : AddCommGrpCat.{u}) :=
  (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).obj
    ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π ((InternalHomCechTotal.internalComplex N K).homology c) U).homology n) ≅ D

def iso (n : ℕ) {D : AddCommGrpCat.{u}} (e : InternalHomCechTotal.TotalIso π U N K (n + c) D) :
    CechIso π U N K c n D :=
  (InternalHomCechConcentration.totalHomologyIso π U hU N K c hK n).symm ≪≫ e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConcentratedSerre.Comparison
