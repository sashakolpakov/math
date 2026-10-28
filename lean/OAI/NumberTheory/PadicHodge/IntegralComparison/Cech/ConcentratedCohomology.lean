import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CohomologyConcentration
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CechSingle

/-! # Concentrated Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentratedCohomology

noncomputable section

/-! Concentration in degree c identifies native total cohomology in
degree n+c with ordinary Čech cohomology in degree n of the actual
cohomology sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → K.ExactAt q)

def iso (n : ℕ) :
    ((OrderedCech.Total.Comparison.bicomplex π U K).total (.up ℕ)).homology (n + c) ≅
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (K.homology c) U).homology n :=
  CohomologyConcentration.homologyIso π U hU K c hK (n + c) ≪≫
    OrderedCech.CechSingle.homologyIso π U (K.homology c) c n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentratedCohomology
