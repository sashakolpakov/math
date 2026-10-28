import OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ConcentratedCohomology
import Mathlib.Algebra.Category.Grp.Limits

/-! # Internal Hom Cech Concentration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechConcentration

noncomputable section

/-! The surviving cohomology sheaf of a pure internal Hom complex
computes the shifted ordinary Hom cohomology through the actual Čech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechTotal

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (N : X.Modules) (K : CochainComplex X.Modulesᵒᵖ ℕ)
  [∀ q, ((InternalHomCechTotal.internalComplex N K).X q).IsQuasicoherent]
  (c : ℕ) (hK : ∀ q, q ≠ c → (InternalHomCechTotal.internalComplex N K).ExactAt q)

def totalHomologyIso (n : ℕ) :
    (InternalHomCechTotal.additiveTotal π U N K).homology (n + c) ≅
      (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).obj
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π
          ((InternalHomCechTotal.internalComplex N K).homology c) U).homology n) :=
  ((InternalHomCechTotal.total π U N K).sc (n + c)).mapHomologyIso
    (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat) ≪≫
      (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).mapIso
        (Cech.ConcentratedCohomology.iso π U hU (InternalHomCechTotal.internalComplex N K) c hK n)

def homologyIso (hcover : iSup U = ⊤) (hterms : InternalHomCechTotal.TermsAcyclic π U N K) (n : ℕ) :
    (InternalHomCechTotal.homComplex N K).homology (n + c) ≅
      (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat).obj
        ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π
          ((InternalHomCechTotal.internalComplex N K).homology c) U).homology n) :=
  InternalHomCechTotal.homologyIso π U N K hcover hterms (n + c) ≪≫
    totalHomologyIso π U hU N K c hK n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.InternalHomCechConcentration
